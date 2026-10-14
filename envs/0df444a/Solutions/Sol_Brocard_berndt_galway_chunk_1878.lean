-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1878
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:00:25.44362+00:00
-- url     : https://prove2.me/submissions/5baadc03-b1ba-48e5-bd74-ee947d4afd1b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 337589928 ≤ n < 337769784 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 337591178 1250 337589928 337589953
    0x90218040609110109082a06030f10141003090213060b120a11070b0709030b040c03020f0307030528080c030714010902030a021309060e0606010f02070e010303141605 73
    0x40c0045030f000740381030095240b41004201d00c0071409101c40b0003c0c85181c0307840110311020314808031017104035680c802c402006109000c00c00000241c40340020143c4002c2c2c040e1907154100d031501030b11080326840304004503903041051080d042440301510141001b2082060a001c000541d000b0740c2241401c0c00c0049001c2003400d1070580d07090b0704940000c00400c0f0040c1c81508040e15031003141c0000d00500003d03400714102500c606146001150060906a245e0400d494181071850b0f241c03009a03c101e0200120746074510300491500102c0e035108000300020040c2442000c409149d180b02c001d01d00101d002040b01080c0d600008140529400c00a903642d00041d02d4901a2001d0006d034900750380e8503010700800180c030000307490400c458040b5600e002400303c6540d000040c0028150062a04d420b2000e084001c103c000b81c10340c040d1800b6204d0f01500319000341c00700d03a20b440750300c241105013481754010800b0074025650040b08418920700c451070007401141181072400c0c0d800301250250700204c1199003 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 337592428 1250 337591178 337591193
    0xf010e030a0e0105161e08120a051510030e01090501090501060f1a030106081003020d120809030f0403080903070e010602060115050c0615060c1f06080a0213090218040609 75
    0x14102c09082c01d500f0030f0340589507000903030b0944000a0100d442c2c010380d5094a0361048a00502950200c0d600d50340d507041600040c0c4172030041d1440a01242408085a244a03074000481b1030300c2005403000d142c059079001c08401030600541409c42703c0d5039401090f0049002070041985a600a400104495291616034600322149600842190340035250b004840d045280440c2d04455692070030031229110640300209042070756000035407003020502e805003080301d4071600707001c40c078825140c0440c996a0042c04507246e11507202c0300c41c01000100410701c001800310010300340b04ca0000d003c59030310030307160172100505040a07040340b00903a104000400c1000038040781204003401910f0501c0c1880354a621041d60780c1400303091603000100d40317074120071541c441c0301c1a00c42c2d6942190890346101982880701810b0a5061241031545041900c003081c071410019040165540c003910404a400c401c608140041651038402c0780e21505c0703074607a000001610240303180a43c1c0203410016072407a041c50580f4 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 337593678 1250 337592428 337592447
    0xf060519053718060e13050f09010b0406121502040305011e1a090f0603120a0e1e010c0219030203030a2c090703021b0102031509010905060f040b030f010e030a 70
    0x8200003c01240300d1a4161894010041350318900381003554956040000d5444a11100c0c022840c925203010005c101e003907803980034010f81540300200205494441400207503402401940100c03202100307814002100d01011010f003594510300181800d860b80c0e55242921860b00c2d00600c0d04010708184020502c2610894480140084e104180c003042000820400c0400803c000c031781c0010340c07002881d251001d00c405100f0346043d41d441965600350000203058100c050608a000324102e0f81c4195140f0f00201140381d28100503180c0c15484803480d07082192110790a003400c842e0806840000005840c100040c10011a01d522180c40c140f010290740250b500b89040e0502c02840e0421a40301181c566200c43d50b00154949070169a880c901515221412042514840550b10003c10411403a0b00b54000f50380d509801c943c2244142d990b5142c2c80180c90703082e1801035014114080401007440d00303900c031200208000d425502d510721548049821159903074002d80f00e54000107407020040c0e5103e1141c2 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 337594928 1250 337593678 337593787
    0x512130b03040f0201031109040c020f07080a11040203040516080d080a05100302190314030301051503010602121305030a20060c06150312031801060f06051905 70
    0x540c1945003d0301c0b400707440d0169000c042d050682d80c860b02c0500c041500708890100b00301400610450441003c000e44e00d10100760511b15038000c042001c1502100862100902500801d81e00080c84e50101000b00a41c805802140c06100703a200d0a10703010b01c0d410b00107005001d0b601c098501e441200c034002d42281001420328401e03502e070034108511400341c03420190941e501510220100030013020304200c100b049030802b400d9406a02c40308150344400000443c140d88040d01c0c035000e14000302d0030b03850f83d6000a010350b5000d60400b014030044824948080c001da000411006a135185d036940101c4c1c01e014181c20141c0300c6d03203c881040780030720846400407a00c0c403034180d604034034010000100c01d860742ca0203021804181400106032500d0391b410042a9101c10610201d10358a0030301034861030144411754500c500950801500040106a144038481144c0080d1075240c0344c0b108841d00d030040300e0061007050040c043c062020b100c2c810306c4500c0c0450707005540300700001c0c482e078945850700e010308200610 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 337596178 1250 337594928 337594949
    0x10603021c0515030304080102032d0c070302070914090f060c04091503050d0c030906030902060a0c05010f0c020a020307050a0609030b0703020c1009060506180115050403051213 78
    0x2030001c151611840c00c1c0740072590441c005202d44038200d4046515420160b929813503c40400c02150081040d80118014101c0c503001030414902d40302c90161050b2800348a100c080104000240108070303c10040800e5882441690078250300c50b031101d02203600c50051041d100001c801045030000007001420540c0100c50003c081c1c601d800d0002482501c21406551000c41d1a5410714074125a0301c855200a90390000654008000b0307001d00078044000842c064000440d64030000540354001d1050031308158015002c075151001503582a44e2000084c54121540d40d0303110200a2207000d42c5c4261100d070901607002c1c0c10080210f00415191010319000248150318041c0b041162640085c415811a0b50202208840b07903100c200a40c020b004080a5a0480c0503c10006c0d410b200250f0008000d144282810002a201e040070303c0030484c035000c050420344c0c00c800018801e0801c0c00054282004c03031440c1461425440342c0d2440e0030406d04414490011401007070b103562501c0b0486c40321002d849420007 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 337597428 1250 337596178 337596187
    0x30e010c05030a140f04030506040201172208090a0602060108120306030c040c050715061d060924030a05011a030a03051603031103090d031b050d1508060106050306010801060302 78
    0x1922602ea110301d1001605003c140c007586072515489105035a111078401c0203840e00d03241d0324106070351a03a00450701280003d5030700c0580d102008042210324014540c42d080f92032122103610301003034040800c0b24241da1042050104100300c1d030383c1064000c0507100984c060300c80d9502d1704520500c1c001c1c84034400b0320480c0d002c1c07003080129240001ea0f40e041c540c0803600070580003034440003038895202d0184003803c40043c6000c0c0f107421a415800150840b40d14500d10740c604005a0030b044448801610840c1d13000d04070001203120300d4a1000c50301480184d09003104240f451180002e40f0700b90340c401c070845143e5141c0340d81c01c405d03061030404582d401500b54050b241e42203680d50001d0171846043d440c00240414002c240003030510075403100032410320920b41c040c0e42e0708000c40d10136038843c085d1064600213030901c80c00421000c60541c108404005545807a401d0070411004200076081e8038000c8044d00c09111030008400c0410407145000307280c035485641d9241810800141f20100507000718041c0340c01080b = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 337598678 1250 337597428 337597433
    0x20102010c0e180606041503020a17070f0c060609060801090b06010207050d030807031506120e1908030901020f160303050c0f030a0506121b040b12060609130602030a09030e010c 78
    0x1100800301c4503d03912055080d6a0355000201d0a02440e004451100340c03c000c1000510b8140d4000c041c460115246c68507900c204034400224110101c1c0d000002a01e81c0404070b0019000d80054181e081c8180d001180d0561104c040a00311400d0b50b128030040d80d11080240700384000440c074941c001d4070a00c0030b4283c45003080040b410b0345e00800c1c401000c0215010009040384d1099100c074000c00f03050550b019a107540d4000040c10341000c91064086180b4106120f440d4880014641e0740b000704000410340800c8542e100d05c5442e800080030b01920703540030000d0f5400381e40c2c4600102403411a00c0030844c52604203080040485000900300c5680210402c082c008040c05101600c3e4012a440c00200751541c0b031102107807001000d142000854414501040c800000810f10860300007800d407006c00216002d03204201407203c5060700e03e030103608a03e012407a5804c0c8103c403254007413540c24000b00220740c5a600e220499008880203070407541d0754805a0201a44050796142d000001d2070002d2610001d41c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 337599928 1250 337598678 337598689
    0x15090207120c03090503010501030b06030d0207050f0d03170408041503060e04021c0b0c0414030a020a09050603190812090307020f09070c02090103060606030506011b060203040c051903020102010c0e 87
    0x1c011a4140300741c00955108051188400380e0140c00003a0080c03004c0c1d6942e103041a0ba40000303030341d191712034041c0f441894020b03480002d40d503003164001031642051307600540a011300c480c0103640c250204042d60b010f0384403040070f9051003805907100e010038541e203a1404021140e000300072242c180402d428000c08010001c0b03041481904960101d800000001d60980452030785005a01e00510460022080003000d02c5000090800c86058441411503006107108040d1a1101c8520007940000642c80034007218245070720142e4845d40103400c544241c49074072840007022102103411a000e0f60005031600d800081300545c180c0000d582030045050072500d030300040043c802d80c070315280038a992900140c06103101c0c80050024a402500000795961681041000381025025081c0030030305010120b041544240c5d402403241c1c8021181c0c200c0d82c0e90f19600d91000e90300c00b030400e41c0c1c81e5044210103e1150b03110481507010740c41050641000629610002e030943e81e0a40d488001d01c482020440c0c9aa148c0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 337601178 1250 337599928 337599953
    0x19051513080f27010207050f030a08030c0f04140307140612070504051002010b1e030303160e040212070206010e0912092e17150d030309050f0115090207 67
    0x1107800e500c5035403002e8003000c207020b54040d102c80ea8070207003420025400c40903540280c1d62400e900b07503285c0c151580300303110940400c60000c0d600342d8002e401800101d0300303050245030000c103680041403820480e541c04c0c00c015003164111681c0e01d0f41300c1c0d40300e034070500d8104580c80080060f02c3c10aa1402c1140c1d00248460140f013018041181070800000c100c10301c42c4080358041c22000f0015048940c0440009008003003558042e4090601980e0507004001584100041000010000e500d503a40b20620449d90600e105142d100744141100d40a40701e030b4031400902a640701400312848103103041ca100a282c4201070340610088170b4030805002e010200072511202a244032181c242d43c2e0f114180105103e6201e04581810901c04400c00101301c064611701c508110b140b985d0340001d26542001c10f064240019181000b0500d58843d615002c1c1c03e0148043c91880d0280c100015080f43c141c0743d450912141445481043c1d54030581c1c0d60143c4005c669030000f50002160860030002155640c1154800 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 337602428 1250 337601178 337601183
    0xc1c060e070e04150f1406090d02060c010605030307060f051302030c011110060305070e0108030a0815130f060825060806151227061b070519051513 65
    0x42c900b5102450b165500490f000ca039058241003101c940d61440005410701368001e0500a0103888001d03074040c0b070000140c2c0d542030001803030244540156820400b941d0b01281c0d2020701da54a64100280d03941e018805003038418003844011800c3c603111044c1000300c5100034401d10443d2207a601900268800040034072005000703003010183c01050360f24403464500480d88403e4101d050841c00300401c0408605141115401009100d0698035000d00071340320b020300000070f000141180c0000340100c80c3d91403d0910400080c10030b00e041ea600c40081015a8444c10383c1031112602c03004208018401000b4000480440100c08401e0304140c43c12070350b0700c0343c49119240401403203101091140d87c651a580e882c1a00c0089035030341e1205010b90007403402004440b081c100704199403d1440b40c0c400d04034410303401c0da1040c0c00391803590b840310075800d06952020030484503102c003030000c4030011b20104045c00303044442000e2640401a6171038900d2524143c150301e011041c41d280240007404042030885a1410f6 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 337603678 1250 337602428 337602437
    0x6070e042d02040803070f050708060705220b2101080a20031e06060a09020c0307030c061d0a0507062d1e08070e1f03020f0706050c1c060e07 62
    0x441d404052000303801950031010341170000041c2d1900b00409448070640851141050364140f40e039549401e500c0714812180400410420030285c401d41009000c000528071f0301e6201d10032810303141d910488250b000710550100b0000da0058000700640b840c0081c600408529009142e24655555840ca8000400780b0014605054070300d02e1859a405001140d800b072010b01c03807000c00c2d80c84555402e680700b1b816074805000d50754400002c9000c0c021802246c150416120065252111603681210121816032040d28000c2e0764103007654902e10703100448514083d036000100078129103030400c207007000e8240c0d1000c818004c40441c3d8516111205001c0c9084c1200c1040409504c0384500c0c050314008008201003d170320b81310540302d045481d00310883c28080d40341903075802051104c1c8014403c45003200011111540d48024281800c184250010003500110082d41410054566121026142c003502d001c44040d0011609000c0310900307020803994000411700600c00d0500e0002e00101c80b40004e0000420072 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 337604928 1250 337603678 337603751
    0xc0606031c03270f03030e06070512040c2303010e03161704080303040c06020c010309080412030c050102030708040b0a0c08010302090702010905060108210408030f25030206070e04 79
    0xa809030711100c0181020b114021241d000035103012000103004e02c2040b008640391040030225444d000030040e01c14120742d1109403400d42c4002c0c508001d880d000340121100f1841d804003084a51486107035444ad03184051029181c030798400205070944000841c0310340241d005203c00840c642c058150903c80c075420080c0d1000050042c04901a5803155810844807440004103200030040d016a050044408a9007500d2003640804011000c0d11080700c40a80200c0f414441449005d9502d4203039030003203102e401c2900b1a180e0a81d0f8003803d9810481d150804a40c0c000100814802c20741410703075004400b41e40c1003120090140d809030110b0300601000c1c1c081c4140000003031026000f5448298910b0304203046030384669440c0242c40e038500940600d00102c5000b0352000d0302c822180d50558003a0f07409100554100f0312101005441a0048041c0c0c0c00a200e08800c00344800c030039180201840e034080d87c040d00592034801805020040d1005055000320b1030098001022045000c40c0081507038511400c2102c0c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 337606178 1250 337604928 337604951
    0x30f0c210a0506190c020c031506030102040f0e0106020c0d0b190921021002042402070e1905130210110f0d121a010503040f0c09110c0606031c03 64
    0x341444018001c0c910b20844090006003010407100450000613520706029031201000103e031920300340401146c250380a84224036603000b10442c1c0660003400034000506043c0e5402c4141241c0820b0350140714100f0126005011982e4140855074147d0010344051008401c2c4d40c1d81c1924540004042d40c0e22500341001058413502503401c90364919130840056031890b800c10101040110054421030058031480603100044c16080c0203440440d075440740c03010700e0040240340d910403030744034000e1090443c000d01c0800f203890003101e42624011042c141041c4004100511031000722900681885144030381d12004400590b5502c0420350034800e10300d840b0702c100e030b111920980382c5180018541c0141c065003011142c640d50200d0712112079074900400303101d050400c0344103015480c0300c45141400210104000390103d125030264400c6248280010b0044940d20349980040f100c90107002500f034200000c940b00b40200410043e500310f501100074041c03155103a654484d551032010360b094241070726419045103 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 337607428 1250 337606178 337606183
    0x3140d09020901080c0907031107021c08040605180402070b0c1602100e040f140403050a0908120a0f020706021b0a0905090d12060f171e010209030f0c21 67
    0x2403855002e04003000c1540c50b00501078580001100907800742c0545400100c02c10f20a00641e80c0d203107099801e151601420390240b1940d40900c00702d40000080300b4410000203080000100000e00719a0344003030b00c80d40d515100d00110b60824104901c0307035005000300008180f034290b21035044180902d50f15074940b2651b4502034800b402210295000b0740c58002a21100e400c00c94400005600f11000c0047c0340c032001c5071004554040140000e581215000a400240904001c3c0701d0f030140750400210f01d43d80c1d075032110310f4400c2c1501c860700a54000304551041c4c6c0e030030070051000385078140090254141800300c000e5840501c103440c20710010b1070040c0c0c038005071110310140c1c0107004030070410b00442c5803403880300e030b69590903490070000034195803101d46048856110307000584015101c5210000d1403c0f10003104603440b0b8212001e14020300c05600c140d03482d842e060000d040562070000d40c513005d0202c109410213584184000c9241c110716552802e80d036840c1c07050304100c0c189041d1184840002c0e5100c92 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 337608678 1250 337607428 337607441
    0x703020a110106031101030b040207080304030f02250501170f06040f061a07170403050307061e05040c060906090503100905010605030703080903060a0c120507030b030a060203010e07080403140d 85
    0x42880d4a0800040103102c0d22000030f0303030354004c00c0c0c03003d00941648d403060004921031100c0280c4907820030f001103800a8405c140c46d448588041c4112140c258a07080d11075509200b0300d0344400d400000351000c003c256000180a00c07100010382c1c0c02c1106207460a110b80c0349002c010501d038072440d035920035005443c501d40c0c0044080c0100a00c50203281ca540344403000b090344040c1003560499003507001d0a070071403900c100301e82c01c4d03070350041c00345040924690b1010060007112000c01d01e007241d4214070101b242c0040c42501d200d10b01560380d0741d20103440c06070040c1804115403c040d00300f0007200d20501c21610005414421041c101c00002aa031046090481c0102865004661315000302d400000503c410705019142e526000c40544000ba255527400b10200c440120a0302d02045041c5000b9900e48865444164465003e0401040441490740000e05040c201981150070f2640880180300707180b00075003095800b50326410b241c00c940c01c1035140a44ac40415102c8074a00000014940c4032640040d00510f = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 337609928 1250 337608678 337608707
    0x3070212031603030e06090309101d10021b010f02250806090a0c0e10050d0203101b02010501050a030c1707090c1d01082802071505010503060108150703020a 69
    0x210040000b514005014150300e002003103043c0b08143c01301c1ca6032240881140c2c80c0705801404844012421711042e540342140740c1e120b4140d0440311208122907190035501c91400e04280c0c1c050211303000c0d01d142d61100a0303031380b0340064100100800310307681080e00080c09c2d00d010b6400503c8112000c0c88000321114101080d003106c0c0c4940202030510480b40400144e08401a02c60540038205903122549445601421a440e0201600000013045641080780c50046503600180646440304401c1210390f0075100c03004880140300606500d25255a6420b125560142c10111f0f010803540780b440d11030742000340240c00f421200d500b0415401079020f20800101c1c0c000c1140402c2405023601d11a8080c00b4031400311001c110040741146203c18540c4600120391080c44454110508000c55101500c01e8101c1440c845101617820410280484c030502d24045884100e5800402c00d98104400d2600380a0184c0c060318082d409400030240c1c803e00e10360703007550042d01d40c600143c40c1ea110316011a40c07038204210344e = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 337611178 1250 337609928 337609957
    0xb060f0a020616030c050301231005031b070f02090612010c05070218060114180a0f03050c12030f130b0313120905030c1309080d06061b03020307021203 67
    0x1260301103402080141c0724003403ca9100300564400041030381a1001400c00d400003800800050102403a61a411a0b4152520340406801d40f41a400715441e0009010b00350046800842049201c0c003407442102c00c091490418a4100bc60540e907030700214807502e030001d01c03d21951000410645400384c100a44002d42c00c0240401c440340c01e4080d0103988015801c1e80034103588259108510144c03031101c0d02900341a0350b40142550704900c60b02d9290070030005000307011030b0300d0100096582c599a48074040d0141c0d00e0700382c0581c0d25524169140003101c60056009003580003809460200200a48221a0801d121b03daa9040301020300d070403800040e04040c40c1c01d600441440414484401240d8207248250301c415941c2c0310490042d6030181d010710034564940d118424000050410407000c00d9803000e1200041445181c9a851f10f0841c0c10021941290a0307580c1410042140d02c01a44031a80f54800c0000e54101c0302a18000d46034481c10078040d0040f400c40515141c201c4003003003214400d12a0049 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 337612428 1250 337611178 337611187
    0xc080a0e0604031a0a0207021f1412060a0602010c0219020f0406171b0f130f0504030c030e0a0e0f180607020109050601080c0307030314070f06020706051f06030b060f 73
    0x1410401001203803031101c907004104d03000031a020b04038801c0300d80b202d40081800450900001d0982000c1d07000031400c2d800c01108a10004042c1d88113006001c60040e50072100241c1d2400c6c1050000440c1e0a921200842e07042460028505401140200109807028101c1600c01c20a00120b1007550740c00c40d013580c10a10700080083c849222202801e415055441515494550181c0d0620a1180c1c25100c640c8280c1744900310102d80b51a0b400c2900041c4a0900450038010144461089601c119030517404680000e807400300701035006440246d019021184c151145081001130240300100402003a01c03481504082050368800680503c20702c0f40c402c0885100749070174440280a4150030340c00b03d030203108440c000b0a00b04d2001c540e0801c80500900100015441d540303080724141c2403140c0409820104001940100e418a042da444c50307070083e4000344c0d441045207482d8003141c4004028904800301004c10710144207040a401044461620f130120b0303400c506200245e02441500085010341d4000203 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 337613678 1250 337612428 337612433
    0x30b061c080d051e3102120601030c091a0112020d060f051801052b1515050105070201020a02040e0c090a050702010e1207120509060a0201060e0112030c080a0e060403 73
    0x70050380c0300b08404110a00044d5010003400c41801065611040185510651082c003404004138181840c801c44880213010003981c011820104038442e0421881d0032260041c030a2240800c407441c02058081c030200084206101202c400402c40941d0300d04210354000310801403145a0103030390343c00c0c1e0040010007080e40c0c3c0e050400c04051540c0300b4240a6002d149016904000003043d03241200d0000d40b003107681e4002058041480c4c40004a103100008010b82510003240c9058580701c1003155030b1000003220101c142e0510300c0507007282d001d41d04100301000700900503603004c1352166503c0da0585001c200c064200c0441810854840c001c1504141100c00b000150343c921380140d404de0703d15800800546401e07800f080c3e00d884680034a0100d22000300520b0700003c500001101104201e45401402c041504000850550024503c140145e468a1301482020062809540108107034009410194990358000e0921340e101c0001900d00c1c50049040b01d941d50080189103c1440001c0605542c2c03038603803 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 337614928 1250 337613678 337613681
    0xe0108090c060f07120c061a0d14010e03041e0e04050d0804060f18121724120c030d05030610120222082404110102010902030106080a0b0f01030b061c080d 68
    0x746e80c00d0329401d0a28003c5489031440000c4c1c500003660242900408440c5600c4c2e030a100307510a050070a9542d40c502d1288848030003070000d400646107120100a94580702005001c0c8110b142d000013003481c0030b03072081c40001a400150210810070609002c9486d6507541003800051001445806c01c2c0c07820100a0702042e0044218000054440d04921901c0c101201c0d0440d800036107443e140746071455200100d40258020001a2003a00002c0054480e18424001040e02802d1408400c005540008911540d41c901803201c014005c0443c604541185020000150b0190030040c15000348000c024640c03c08280d6601114120006042e11004070f28103941c5542c002c400750700c03c0c05038900424101c055001c0fa00807004203050604500140e241c0c513140c41c5d0208035105944d003681035641e110641c2d001618203000c2c000c01045c1c00c1c4050414440d450034540300701d0b01c0040045504c0c80d600001840043c80c1565420380141c426a10381e4cc4025026003118141210251301504120001c00e6941e81c49115 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 337616178 1250 337614928 337614947
    0xe0907020a02040e07050d0f2405041e0b060613050a031b060c111509040608030301060e06070b1f090501030507050f0d030804020f0612040c060e0108090c060f0712 72
    0x381c504010000c607080e02517844002ca8094250b12041c1c1e90010300100704030700244510203000ba003460341000355070b00c403e040085a41041c1c0700029198010001407081400010f0340d201a040d1411410740b0b102d544014541000511292250030080f0f1403420500070b004143d400341c03138042e00b03086000ba12810f00a0b1002c0510003031a44d4002140c6000c90b0191091020280440c1d20030b800005002c101c4003004016003800a420051103c14464102d20742e0f0345000380802042e649020b0b5580c3d50400500412240e11010f641d40201c5080044200054052299507803200b105c0e00001d4810b14601100403a1030f040d2b600c02ca54013814140040700340000030030890102c0b102100c800001c003469900340854048901c40240100d074401002034094100300b0490143c0f5000240618034108008a05560000007501c054130302d6405104140101500308905004a80090070705203000d103450034146a46548003210380780504000320b40c1c3c001e4005100150349111740d200005810403645a00001d0940c0315 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 337617428 1250 337616178 337616183
    0xf030f0a0c03020c10021e16020a060903030906051e191806091703090310050a0b0d02090a050604020c01090609020405100812090105070803040303090201120c1d1306120b09060c090108070e0907020a 87
    0x10234800144141c00cd21800d81101e0380f58030381000c80392411100340d52941000c0c052002070a92101d00118681485000702620904081c81c6800141d0120004020417107107404a814480c3e1020244240303604410440c04981001500d1108007034900012400e50040880a9426215030105580380807142d0f080385205030810346c1c0c1003081c00d01c800b08108840c42041806034001503030402041074081c1541001e580b0040160000d4509648011694212100c128094946079605c3c0750100c1103140c50300509803c0110b2542c3e00d00740f03608000e0b0440c1c941d007401240c04840500090482c482d079004100f0740e01d05c550804142612842d00c5d04010340944021030040b800201c1008403100a44041d226496903c000c65071400c0d01e42c1c107c01d010748d503a40c1c0c09000e00c96212062451b80c0c0441801401508041c01c0400d43c1c0182100592030a04000c80016050700c8054100c90300f000001c050038015100c10b0720003483c210142d0b4a40b180d0a803808900344021b540c00c6042ca0741004565600050107041c50362 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 337618678 1250 337617428 337617439
    0x60611060a050c0d02070201020c060a020f010506090c09121f06080f0a03020c12070512011b09030b130204021204030816020304080c0904080f030f0a0c03020c10021e1602 75
    0x10740e2030900008840c011242c00142002c1880b030010048020350280103c2ca106004652209400c030000800700d03005241301400680c400e8400e11403d00d820b0003695000141036070802c00c50700b0800c000f80964083c140009010b603841d2a0a00c002c502c0c10041c0740c111219103400c00a040109085000c041c000e103009420b55840f4100500711819070000d0b03800070454055002e0192190301c036080240c000003241200340d080c458050041140e03550074034100161507040c800001c0c0400b981030860700c816600c0c05843c00b40403442d8420000300345e80c08000c0d2340c00b0011020105000990b840018000d00440f2a40b504041b20981040109904141554003400300c10302c03c542e440b10032180482c0c5e82d220300d0080740c00c160002e048024050410241c0b66410510644840d410008030201d003000076081191031418a150742000c1c00721001d050721411540140600e0103600d81084101c020756602e00c012502c3d4081503001850106410b05003036020040d0034048030399035a5010300d0345410301c2c000445800707a2165 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 337619928 1250 337618678 337618681
    0x27150f0506070c05041d2a011b0303020901030f231014040f09050f150f010806180309030712140303060306040b04050106030f050307060c03020f1804020403050106061106 75
    0x1e2401500741c03078656500401c1c00301c2c401d040c8002d003c050a808001d03100e41e02c2280010403080941032100d84821110040041d20440b0016020385102c213510701894103008101c52408254200385e486107850503014207025944014840040b0000c10700782484526a500c0e102614403035502202080c001c04550015000480d200c20068904204041c4250513004040c1080c01525040a401c9200b01c0d4145d0100051484015200e00381000d1b841c14141401d03030840749a1002d41040400701c2900f04c415001d90031469814414003a41c1d4000241242d9640d01c0010811048000200229004070310050151000780755202401210304c090a00102e4096503204c0b82e240d000140002a43d21800d001402456191100e8071520900a4080c1044d28155290440880400d0090011581f0244a0002103641f010310b400c00400301c4010859030000c240c0100903410540795071405561a50902108003c2c1840c55040090028030403a840244079500709030001910b260420340c03194000c242041515440d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 337621178 1250 337619928 337619939
    0x30c070510050c09090606070f051c0f0807180b130e06031c0c1e08030402030c030610051522050a06051e2b050a060e09030427150f 58
    0x341c0da001c541400300c41c40240318080305850980400d50b00110054101c234070340b0768607488201600080d40b10a407081d5000da44528806243c15100b40b0780d8001524002071101d140340f400502d4110040d042404000e00400341009109410045100030301204403019500e005198580214100f6803007561400340e0040001076041c00c02280500f03144503a2404616098210901558800d5020740b0039150032162524081d407000a183c54411f07140d0280c00020749034641441010f20f030100c400d8003640250030050502868655200500090300d100300d41c2400c1c1540707000c400010300e015070300081801b0044404040d040c00c2c2031140325404e0300d006560f070b081e4079134480c0820743d801e1048c0702680c172100840d44045140c0c0000000500f0b1072040d02201a000d640760990070f103105401c3c07004604443ea43d1402031040c00c01c4207114010003000f03942001e03401d916100d01c1080d04c901642c4541004e03010b10101c02c800c0c44014841c0c5004404181c03004100c0c159071043c1843c510b5400c2e0150b80040050383da8003080 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 337622428 1250 337621178 337621181
    0x1060201060f030b01060f02070f03030905101b1103010b06030a0b030d1103030115050f07030207060801120b1906080f03090a090203060306270d0c060b04050402010219030212030c070510 82
    0x1604e41006070001c0f00c0e46400b400b21613448401030100118091450046031f002e5120103498000c50107035880320000ca05040c10072161100c0b66468030140b00c85103041e504400f00001c0d1120032140c101c0490101c48401e5800301c3e0151050f5098980e2144001080040e02d400941c00314562900c180d00301c88800c007920380180c078150660505d81290f5401800104202990450220704030009440d00905102e00b0703444122003500584021030240c2c0015005000c02070f88864101c0c01460b41180c001c0c4000c5450f120f043c140940a041a4820981056a559485802d40140e00140700390011100c030b4206c0d0031000f42d00ca400449a06108a6103035800046141c600d0094034003c1e04010040c0403980c5540800d2003103044540805000484a512201e600305424450402c050145480724011300700145440303004c032980c4a8000e481f40d4904402d010150340d000070a16183e80345001d0200c01c00c4190709090740b6002c42c42001004481d000402c0006004402d00540300c0315104404640f22000303020385810 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 337623678 1250 337622428 337622459
    0x512010906140f15011b060506011d0d03051803060403090608060a061b141204060e0405010b0f2b09032003090409031e03090201020f07050f120c0d0b0106020106 71
    0x140c4181c2d12402041c40790700280e11040244130141040002885085104080410741880580d00700d9540c40820001c0e5030460800c00c4c2c07040c220316010441c80140300028002c4078410300090100440404c0840c002d070a2032200c1c40352820300404903891450701e850000e12546490040034006040100812010300340f121000d003d482064464010031a040d460036503058000c40c60a40d141c4180340c564000c00340041c001c05d0208400c08060740d9035582460406403400d0031182419010b1403800d001005484034150507100e10b2240304e002d941d030f40e101001c1c28a598540001c03941c40c43c45d05003050050780c42c140b079209a001c6482502e40840140208804c0c0c49000c0d01180c00c00d150b60001c000d5000b191620754040c0624038480c2c144070710301e10b140990301c000b145001c142c841c001c65612480001590727010826080c01081060003070641c0390a100115951030301403502a40251210210713203002c158148804084000701511010f915081c174100307041c40080070b200341c0005d5481c0260100341c0301c01920380807 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 337624928 1250 337623678 337623691
    0xd1b0b09131a0d1103070b0c28050601080705040e0105040506040305090a080609031323010e131a09100803160303090b010b0d05010b191404051201090614 68
    0x4070104609054410050840c403007901c01281e140b503852454540e14501c40c2910ba500071002a002d83d02070301c0500d850020280c000f000385240500a11460000024810180ba0050000208503030780c583d4002c0312020b2040e8000700180140b00000c13480c1d0b080024898104c40c0201d07010300c102c24841d11031900f2034070260790140ca80d0304444001408070740a04010590035001a0400f0f401c55510024181082c60a50340000a5080007401000d0144040340500150100550a41c00e401e02c0c20308100b0342f405c2c20078907a4144030100014185a0307a40840c1c41500041c244402d00c2480c424100c046403c1e000110400c0c801c3c14004049814003c18250050076626407030015450203000485008581c000744004404050312500d0031000500203007401802031443c1582a0380b0380c50b039a02d83c1029150140c01031085e064040c000c0c01111a000e00b0404000d00603810550941c16594100c0c0c6420703c01d84e04281c0d00800032001d4a000000d055000b108464044c24040207000200e40c03820403186001e039071740c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 337626178 1250 337624928 337624939
    0x160303050d110405060406080f0a0e06010e0907030605330d030e04060512061015090e04110402190206240907030e0d0c12020d0503150d020d1b0b09 65
    0x75000c41046503220340100800c0d04100e50800d030380c0b50700081c25507001fa00300c2c3c4c000809030303800d001c0580d100041e400d40048603148107004800980400c641e03900414400d519418240c00e0120342c107107400f4403e00d0091500300c3c2043c00740f45400c01e5040f060081c2151503001d00c0005444540c0c00715030624601102c0b040007032502a4030f94840e201211090b44000300c841e4072964880000405a86950001d28801c83d010080d1040b403410305245042100298448080766200c210510765042d4080ea064007a40ca41c10b05c130b0005a207650510142d01c16900110780d41051002844984400c4194176005841040d6030031078166540c2d103a90a090444880c070048600300b806008800140b5080304420ba00800509c1d00003500c8849140c0580341072082254400420340720340e00c00b400d101050584012040c900e00040204000b01e00d0010b1103844028a00d02e030104942e92030604d02d0b50340100a8041c2074004203012004009401d000b0030005000000200140501d50002400c0c40c40c98103680748940b00408 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 337627428 1250 337626178 337626187
    0x102031501020c0415093626041a12040b1006030204081c110607030506040c051c20210f01060c0b0403051b010b0307060216030f080c1e16030305 64
    0x90b41405400c40b0121003861810a0a204105000d500d90700071541c018280c03c0c0d1800e050a040401c07002c081241c111900350840c4c40080c000c440b42354126022110f00031a00c4010000780070790040c140c041c100c252881c0f03180702402d010038408084c949070300800c0e500b41c0541d000c566440c0180c00b03d01c03031441920900d0700804004030312030450003045521000c460a0080011003240140c9040c03040403910040460b5640c8103024040c2014030036100490110709115141244510004040d0030101c0702c240d20242d1140c030003820000d03002c5581c040c032416503000b01e61074403180040300724143c280b01503100900c54040002811010a415031604031190b03030300c868400c0320b03864680c0480e4110041066051003810042c1a403d090040100014030811f01d00004e9000c3c20303401010f00384002981700404651004e480441c00d601c180544000f10b80e03102c00d00d4000c00c102850541500c1c0942d946a8800b401404110110039441c103105560341556101526060090086060440b48043c000a0001801840b = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 337628678 1250 337627428 337627439
    0x18091a040506123a0206041a07081b0f0f071109070813061806021b010510050d05120f04030b010b070819020703060c11010506040203010e0402010807110102031501020c0415 76
    0x680f503010a02158078084c00c240c0d091240050540d0010504016806201084148201400780000c0900804610042d07818082d000800201002c0d0802540c0986d184a4026043d01c9030b040394040123401c40300b0780e100e0010144402172500f20250990b40c60100701c10074029450b01802c800d121f0740054442800c10b813610f00801c0e101c24411039040304c40e81c1d51481d16a85020400d40078034401d500c500c01c0545d07a40c44040200c5c046100032081c0c2c20b074aa0400080c40007010f8104c40b0003056070f00c02e88200000060a0820034030b401c41410300c10f0711480b00094000031a61840f00140103590203031880007002d981e1081044001e20401c50050090601803014085514a5851600e00c15005104480c1d4894498644408541d01805450701141d8601410b14441c5828043c495204008641c1141107614080c01d501c1e0582004000904000c08000003070159401289000c8034002d00a00031500c9140c08008a506c0341030300540035002d4860a1621043c0b40b41501030f840300491210310040d001031509 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 337629928 1250 337628678 337628713
    0xe0613030c030c050601030c080d111002090307090203040b180c10030203060301091407060e12030d090302070e040c03020f061602120f030d050106090605120718091a04050612 77
    0x1d40040b420070035204624800f0a4040108901030350142100344502c51520b03500c54a02101c0035280800c4c05444000210110030104d081140203907000009640c461242c0e00007030900609030020302840c0c0c80841403000b8091407064292141c0505404000c0035044a0001950f82c1a0140e03110b41c803805840e80d12100d640309030051601700c1400350012800d072040d40d8036041e242c034541102406545c8540070410402d580f0800c51800d194003602c40b114800f04804480741c81e80310784030303c48464a46810618003014401c0291300000c06164450b5803142c1014a030000c009089480281e116000341d4008608518003c02100c04181c3c510810200c5412140c0c20f04c8480101e00c2d0312780c841401030500743c62014030240000c000308449038100190940c100305025210701d14070380080042040500c0f8044060038004080d030f400c11110700b41060301051540c203040b603030800c0f60000c008160911034808000c2c074070071510300007080c003c84090119a841e8020f11007111425000710b01130707a01c05285401c0d0007092 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 337631178 1250 337629928 337629947
    0x51009030f020303090c01122913060501090b0a140316120506090a1505060d0203420a0b0d0c0e091005060304050a0606060c05062508091c120e061303 66
    0x42580103d2010121038410f81c107514103c0c210781c551664540449c60300e180000d40f45400b10302120040004c10b0904000804044403400b651003c514000b40c00c0c0001402401d043c441103031021201556880d00114a08001c00c0b407801234408103041000d84a4109600d01600c3d12410340504040140d43d92038040401501030300040080602c0c081c10702081036110075004082b0b20300c109402598a06106200281403007559610046010182203001402c4070070f03011841c000048042d030102803020b60000905604c00c01e90102c9200c0000089d42c0822220350740001100d881541c4405510036451010301c09410011205c05030fa802c21840f051080d45802c4002d10b40181c0910304840185903541d56040450b80a40c100c1000700341110050b1041180030004140c4c010500007103130800c1c1d25005d5030340002e0310840840605106800c4c0008030001c90402003002a0a00f190320a01c007407264010160001507400020444c3e9070030803141c5420081d0005545001e0340f102429140380910f90346007196103011 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 337632428 1250 337631178 337631207
    0x1050108011802011d0a090e061e0f0406060f1220030c190905040b0105091506090d0203210924030105010e0a03050607030203010608070206090a020f040207051009030f020303090c01 80
    0x140341e50120454a07038403c0034024141031f0000094848460100d149407580040c000c198040b040203546076403143e040d64203a04402e203107026180076119443c00c10050046600080701c1c185031401d0003c0e032010110304040d002c40c01600c018004400c035650075041d01a000e410b240c0c040d0720150b10f046040c1400c0048034220f4a507424209101c60311417103020240d0314160b405540d01520b44006000602d00034a1864000ca4010718681701c1480b10004240d548c010440424800e120a4040405644050000c03071607280c3c03200412000021010366999554010300c0c3e0f01401a002c20321001a18035030300400c000700354803d171000c0d0f080d03038a050011074501c0601c003130054112020003000400618100201c2e4050043c60300d0268696052820007000400d0050a80c82154058410300c005c0312030104d240d00b00349405541d401c070210319010106001c1d205030700d4001c10502c140e980100c407202e450390000c0400362080e9100f00480d81003a000b02d82e6800150b0780d18146422140055400758003407900b603508100c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 337633678 1250 337632428 337632467
    0x414061e070e04090c050301060b030f0402040b011101050a05090111070206071401091b150e06030a050702160305070f09091e05070b040e0613020a05072d0804080105010801180201 79
    0x548580104082d2000302004641701c010b2880700307004a06d020f001c0c000c0501213030481c2509600c0c1000c0042c0d80350001030300190143c2d070307034290030352440e4460700400310481060b038002d206508290803000010542198101034952070000d01d03032855074964040303443c0b041e0024102d60526a007030302c0b050412a006540e4081540da9601c0d2000011449da81000e00080224600b51003246804881c4240c800300442c10030800420f07d0780c5100954605041c0ca4010944080003d11030f07541c81030507890714080704c0d800006a0180480002007103c0003c0304026200d0228100301c11940d2a21403206861031034000800e1042031403c94042d0711006004140b219028a003151111503039065000240d502c1a0045509001c100007082020305000742074400d4400462811490a500b070305000b07119005604004140708590744039501c412041b03c104103d0000c00c00220f0110000c2480c0088981d0f01600c10f80065508003000043c2024040c80ba20051398042c400c800c05c10380d074980c011241134442d440f2414442 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 337634928 1250 337633678 337633697
    0x8031213050f0a0302060705030c070615030b09010605040b0907051b070308040603060e06030f06060d1a0106080117010504020a060806040e0f0d0201180233120414061e07 75
    0x1e0010491240380d81810340140c000316a490400900b420b40003080c0c0c5013844401c03c2030015200e60901181c0e00141c020b040010076155507a4540b06490b9540c1c00a40395948900c14880214010341c00031048400072182008001e81e040180000003100301c4000011800c2440340504001500c801341006001c400d007034801c1952281d940540300e8025030000030010307030b0340c04040c4501c2440c034a00c160492421402804124070a9080da0741d103030320050a4038004c626144c0c0c00b40c10007044c1c500185a03250110400809980c4079003004000d02c20901c1100040d002c48002c4030001103061050501850b00544400c00b41c6092000c1654055405030820740c215540302072140c0401c4080c84061070300c81101c005061202c240c00c40003425600b071601c030b00341d0301c0c10441e050500607921503559013100e0322002d01d4812020120080b104170902c2001d00c2d403405041c0021f003200d1242152000a00c100d1052000580c058460007030603540b510304546601c4050305888841840c00d4940c00381d29417000d02480c1c4040075 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 337636178 1250 337634928 337634933
    0x15070804170304232b0c030b10050109180b0d050d0e03070503030f04120606051207030b0a0c02060a050603030c070b1b0d091205010908030f0a0b0a08031213 69
    0x5154074100789600041028004280341d80e0700c08004000c052407148508003d50000341ea0b030440300e40e12180310460548440c07451044400c012840c1078200380d13000425139480c00c0401c1400001c851441407032010020128541d80241d849800343c4000070808041c0b078441140010041005a5813690f20850440a03400003501c100100c81c28404103613a60baa9101e04542403510f080600c1e00050300c640c10520407001611808070646040300c03d1f800c1c007645075000905012008052540096810a15000c0b4039819240001140b10480313218021901c2240c1d10450319100300c410608100005030800300101e0400c3c04036811070340e0006d038010103803803403d41e0900146207009059808140702034030100f6905943c2c00c0c010480d00d081040320000e4068801c0119000300168580d00800314040c0384164075006101c001d600401d842035110202d41d949003480c0d14208500001120013a00250410f8101e40e03140c10b019884104440c403400045040003220742a40c0740c01c501c0101000c440015040d8030303501 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 337637428 1250 337636178 337636199
    0x60102100905010e011a01050d1515050a0e06250c05030d03060503010b030d090b0c03070c0b1b010905120913090602091e03060402010f0e101d010e15070804 69
    0x120544902c000242102c000d41d407007402e41c0c02c07100b0003002c0c91a0602c400040c590f0001c00b01e0700d80d0102103500080383d40c1410307221a201c440e103400680010680c0040000d40a0300400101480700d101d44540100c20348040412800d803080144040b1b40001e83c203101d00c04444036204062211384030b42d0000c0a42522070000c2031070f00100c400c14000203900c0301070400040c00c0c02e20444000110950103442040059000076080b818284901032407506d0004004818000510075213003403035484000302040700d0b5201ca5224198207c4024000c01505807000c0c2058000e0520074182140da001c000380082c6a00c0c400c0601c0740da0028010395401c440444109041200c4c2403103103144c00d910035000161159403000503c00c11403400044040640c1c40c01d010311003245e50000e401d0b684540e0900e0f1034071903046504000c0307502030702030441107810640b0841c0c111041038000d402c7d00941d203203800b0381c1c2600d40c1c0c40e41d0046504122141c5180e80201519480c2d06c03041c0c014000500c403440c05001d084e803030950740741512070 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 337638678 1250 337637428 337637441
    0x304050d032033160809120a0903030e04020c1b010201020f0d1a090714030a1b110609030f0403080708040510030501030b06010903051b010207150309110603011d06010210 75
    0x240503c15102c40800c107580d04525501c0c40c900b0314494110600d41341200030a210f05240343e01d41803190044c00a41c060a04200c0072201c085005030792510740c41d080c400500201190301084010900c0e00070410b0450074a84240c03010622000d009000044215000d0400002d21042141c1195001c00014216002520081070300d40c0c450070300042d4a00020312042d0b0044089491544144100403e0000d0036502c402041c01c4005001200c50f0740b6107560000c00000d05070000c121011081c5003c00e100360f20f0b000030102d5404d483c4c4d241903c0340780d135039000100d40300c1c41160b071100340b1030320280700510200302000058002244103c00040c50f182e00c4800003900d4410280300f0780700280e101c400600402c50341540c401e4100c402030904144013803c6581d02e6440301c08105505a80369004002100030f07a1003001070038000d00e040080708804070001c0000502401ca070903025a074068403000f2280e12420140f045070704903178884824070105601303e040d60b0300d0313544080c2040b1f0441c4610180d10703040424611440 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 337639928 1250 337638678 337638703
    0x4110405061b0106060f090b03060a0f06050d240605070606080331030f1e15020a020f0d050a0f02160f0501120504080904091e050303180304050d0320 66
    0x221442c0c1040500d02d0039640150000e8041100c10300703900611941090541086d90083d0002c141c40e980c1d02e001052000304076501c1207501201f8000f0004e203954100b4024000030407469000d01606400115420f000955210b10940390704110f001042600d100d0720180c8502c40c4680004500c141e6180001031440c3c000003441c9032107190b102a000034644004072100d42d8039060341e0266186600d1a19a10440483c0c5440a00b034121005941d0007540e00100c64a4062580003c1080d0300a4010744807400030b41040d03030bd0902500c12803051403030544000407800c00c0003100341d45040c42c00c81c002d4002c40d404640c4440441c1503206107603c1c00e61303002441505c4000307081d44501d843c440e0703880c01e0001010183c1c800a201d05044c900814440070405c007801302c030640301c0c0944000c284c0c10040e00c1c1500c00b51141202d140500300d40350791514104034001c03004601640d00e1007015401e882c3c20b40034046c0c50744290f1180342d03884030f08401190006405500301d04c0c80c220804c0b900d4400060410b0301c4500b40540074402 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 337641178 1250 337639928 337639957
    0x10e070f0609270207020f0d080904151a0f040f060c06050a0509070308090d050a08120f160c0204110a0201090b01060f090e0a020f040806010305101107020411040506 73
    0x1802400c0d0700800090041c044002c0343c448243c091060060006851404034404640015105045d502e80c200503c0d040200582201451055410291155001113001ca0711075030806003c6068400c00402c1c00c030640e403425032400e201c2e1004184c140442d5125900721141c0180c03e00000402440c5e4407180d900601940d00d84000090042c6821801c903135004119450711413824084c01400840001d0300020b0b240d120b8801d80d520042c803c0000c5c003007502042c00500314424640180100700c1000044d014100407484440f825484244180d03046240c01c4504412039441e00100c461407503c1903903820082c42c0054800103070040f000540d25100d920400250700581c0d1101d81c040e0401440041a41c010403940c038046c2c8408440820040c5500354030711075403039889101000715140c0b42c0b881d4121400140c00c0b1580c503070340c0ca030380c1d018045c2c49283c01d01c4184c402d8003500d20100d00e00007081c02241c44110140789007500e003905950800008050540341e9106104050001045503200c50008141e03400c6142107 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 337642428 1250 337641178 337641209
    0x10314040b060f0604063c09031202010608101a0907081806090d030e07050a03030c060e0d120509070e07030e010b0f0607081803010911010314010f0b070203010e07 72
    0x70f200d51420030705155409000100010440161b101d070400040c0c500e4404c003405504040391001a4014022503a100d4103000749402140071502300c039400045034402ca03072503880c079511604140c4c201c0d000c611030890160024603141d4604c034201ea0141c05d044140c40d108c400b100d404c000200f1246207048400b070022400322014049101c90003002c40b140990031400900c07403440e007501041d4803190103507d0081416141c000d40d440203d81400010003800307001e88881003c7e640d0b400d0003059a2074be28019038480d858040c1c201200386005c106224500c0e407d03202c1e01d065a0034810200000d0000401c000340c14081da004c041140a02800071034043d06240d03a01141d074210380320502c1d0845540ea55441e1254082c0c110174070b01c9440c3c000035202000d070031480190b190286040c0b810228040d00500326459480e104000b800c000400c40c29030341440d8207a800700b0800322400c400208000c02070103203144503208224108107100040000b000da03984080e002090310282401c41700d2911840790054105605d0049 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 337643678 1250 337642428 337642441
    0xf0306010521070c0b090604030504090f020c06041b06050a05030c220603060f0807120b040f15050a0605040b0d0b0a18050706170c0415052802190302030315010314040b 74
    0x56001d40c00c200c1d4031000c7c1c00e0302d007441e135009000c5108a224110000f505c0b42020f0000819580c19a0242040001654110f2401c0e1510b860f01510a46021f00c02058a60300851818030540581d0305d40d0045444862039511250040c081e0750b04466072021401642c3c180c2d10021000c03580c024001040b40c1e86000c5203241c100341c02880c03502800c2d08002565403106808001c030314192151005181d4100a617030000d03850b541405981841d030518042d1010031080301211b6a150725038800761152490360403c000032510752080105864513051459440300320310040c1c3c1c010644424056401c410043c0000840c106940800b5032001c022070700c261040e40280d0003c02c851078101060003203809460104040e245441c40d09000c00b4001c80c0251501100380042d801480c500443c03c48440c60903141844c0714030850b40700c0c001e2000d80303019490001800b035242610904115054504900b0b0361640141d07056548241034401060b0701001c9081c1010340301e4407914012540c0c08402c5001d0703030144507841c240e450181e = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 337644928 1250 337643678 337643693
    0x305010f1b0318080906040e130302011802032a190e09060103020d06091502070807020414070212160c2d0f030b040f06020c0a170f0306010521070c 65
    0x1080c1c0d6001e040c10042c0351011501050869486168020003c0c1d86961055010403a280201c0d045070040060038428820701d84404c08c40301e10031030301c0303a4001c7c0000000800060b60004c8000030086d01540100d501c6440b5a01e8030007192603c000700100c0082c50040c04002035544100440c5400000200350001d2010290340c2c02c0040c1d01038464401408107525581c085003a0b4195910054401070340c1c1c604a10810100119092280080200640d02e500c0c903401c20782402c2c1c6c0510400c91080e4908402c1680d825001650203100348825005000074480040304038429502903201c00d86c440c403100344288005440307031803031401a091520044988102241800c80980c0500d00284045958034a0030810406503100c008250380e4440e0309a5455151440c012081a0000800030310050000c11210304944000a0130010140a03860480c1022152a4040c04a00c6441e07440b4400380340410000c0c40c03650088004006030f085174980703107080189400300741c200e69005503460340026036400c07080c2c018031916 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 337646178 1250 337644928 337644971
    0x10020f190c33020c18060906040902012f030a020601031a0105030304091e050a020c150c0304060e0f101a2e140417010e06040b0f040c0305010f 63
    0x9641500700c912600895500b00b2000c52007407100d11141100200c1101032080c0044c100c9010003410410f100c102c04070744e0306038941c13044402900424145c0d0004031710b8902070260100f1560180c5651040780c1181200c8074421a04501d03070040c0004039090540a00d00401c0104803c12107940541120750561401c490481c08045641c00120109001846941d03404400c8900302d40b101a00010500150741040b07100c1c00d03050703d0443e011494041000800e450f00c1e0010003210050320241e554011480d1070054250a0a5a059034800300c180006000204294014a28615000112040b0103074040c0800d143c10f11060012032542d41352019010042104003071025005c0702100c0da06204d05000300070780c407050001e081c64405102011f8006291a00030688200c1403040ca0031103559850712030451140702c40c01d2490b180030b1513103410702c3d140c4104004950b00340103940c84600b03d102c648800e0301d0880c606001a0040d901842c641d00700100190b000d11900c0d540c07909548c8080369801d001b09245065414 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 337647428 1250 337646178 337646189
    0x8040611040f1d01052722050708060718050915060c03040e06060a021015080a05010509061003120f0e1804020109060206090c1903080708031009060b030610020f190c 73
    0x1248001c0c4c6800809003a000080c040091500b00311b0f680c440810030b440c680c40036112800c00c0741060104c0103201d0041100800d540da171a085919588544030101c07004900400c00f040c050720550020700491614844264000192445403041c0c44201c1d4001904c2da0f11441040200c0d80c40010f04120701d5144280c005c0e070005d400c450440c103059107028042c3d100d01d818920603440d10b43d80d0301010411213a2540c5180546007440846e5504505894480c2c000e10b001c4c3c82160042c4500c9002500107a590b074001c00030b50341c8c0003c0310702d8010f04c2d10000341c800ca82c0c40c5e20030b83c080c00700f0410088201e4071a0381c00c8403400c888455603d07206041c14000034041a546da0042421908080100b041c1c5c9500004c2c0c2c62080c140540d200f10701002000c00c003510302d480d1900010324140e4006003d100b8132401c138001d540074040030041001035a03640e224600488860340700e400803210003070000515500d80348034409013503121b50041c2c6540b2810104141c2c1040300841c070030045400030031450028070010a0b00e01c0081c26 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 337648678 1250 337647428 337647439
    0x813090b040c080a0207020a18060e090c011e17040b041109220f02060a02070503120403020a05090a0e011e0e030c1b19091b0302070308040611040f1d0105 68
    0x10030421005143c00001002602669000203a010454903800710700001440394070380d1503c0d038801a041c07604c0944404d21620384003141102c0400d07801500403540888a1005031118030300e03d55008a4041d8404d4000107510a01208403030003582c000b03220000030701c6148541c00c00c007214545440c0c0004000081c0807410301074640e8a0400507440c10640386044095680901a2500d00c0302d0b25100c4101e91400c80000d40111000c1540354040d034000910700c050740c1007202591110522420207643c2d034001c610010398850003104c0100042d0078844d06464016401007000f181b04074845258500351403030400307016004d4254003541180022207219010720805000b0107145042034036400981d548420050f0041904402c41d0248a140d81d15010080c108010b003002c0c0c058161b13640d4401000f0084044011000c2108081d0101124840c2c401c0f5001c0b1a41030f2514651916181c4410006000c02c0b00c81d5095000c00700008607400011010042c000c0071010342c80ea120b50058254414480010b9128a0041 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 337649928 1250 337648678 337648691
    0x11030d05071b03201b120304031a070305280f020903010207120e0a0b0711030c0315010f05040c0f0f0306170c13050108031603030603061d0d08011a0c0a0813090b04 72
    0x6080c0200f0048500007101d02d61100c46c044070310f0074213511540d40700502c2c050242000314a0344401007a514480c1c030958070100045c2d901c00b27030700007050303201c01440c0c07680c19460041910041780181d200007208003581900500300708240c000b103401c81e801501c041d59240c00520301c1e80f940380e5103e51404552441a182640118174150941d4100d02030648010a540b80050056800d074908000094039004010100e0300004220040914544400e02825a9100e0100008240c03800c150280c1d0406080d035aa8100302040c10060880700000820500300805480305400140c03404000d80003030307a4541031009080307050155402c00450b074401c1c20303011012130b0400d00104202c5102000b0b8488045c01c1c6208900550136174501103005003503940004000c0c0f071800400d2290b004d40c2101e810f0100006204807502442d002105503400142445242022952000480c5541c050080600800541d00301195208016580d41d8011178009003a4060002c1004c03404004160042c000e1548940f010341701013004 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 337651178 1250 337649928 337649953
    0xd0510051003110f0304080301060e041107030f11160807081b010c0804090614090a050f07050a09090606030b011205040302072612090406050111030d05071b0320 71
    0x501038625a4424036954540b03d42000f081c0744100e410680a80d00340329545d20f01071421801c540c0080c007a0500080702200c80c213202e07087c07a00c04c8441c0508011102810485c055504840081e0484500703020420314144c403150400b820008803a04042200e2426049414188042c0c503081c41940305044590000928041c0840c00002d6014004428078000506503a98185840c0911540d4003004005180110000f000915011000c140c4801101c00f0101502c4041e40381c01601c0082e500f2500001c00c080100c0d90941c018001099400d0003824409802a5601641d8003116090340c17161010940f19290b4549942e80f081040380045070a010070003140c1450307140250388520f5800341c0080407180d085201140084035100b072514000010491391811030001b599090740d000106018029400e10b8000f00c1c842d0301400b54985402e4480000718104038040441402811014216900b0300c410780d143e505044101c14040785400f8081e4884810180f46400700242c440400000d000c0c0b175401081c1c03003601 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 337652428 1250 337651178 337651189
    0x30e0312121620060105041a0a05040f0e1606080106180b0f121005041107051203070c050d0c0302073501020d020d1a01051608071a0103080d051005 65
    0x208070354640140e10200070010000d40d1501140c44804a194180008803a1010740002c1d501781070ba04c0030f07070303040c4103004c01c1c04ca004c04080c4980243c55407129410740c0500090030190300c82240119200c801103032a045000c54107003001904188a00d2003100e4060130f100080c0c0004100b4010200c901d0000600082b004504081c00c0d801e00403141c48103000078030340303000811081c240c0b1383c0c00f258110b51706840d0605041a546a000d54030500b4081d5040440fa28082c2c5501d00c10f0300c00d82e5402402904a403c1d4401092026a0004251105011641d01640b02181c0d04024824078072155460323016a500c0241400791030503038a40c1c000100c0f4480c882e65884d600c440f64070464140e41e014160004104c49580889029000e0300300c140004a00c04200010080e102e80c1140105400824946014441c0e00300111868812022510050b04204a52030005800d100052010b0341c066040860b010720585c110981256080c0d01c162008d1402040c034198010051003881d0300000120307032054610b4580300c042031 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 337653678 1250 337652428 337652431
    0xd0b040f020d0c0e06010e0301020a0504092a110129010c030c081903110310051e060a03022703100c090b1909080703021507020d0f030e031212 63
    0x40c941001850810215268607840354009036000c00c2c03403210f454651012499040c0c04540070ba000481c010f0f840d040c14101803080305c403e44001c0c0e8460780341c641004425406003000a8240c1074003840081e510703a00c41c64100406035021015520144107402c11000f560940c0d00e210809401d40000300f0104411401b12081e01a00c2c042c2800c241ca0310344014101651b03804240e48010380b00500003d2a80600405c00b80c0d202d000b0340458034100308040f250000144240002c441200c5807100c10a018030036072900c0300c80b440c0791046a50f1100c8000c0304032000306030b00c2d0b00b143c4480e40c00f007a000319544480c4602403e02c028141080e20071070200340c0b05140080c2e90360040c15102c0d44960f030b42d00101d00c0d4151007814000701601d028181c0d00d640312401002080d001c0341d0005100c0010300c200c00089120080481d4030811a9001800e00901c003e25243c0741580703600454080f0b900c03080240355000002c03648045950880c1c002c0d2a5075543c508100c06040c24140032401c440110101084080c40c514480050107 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 337654928 1250 337653678 337653683
    0xf1a0a0519270302010501260304051507140109060614010807110102040e0c040302010f0206010e0606130306090c1809170a09080604061b0c03020d3e0c0d0b04 70
    0x1154900544800c000d181d07030302841d0044000c200b26299824540c054000b03a049405201d114101c0c03041c1045010341c0c900f580302c065081a002017100700490302d01051840c03c68883c1d07054440c41e0505513501c101c0f045024450241440e51203620000134803a10303110f8000188007944c0318202104c0a000001c3c1801802001030b030a000c51241c00b00c04680095040d20b003d403001440c4600181050f440150442c1c125100072070010f1880380801030010702c0800d07818100c031450840c031126600c5540c03c12000f07421025191090b00d13000200040458124019403030136a000700c42c20b101407400c04900110340c003240000d03e40c01c1802c1c011402d0015407404040800038045c03844403500d076180c0c0c40302280c4c0103c655101138440e00ca084244414072909038040066180c0c11000e044620784030b80011b480b080c8502401401503004000e001039011301610900845c1903c050840c0640c54104860f0028003640501d6101000e2100d013034a41029800c1007c0c0c1a030240c122006110031000756500c0c0010038008000 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 337656178 1250 337654928 337654931
    0x10e06120a020c10021c20030402012109150c020d030902030109020a03140c04060f0302130b0a090b0f0a0f030f1401090602220302060406030e03070f1a0a0519 70
    0x280c24407a441c1d054070702100c502d00544144482d8848154080e401481103500314103090880c611a680140c0300320500d00c114100d20070036034048420600340d560070081c000c0e4148a000c800d4030010031b0344004019030110030700d40c000514600a003010a064441c3d0003504200303501c3c0055035003040e600080c00b44a0b0402e00e00d00841c041d0024070100703001d0a05440025000b240e601c00200c2001100c58150148441e08002c44003030503013080801044d40d03102d100310000c0d0303d154001032016086c0070b0405407a801241c0004240c045888000c9106504254031981010756504001007462901d401d8520302003400f142c6543d141403e007080e40105086500c4010712518008010b10308220341b890144454212660080104240300e0400c40007940c0805805001e119000d1020b001d48104200700c1d1060341c1d00a41807a0420741400002d400525020b080341d1120f20040c4207000000d410207003014042ea20070b4a06036481410009001d600040142c00d105c6800e0a080070003950700100c1e40c3e8409800084c240 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 337657428 1250 337656178 337656181
    0x150305090303280908070b160c17120438180f0106181119080a061802040603050702030408100b0d0212010623060315120f010e0606010e0612 62
    0x440b0080404404640f000c081c1846208030070300c03128401804496000380500000355030359600440100c031a50346480c1c0450259400b0a0204124540f50208030316086103803071a0661410f44800d900c002100c0c01c44804400e61850040c0880b006006a2007008548104055200503420811b550b84014211031841a85d1030309201c0882d42000182040c054200080200d40e850710891a280100340030342d0b46100d0b0038800d0b41e8111203d903208a50815942082d1f102e10240000c10072103040303802030464490143c607988040b0f07084042091004002e81060b500680e43c1c0c2c5824030160a40d20020a4030b402d64106010420400d24082800c2c1080100300c60009420680c00000134203102c6000d0010750080508103054841450550043e030070f80d10309001119040410714040747d1000444407003150040d07405d101240d0380c1000401c032501102c4c0024829040705607001e1045140090071485078440e030303444200302102c62005200242e0020030038038042165048540114040c2c0c414000c424403076180150 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 337658678 1250 337657428 337657471
    0x30c180402060708190f08010305060f151c0b090604050a290103060f06050303130b0c01020d0221070f200f030406020a0b0c090f01050f130906150305090303 69
    0x802c50f9030707495014100c1034840041113071030170b20040c10012550104070403000c2d0074801401007415038102d0354494000c042550b103000c40095020342c082c200303103010009440d11030000d03501e000c0d55101d02000f0494140c0541c1c0b05040844650303401074405403413038001c041400046000450030418160700100c981801e00181c43c1411510f0210080102c1c8455020b0008010411710380c106001d041c1501d0401e0152545601c1090781b04d00c6182c0f42c40205080ca41e00402030b00386610050404900c05400060074071030223400c4401603134040140705070044144681044400d28001c0d0351764001c9058903003910341d946111006014141c1e1403152082e140094504d61514020030008030181704070500a5030748995071810060768030100300300308848039440c01c1c001485003484001a56180d0b400101080941d0480200556031540f100302400ca2003542041301018003a4540e048500600061900080d06441c10200c0c0d0701c6503d403542c441d0308040c100002c0c03000035800001034941051411144400490404 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 337659928 1250 337658678 337658689
    0x11206063305040e0408030403032910050d050106030b09090607050304060e0f0d32040b0715020f040e0c160b06120604050c010906020d080406050c270f030c180402 72
    0x9034804c0181c2d10040381040208244440558040c1d0320985090106041e503903003220014200c09818081410481d8030a41d11b851300d00b40f218042425820030603d0540200e540a081d079000b41c0088010035102c802c20060350421804050f4486085c0303000d0021070504640040c1544005040038000a4641c0302c10202c5420911198402c82c00403c102d9081a0207000e024240079501010700341504d0b090305001b00388866082502c00785048100072189005c2c10041e0707a9545801014046c5c4070a076141181065081c411f01c001d000f5426041c1400c2c0d10f40c0c3c0340a0700c403003c4840041002030295030610000803404c80300010805040e5100710b00001036074401002c04c901c00140c800d0880345100d18400c0c81306005c00814a48000b00f07081c1e85901069031142002d0380d4034105010500001150000060003245c600d40c0080d81082c40855000c0c50400c901d950111912000001043c40310042451b208036440c18950b03880d031081041d0040c00c4514050400a034008084503000c00b41c0c0800350000408654a4 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 337661178 1250 337659928 337659937
    0x30309020418030206060a1502060402060a1b030e041104120f06020d0c0e030106050102030f120702030f040806070e0f0f150c06010806150402030408041203030b0603011206063305 79
    0x2100b81d565610418200255600000c0d120070f402a00030315000f080c0089451100c8403c00440e400030070541d05d072a800e0180079404100504200400000031900003844c0400c80b401701402541c6000d610030700301c41004201d0b80a42070720002c542c810081000404103200c440c881b210b0700300ca030300411100c141c10800c01a1144065001e8054544240307904a030350008030000800105400801c00d0a840c2c200690740d80c4a0310818041c2d08009109411503001003119041e401191881564240700004910400c1078005400400c1c840d0491410480390503807000c00d009030500b0403250a8401003800780462055910304440c24000c402000c41c420380c41004a041342e05601d540d200703c1d030856035030b02d401c103071100f40964001e080f001c2000301c00d02c80380ca0a40252405560408446c510700380c0382011080c00445001c174220f05040c0c135000191116590a005103009040880c180d04a903c01490702e401161403a8004450543c148140342039004250078401203181e04411380801d66410483d0103448a008 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 337662428 1250 337661178 337661201
    0x40b0103090602030c07060b09070c020d030c0f0b012108090103020c070e0115020d0206090607080619030804061116090b0d060c0504060f08070c080306040f14060a0f0b070303090204 80
    0x50017081c0100724000c1c903a5070300441d002c000240000c0c0030004480c0058411000041650359450003500d003031150184602d1182c02c1410090840e5921001d92030070804099600c2c035414001002410440100740c0780058007100d00b1000e40030a40c0c0c445405020b82d00b030860400d40c2c042400c00c9004020040e04019240c895607805a03036940b00c5118000354840c01010b001402040000301400b130000601900804c016001341407990344000341242d0526000740703079560200e01c4114140f01c040e00c403021900514011401540c0c3e540c20b08501604c480340c580c030b0761662584010103c0d42c14810fa4034150b8280c40c01c000d00403610034244000603e541307042500242001d8941460b9000d0765812500038800c54266885401110420b00426951007404440c0c000100d2459041c803800603103068011503225000410004850382c4054803441200d040c2070142e030900f0550000d018892800c588804000c02521450080e10350030207017044024012518002e082c591260704050840d521b40c0c00c0001c9864 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 337663678 1250 337662428 337662431
    0x11010f05010b070c08120d0b060712020c0108090f151005100c0506010605190c05190614010902070804121e0f020109050306100302090603010b04110c1614040b01030906 74
    0x503100c000702c01e203d41c008072045449140032080060b09440200717103261041594404203081a00c04075641c0080d0649036012540f0007000c10070b01c070006020307822501240d800c075402401952589000500340c0180500f00e10302a80c480a046403100c800081e0b240c1c0d40c04030000d2254800d45411100c0040880c0c2600a079600041c0c01e05402c070480c0d404100000c07014000c40845030f1699a0300c2090701d0030311950b9180c0d0007014842458600e014014850881c00b14414812203070026010401011011008207044032190344030142c9046407241d107a41d103400360502c0340b411841d10f001582d90304414070440c0b15404a207040807026a0078003000010100c414040503209800b011201d00d4603079901d074146002240840d8541101140d94100010458440c400c010250340e0b90034119020401000c0c40140619815901c0e8105100162038034001d60945440c40800c0580b9009060609410000584100101250386007010041d01a8000481102d00415100000c0040340080100c0140c0521040986901e = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 337664928 1250 337663678 337663681
    0xc06130b1c0b010e0d0204202b0b1c14070e0702010515130b0a05040c02010b010219020901060827030c011103010e0c0906070b010b03070f110d11010f05 67
    0x40001c0c6240810403088039500304141000d5030019100704549074005a0040000c0c80032000500f031692110303c0240e030000e40940c0105040c0e1000d941036000e030b4104000303152155100c050303803180e40314500209a4008414014aa01d50300420303103a04a601d4000715143e6040103050510880310754031f40d0203010030403d6809098884503120406001078402500540c070b0000051258101d11a09481078900188410405452115054040d01c09110103a41c008003916001480383d890340701d02e01081a40380c0010500020013000641413500c0301004465005840400b103005a494680c4141920094240210192036500640c1c0b210300d000b81c40711a42da0b04600748035074440c41c0040900704e030085100003400f40b9201031403242101e000c28071980c4a441c48890200318600c0684003d412a1391015000314241f1300c683d21158401c4000f0707402082c502400000b0b0bc24181d0b485000c40e41c44440c0c40c1001010003d00c581c203a942c03030181c0d6402c04100120090950049003081d009a88054000d100501c00d5 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 337666178 1250 337664928 337664947
    0xd0305190216120c06030b040e0a0b0901150b030f131e0b100614030402031606030605040b090c1b2d060703060602030a181d061e030c06130b 62
    0x985290b06040c004461198400041d10035984009890b4190701441a601141c5450410780183c018000311540c00b0741c54540b080da504404002003880103000b5201c01c90141000d140c2e49007102d5051001600c200d42008050088540741000c0b40e8111440c0300c0c04014a40d5211200d55501d09102401007842645403011300d041c079041744801101900407060004582c44045002040388410301c44c1c200844e50300e080d80c004099081019591040c00034041e0f840c0400d2080c00c0011070345407a001100800c2d0346d030301c0a10060500b44a8109080c9003900c91200d40c1c108005104028001c0020b6418882c3c006600541c0c01136044c050040c041d425483c1e510b0001c60100e00d83d26113800c6c800541c0100744224000180114408d001e0202150b01c0c0750003079803500c10030f5801201d502000c0031100442900d20f0000041c5407141c0e44d45468012002c0d05142d400742070010410940304140c2107040060800c1c95140180ba99011410006500c4101d861940e00c1d41c3c0d0103003102e00620650b204244000020074400c0c070 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 337667428 1250 337666178 337666183
    0x905250c0803011d06120d030b19180b01050f09041d0d020309011202070c0302010503070504260d031506050706062409080a0503030a0f0b040c050a18140d03051902 72
    0x14207084101d28003600c0c1e60303645c05200e80c92444050302c0140c1ea021010040600d40664000c0e0918803014008007010328500700003204450042e40f02081d03d21941e00d51003150180c2e031048000004003440c0441c5414000042a41d0303034061440c0c00391045d80d5030008540d5544114851480c00c03d000e00c16910b02180200010b900c0c4e412000005002c00c020407992008481c1505c200c40c451a030080003210300070b040d03400440c0c49402c0105050300340103042102090302d00b01d101112108500c1600036484100306421560f0420b40c4450348a02414104140954130344c0102400c041074a03041e20340503859100c0c42c209100604000c0d440484440d1400c400741d90b81d0b4403da01441429451911808100ea03a2070200a955880c441d0024100350800d00114448250329003040415609002010030080500740c0060b040390412002c44000c250000381648151b030f084065049400d103d4801480d0203481c00007038400581d0061806845001c03035020000406001d48296005a040c421041440c9229500f01a5 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 337668678 1250 337667428 337667459
    0xc01020d24050405160e010c08040e1024110111030a140f0403020307150b1008041416030609141e01060f14010c0507080a08130905250c080301 63
    0x41e40d010a0640400c036400c040c01400c0c007520401d0001e402441184500f11034014000321140d04000758680884042580d4a0107070019200c4106a03030240d040568071000c0c4001c881e40100301c03401d0802c1454a0f24111803003000800f100504140881c4400c0300020740c0104404c0760380d0100d1507008000c0c01085640e076804010142602e260030304241e2522010240f41c1c00c01201c000300107900c00c01c1110006621000c0289000c0b60814020034001c100ca0001554002400c1003072000131000310411050108201c0e041545d44501006011600611b10319400b05d0012400040c20303180d2541244020447c1d48074030100d260110500b0b9030640482d4010691a030328044800105540c01d2400c04030b078141c0341c0100102182c4000384180c028030001001540c803110345a038161914018440e0000e001802844541c00451107500b083c1d0382c0394140540b00f100c00e41c503600603400d031030303c5c05003080030401040c05070324001e00e0b40c2034a0f14060307802000100c4481c501028003e18940003c000024514070080414 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 337669928 1250 337668678 337668731
    0xd1407180e0d020f070303120b0901081507110a082208071707050901120c03080a052512140d06150210090201051e280908030a0c06020c01020d 63
    0x2103010160441c4102e036944066100d4000316005140c01b000060b0184825900b402400390001c94003d032a00001042c2074004d9020040350340023504040c0080d4090103981c0c3e40510181481c1140c40e0303186404640d214986140281034000000c0c80c441d45041030240f625a041102040494190b01c0e40a03040d20f81700c1c0f900c64036052014a0039605c4151001180c0882500c1001d45152600c0c1e1a10f0742c001c01d00302d00c1d040181c0d90340d180b003000032004c108244005c00840c000307071321003035580d280100c3c0d84616003003851f94040d8080602000c1030001010340c3c580c451449068a04100805444000e0b00310340e2091866580750245080000640000c08030441d05070414541c007500d0040d1445116602581e0785a20001e0026904120000022030014a031682c00a5072421050401100415144138034503c0e00d03603034000c1a0380e1000071041e02e5000210b00054140c00c0003660400791030080151800c40c0707079440100386c4e42e000b05030307000c251070b007541916070b180b1070341a0500102c0e80344540c0e01e41c88100600c11 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 337671178 1250 337669928 337669933
    0x424060f0206072a020414041101120905070314070f15080108010b030c040c02010603080d0203100611032d0310090510060c080918090c03010606030504020d1407180e 73
    0x43c2d455806443c461141124030850f1300115045061010001c00101800b01e80c840e6443e0305c64407440a4502e034003032085200781e8000300c00280700000981044001c11748500880d0509036030200207500031580c101103030342c010004070b20403800364021414403104e038000d03044801c40c0540c0000c48000e55846501c04051030344a4140b140d03242c0c8a82d60a0703540345d442603038160f48001e00c113001c40d042c1940b00b103008191600c00001c00c00d4690362a82140d07413190702401d140540100510003011910311800f402071510b410100302001d12004081c5d1603001714114003190201010081d01c1a80030003031820f1103050140c203031941da0728010700313482400c14482c0100094140f07440e0000300c108820303600440c2660346903141d6580300c02d0241d0390001660f0000d48480d4014207050980c46030204200c94890203542c00e8406011100941030070715007101c40503800341007058104000d210140e140c030022103c2160300030f141840103840698259180411aa01a14445064140740001e4030100c0c3d0022150302c608505 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 337672428 1250 337671178 337671181
    0x30901080c0403240f0c1d010c15090602070204060303030e010f0b0f060309030904110c1902010e100903170d05060603010e0f0709050303070606030201021015050424060f0206 77
    0x1001d8049001c0c030300004040d202e034900240240d8940600400c0c0750f441002001c214900f80001c84400d98801d413901c0c201207451004011025100c101781810310780c81c00c0ca00401e4075002900d940b0341d42c245100d89400c025503a0001601840150340454544c1500a070041c4941075072441d00400a00444080b02055484d00c0420201c0000381d016035160001c004181c0111740808900304509a80003070810300152108100301c07003858540b4054036044001290b40c05444036000c5003042c0c201042c410141c8401100030001000507a00943c140307151503000c1ea1080d446003100c4070155441015138101804250034495030380390340b00001006201c0c004810f9001c5c0480c3d1504414022140070a0003003034400c2212130700060144600702c400c254007143d180b030703c1010b0995174004039003143e00c81d84007503070326580341da40500955804100e0208040f01c5c200c41000400d09500300708400310150f0140700e1241f80c0b10342c5030007212903e24400c150500c4502207481010707941d40e03201400a803052039245025024000 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 337673678 1250 337672428 337672441
    0x16030e06160e1806060a0c0b0c04080f0304060c06230f1506030f040609031709161202010e091314010506030705060a0c02090c0d0f05070e040b150f12040503090108 72
    0x80c40000700d01c80d842c0303d21480e86501e020410b2130780240d818401000640d444502c00700b0010034034a070003990140a81030b5900e091482c00c3d800d11103a0001c40c0429802080304110f181ea2120600140b542c0003480090074501107111258607403404040c402c09486041c007071145224080d5800b50140710565080d880c000d20110030700100d408100c0702d2200c4c3d0481c030300c001030100c6d50b541c012059282c440c0c540015400703915001c1e42072400050f40d684c0c2c01a406040300000007042d001d4482c000d007210001a07100010b89a0000300044034444800380111200c80200320701c2c1d410620101856075011620841000d4518016402000c00f02c60300f40c0f09210b10742c8001210308110301180c0140790160380d201a000380540a11070021800ba02c00441c055041004c511802041d20032000c0d001e0f012000401c190a10b94001011401440c0e10903128620b81030540702c50381d8544011a06040c2e001c50855102c460b00d11080d0107902408400249000d40281040308104000c4010710402000340c8803500d207a15040d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 337674928 1250 337673678 337673689
    0xb1e090c0f0a060e0405180304030809031605030a061e0e01090b01050108070c080703090e090a0501060605040f030b0a0e011d07060503150919021306020606040c0816030e06160e 78
    0x5118882c08115103664000c3e643c105038221b036070f02030944a000525030340d0300045c0c185141d0143d4416070f500d50012902e91043c1c5410300c01041072000e460000031040b804c3c0380002e51180c040d4400101403d40d60b041d485c0b11968a85080c0e501c0540b41002040381a40c842d078100c1c0a0a0b001e10b080b100e150b111030011030a58050300b0202e0150700705680300d01d92403116075199503007644640c07402d8060010340748002640100c00d01019114400090146c61b0924403440c04609540300781e0810340a0000501080c04060301c40140311044a801c0f80d04111607844150050005110a0a40d03034400d5003001301d4180303001441a03080d5000d00380e600854500a50b10041200c0700d00040e07806d207291303981c08004031200f480c1c010303000780d00300712007010b060903031040744ca014400c0707034030408100401c1010f0910402541c1c0d01070000d65803096083d039051040e510325980040000d02d00501e08601c1d21011082081503c3c440da1100002c203640400b00d8017140ad0031091600c02c200e0502d1001e00040110441c0c1c0c483d030500 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 337676178 1250 337674928 337674949
    0xa120204050a05070906050d021303060f0513120e0a081005040302072c07020c040603050c15070b0609040312020a02030415021603110d080f090102150f040b1e090c0f 73
    0x555514905d03a041200441d8030f03a00c01055040215020304c0702803650500341e04080001c520480c0001200c400d13070b2803004240d401c000d100580c65440c00f155034000c14200d04c5a40d003025110b26200e4048090f000000e40b141c006034128400500c526202035005150592000e070149000f6004c4030312590f6120301518000303000501020409103000241c4844105082c00309811461600603900c2c54002c60b4080340484e105940b05940c0c1e03034031201030700300b00e4184804902100c00c510a1a50325101107034a40d0064a800a4030050003141c0340790001d0185445040b00c2050460222025503403450040b1000395a50000e0003160b0300c0e68452140880303ca40001800b02d100900001c02445440c80e58441c11141c5526110580d089034900189000007074000c1e0081060301c4101c0100c030b031039002500c00285070030824100034906030280d5050140b404c00c00e1200c04d620903413220700042999035003ea0310004420308000c00c66116000820f000d400d540c0443c0045c0000d2003510070200500300d000c00c02038440d90 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 337677428 1250 337676178 337676191
    0x20318060103050f1e0d050703140d0605280509060103060e0c04031e150509120a090f0b0306090c030402010e0d0b151005040902070f02030715090b03010e150f0a120204050a05 77
    0x50011b0441280107001500509000341001c0320320000c010400303032565100c00c9203240a03940d038a00921240c6407071040040d6886c1020307007002c0e802c441c484ca03403c1000003900410348520b5000000419980c800d810103c0600490849407110b803d005005040e0354000c1d010880b040c4600c0650048500c1c04a00389400c8250405d032000c441e040d4a4201303070010440506000400d001e951039040010680300c0c01051041200d0703a907038020518101c034403000f060341900000c0c4810f0041040c05220f6443ca000d407904881403444180d0340307480318401695001c9a2402194002c0000500602400707504e144007840740310881c0b0f200208414002c100000000c0c0ea0350040080342e02408107101c94040703035024000d10b0740314172940e20a0010035000280340c00c036160b2149000f10001c00e940103e5650200c11400144281d00e0804c0c255410440000c482100041c15180c00126103c58174883d9510f0414244448502510400100e42c6541c9200019150354109a0160b0b0516000c6060920703a489900c0c442d00 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 337678678 1250 337677428 337677433
    0xf020d1b1d06041a0a060c060b040b060a052d09040e0a120c020a1e23010e060a050d060906090b0904051504030c14010603060c18030204020318060103050f1e 69
    0x1980d5004003c001e001c0844440c2a02500c001200302030746942c10184041c01c1651201440d462051030140c090341c118240b500d00440c00d0a41407001074490f00b09a070a1403e09003041a01c07001c482010420062082c8a420100c80c1d030400c521112101c900000c02c2280d00030f88060005000801505540e442c40c101c0c020300b01e10303a40030300d585464070500e01c042c1803500c0200041900c96695200201c6811114000241300c0e44444081148130100500d10304840824012101c6410300000041c141c1c00381d0004841c02350718002200c0180030310980c2101d01c0070a00900400c06151541042002415607024020040e80b8050829209280080d00c1620690b41300c0300801c5582d0700011044007004c0041c1040701030141b0b02d01c01c20009500a2101c0003040800c00000a41d1465424601c0907039801040c01c106104861500d60f00c4035a082c003428094a806681c05aa20340301c400407102c08400b8008840000e01641d0004010032102086204011010100312808040d40a0b80100d40380d1035015200840d5 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 337679928 1250 337678678 337678681
    0xa0804060306080a150209032128140306040b0d0506091002040e011802070804140f010804080901080c0d18110f0a091109041e0c020106060c0f0f020d1b1d 68
    0x54001ba00181460103000c3c05444007644041c140f10510710181103800208040071400c984080600c003080c403150318001a06401d50303581d5003409415211440c0d1610808030780000000c0c1140c0703598009070502e6001070191000000a418103030b4582e0070aa45050f4140505800703003c01c0c1c20035009840c15500074840d2010f4992070000b05c10a91380d64a001081020b4083c0150400b08603564064002801e28510317019140c0c0e203a1081224241070f0f5480f00317050080e068103000114403080180c401e64102803e103441e60741c23101038800c500c40c043c0314610003400c2e0400e010402071038540180e40e100d82e031050400d8042c00003443c2c2045041c490112140703030081c400c1041000600c0403908810f12000d0211203080c540204200401e050711071003114211045074a01032150030455510801500e120349100802102c2c0c00d00c1d8008011246008018000640e283c492000384a54034100c05609580207050340e17070100c0d031842c0810310b12854a0031401080c180c803400003104200e200d0149902217842410a40e103 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 337681178 1250 337679928 337679963
    0x1090510060c021305100602010b01020316060e07081c030f09052505060f0a17160507030909020301092c060105400605031c03050403050c0a0804060306080a 69
    0x1501540b06099034040c030510701500c500038840c8261401104105e041d150302c1c1781401406803d5030410400c0c5411940104400c0032101620350845400c10303030180c40403c100600f0207044e45040002d401c0070855000780b40d80c1d4601078032104107403e0441c449071020300c00d900b10000c4c0d0004403442108094225045030741e1074803036054410540740e089041849d42c1043c141d01d41d0081402038201048034941040009806086250031541242620441300d9568055140681d003142507500e10500c81424000c000c642902018041c010712000750010144c219125a55154014094841c4038440c00c002c5402d02205498200f03084a001400410400200710f02d900e403006105100030745003028039250f04051000ca5506d5000e08c1c0f065402031207070f072003800e402486c501850210303451640028425405a100319410340300709280903920408500340012560f5071810251060310030506d40c2c0c01075010304031a0100704036040d00604165000d9580c1003020039202d4005940e0340d40c14410181c4200e90710180c8048 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 337682428 1250 337681178 337681187
    0x9120308090a080403051006051c110402090303030a05010f05030a111e10020706030b0a1d10050901030b040b010f06020307060c0e100c1109010e0f040501110c01050a050109051006 79
    0x200007015408441c1200750a0700c48040c0b42d001500115826003142e0030f03080c48441140101d80c00380c4012212a036000c03c07501e510303c080150805000703160760041e4601c40800c4d44c0361b0341a01d00c07942e0301800741d0b40e59240c140c140340001d040c01d008004100c00b81c000046030a060004101d62520b512040000c8103608032800c00c07101901d402000c3d01c0e02e5689084d00090303500d4003c000c00c1301d000701c0c0d0014826113090040290964440402050051515070003c0140701e038080c10708084034040321010307400d940300c0100c1006600003a4205541010b21040000304028242d0130342880703240140c26074045662110300000b03102e10361b88140f10050340b0510038440464081d502c02042494542090810b900040012a400458440c40540458944200d4405206490301054000c80701283d00c1000ca40c1852000d40309007030003818041130404940f0003c0d040040c00d40c41035051840b090041611a1186a181030190600302c6969420342d0424000296683e82405424004d41200c0d0444803600e0509100702c4 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 337683678 1250 337682428 337682431
    0x807081003020409050d022a060906040503070f060f080103110910031707140a030903140f06040b0601181424030106020a020a0e0f0a090201050c0105070306051009120308 75
    0x10000308800c8800401680c40313206032a0224071941c060b1072500700300304000e420302c10224110381c80349160281d01144000321255031902d24404480f42500d070400135000c2105d5008580015405101340400401d414440b801e50380d045a01395603420410700e183c89000c407013040d02803000811104030b035505400e00e40307030101041f544031000b10000c00c00795990381c42c0c03590103034040e0b42410f860316400103010b400e00c0103820111101d0200c0300d005002d01159075074000e081014070710002e0030b0040380054441d040102072180030b2001d0180e40c102d690604090a0081c4040401d42c0d40030301098082c0c1c6c00d40900500381d0140300c200d425a210f110802004d50007402030801a680203401c060401d69600002c071100c041c06035003c7c6c51700703a0003441c500c240e5105000f01c01d40f880d0031142444030240104201e942d1508009075010038a0540461610440d2005071464020707009443d21039400c0108014005a00d54040b81c02ca031400c5618101003030034440207541d40342c0395006003c09102142c3c44d401c0883d0003000b015 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 337684928 1250 337683678 337683691
    0x717030910030902100e01020c0102070e01090507020a060606030c09080c09010b0307020f0a110111120f0f190c020436110904080409050c0c1903050d0609050f16080708 74
    0x45603d010341e5000480d22008855108041140b04561540783d580c10000c84400d2030080c0000c1c88424100718011002900501c06c2c0740c0065203950000368201d10078080710704c8590303001c0414448141c44a0010b800b8000030f00038074000403400b550002f80c20b507001031030a0040b078029041500a90804904050799400203058409510504403407801c0940100020301c1e5070760164102855184032040014184030500d440302005612100584500320042c1085420b20045001e80325550840841780f017402d4000c80001401c0c0d2001042c51b0380300d164102401d6185188211800c2101010007501140c1d0920041c010440d021381040c045802148520900b034480390141c05601002c010800014100100c11103048802c0b001c0401d08200d00d82c110302909821807400303a0000e0400380d00d040d06965803480310580810102e8a40c43c0300007803601070403c0740c89001086800703010480d181c5030800042c2070103460300400f1025040000300c610000810b09200703c40d139541c45011913103a0310710841d6403a9025002 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 337686178 1250 337684928 337684931
    0xc020114090d050c120706021b01260a0c111b040207050f0307060b1519090512071d0f0412140d050114090402061909081e071703091003 60
    0xd06075180300c03840700c0b401e10403801403107411208401c4c011500c2000c06803a00d40d42c42150180311585e000f0a814600d0070160301200f50b83c04c0e000380120b801c6418414541c404102c0c20404120300c0c041c6030405440f81ea400b40303041c0000c1000c550200c44811200b440480c1c503070001d40b94010600e50042800c07100c501300074009030900c01d26450b082e05040c01c0420f030a40a600c0064250200302182c0141440030504948a4070240541d800c2625503120b65041480d05c05445110002110f010f2014a009444007074194260b44c400740000e140c2d111307100d024007151084c8004418010410000145100b1141c1100d0307100c0359241d6070381d1456001d401d0030f00305080c84281e050750032020b640b450280005101c52000440c0d036515080740d81410764400e16005004210a00800c40941c464108a5018100c00303004000000c0101a003243d28540c0f6400040060256442d10400e00c02201e06503040f1100b6030094903203d1f99508104041881130b41c0390818107801c1481442c0300e40c51310700603844804159080 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 337687428 1250 337686178 337686187
    0x180105130e01020d02071a010605072406060f0207091107020d081608030f0705120f0a060e09010603140a0507090c050d0203090105160c0510111b010e010b060a0c020114 74
    0x1142c2c26078204441c04040c00f58081421000d1210400340034100200f08a540000d03541880c0002b01a44581400076202c0e40001c008500312020461201441c1410310f041048140c2d142c0d840285543d00c1e103100600123109098000c50120410b10609140e200c07040c032800e24141c4503500388a4800c202030016a030155046c4005a5041d00704080303407844511031040e1030390b82c0c0f40c114891400494050003a0741040000e10044d24003481d6000d04507003102149201c60100da4544500b403010b03007459000300d401c00c0800001d1250310075054001c001964842c1180081c0c0c88203441724555550003484010702182e100035410010311800b503104180004881c03500d00c1c42e0103030342d070340e294217981c415204c3d40d84907035650040000c06030030742c00b8802c511070043c07916161079412901c5840d62454141941c0f20702079a5245030452a40d0440f040390164881d02c0d43e00c0300303442c144070070050003000581d940d04015401c00300850560701c0d00c03604407900350907281c550100286c4640c004441000c03954a014419520401 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 337688678 1250 337687428 337687451
    0xe0a12031707030207031206080a0308040c09091506051f0c0302031201061805041e050a0b0d050f07060e1509010201150f06020c1e1005090414070e18010513 69
    0x504a071141400b43c40140c0d440c0d0f82d40c0b400900c0c824010f000e4001c3e643c5011024014420b001c96004039858040c6003001c060f86850600060041c00ca9000f081a14035003041c00003000f4004040f00350301e20300380300208003069880090111001c08058200303071441e00da140300ca10042c003034158207040da070003441101d060601d4450400300300c28082c0c000c500402c02c10b07040c416007140f1004011001e06410784052010074201c0c5450344400089200d0b15007450303181c02c00140ca18046900c8418080d400408919085165080507910b40b44482e10b4582980144400031560300d01446101c0400792020b04800c5240064201c01a110340003c140c4d64115506c800d01b1444902c8101c10034805004070403882c02c800341c646800a071030040c83d04102d03802000c0070210074036040c000f201e180c00c3c014401d440341440f900380c000040304e05104d0204c10a51051808d4081d03000311000c034160502c2402d95440c1c40c05030700c140c0c03003c010030640d9074084114260000310050102d41098010400101e0b11640e020a0100114 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 337689928 1250 337688678 337688717
    0x403080c0a0b0f0a230105040b04090b0a140705040b090f010c12120b0108060d08070c17010504060c0503040b180708030304050f01061a0d020a09091505010f0e0a1203 73
    0x3070b99001a44203c5100780101070a41744511500c10059040c10f607070030b0182c01e90b24a0000414402c05104507517920f2010b1198035039400220340c0960004c1c500c00940303071401110300181018041403040111400020343c80c42c0c0510101e40c2a00d01081100e424508880c1c200700c6034040c012080b90401100c4c500b0080040c030500d00fa01042d20254450b06c4940c002c100d980011907450003041030400140f8018040e05403a41300f4010483c681200200d955200c287c03d000c1000d00756680071a01c51024600b06250b0f242042d80020702a9200e510300307001484200708200c420740402e9034081c040012050100312044100c100300914060b1f0402950b145a81d648000e03130841d00201c5003900e85412100c401c005d0038000781710b1a0054040094144489460802c40c04864018001001d07a07403030b070014060301d0960040b60390400400040c5828030440c405405072122502d65445141d003c503c001e01c4120056028810a000e03003180901f00391443b9140420b001044d0b00513030010340a00c91040d00340803051144 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 337691178 1250 337689928 337689931
    0x1404050c01031a0a030b151306035d03020304110a030f14030405120114070905060a0507082802070b040605040506130801050a06030b060a05060403080c0a0b 69
    0xa040a051121004000034040d18a41c6110b140501c40c16502e0303010903911050101d0a0341d411820b8031700956510980e9807900801c41c80c2440d40301c08495001890540550002000d0724440d1076000e03001584070034640084070f0951007407008481161070f850101d1214004030f5041019100494100c1000540c2070b91200400107807541c0040d400100b040107001240c0c58500b0800c01c140c4903265251701d5a1100d07401d5050071031000741140c0d020810f182f10408100700b81c4010f49001051036820841c40e80d080b6001708106121003403517070090400294000d02545c0408100c03807000c0c00040c03070030f24001401ca41592004078202e030325001c2800000708012050310303a915161040d00d0307803201d00c0421843c0170386011344a42c070050714098104414041158020141e50440d03209550254482902071b1181e041e4180340c0d041001c480d0300e8013040202c0e500180d00200700304c81c0070b4010b80b0304a8613020280040c0d502140071f82a00924100000c1001842020090480002c4202030380c04030000c90b640d20112400 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 337692428 1250 337691178 337691183
    0xd17070c1730040201050f0d0e030301090219020109150b04090609050717010b0604210b0a0c09050a0815180f100c02030921010e012f04060c0f061404 66
    0x14800c40100e201e228500000c092a050a2150311501c3c2c00e40c00280103105106c00b032880d80b80e003c0350f01c107800995500700c00a070760300c01d030140ca89940e150070f4410020340003105207032003c15002c2d920584080c010f116600802e0740110804035003d1400b80c1c402d001e03103018001541c00c039580765042008106140302d1a681a440340c4040c0031101c0c90b1101002031800214904039071649446440101969030000711401c0703546003e600d00e00c05846080391145a00e0351702d400f8100c0b45132030341040710081543c0d0250240482c162030310020f180d19081881402c0d296809010300c5580701c3c0c1c502c81800d04100d01255130081607850b05241078052544480d081c00a480002107050b403240d2400e10711800303d4010701020640500c0118104032440d4009184d0481036070048100800302020f200d1031032400e41240c0c810301004402407048844550860840003442da102d00c1e090310110011740003100803002228100c503801e43e28443c13104102d80310040034945111f401c8488030b40d030780c1102e07803d400141e5074584243d0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 337693678 1250 337692428 337692457
    0x40b1008281b091d06130603050a050a02030706140f0d0e0a060e12120612120a0e03060702030a02070b0d09062f030118022212050d17070c17 62
    0x1001100081c02070fa05541150314250103c90080b070403101c401002c180c5c4a01d044a50041000c0301c0b0074030400414880d04090b0050041405900c01d00c180014240c007401e00c00e80071200c5007a0358800c11562018000035403101180200200009845260050004001c042000141906800034a076203495400b001c1124580d0300c80c4004086541c085c0065044243c520101c24508018040c0c030101c10000200304500c91101520480e000040c10080d1098017241380c10b0b12952180303c110f024284005117200c2c24401e1182900082d496440881640c01c0c070f5900c3e03002010b0140c20303c0020309194106a90700c00d02203030744480c000c0100700f041c082c4901d00d2030004040240d12194582044c200b00c2c0d0508054001c0300c08000400102d41d400c2d6440041155030507005840398000d1600c040e00c4c01080c0d60012094207061004140c0000c0b00d00415000d41c814412078111100b0040141d81411843d070035140b2440076440019035160090050051a6200700c01e003600b803696801096410340c100e0b104a0500e078 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 337694928 1250 337693678 337693721
    0x91e01151211010305270c0a2907050a02010c051c050c1603150207030903020a0e01080607020706080c1c1406030d08093a0806040b100828 61
    0xc88516216402c41c082840c00380101e1405801c9058220051110b40001c414007002d61180075800340100d0f42501d00062a04c1c280c590756146c0741d2000c0c103940c44900711b0f40007820340c0b101c0c2c010000d0341160b0741d8590040c05800390014940064599288001080d5103c2c00740a074007498840d001082030404d5400d81d00d40d580c84040302c201c1d8510f01002907080c1841000c50131001c5c400325505d6079101400500301e03100175030303140398a00e012100304084d80d00007034012584030404680c0700d084d90301440c180c85140080300c0180d55000d4080341d440c02e0174882d503004a5502c0c03001c198200e212000801d003080602840521958010070550111440074040310505a02c0c40203203c05840e043c4105581e489644c54051098180340f240943c44520a081c018808002c0c540c2c400320030b210b08084d841441d007800040a541c0450b540001c2c00b0300108a4403540b2551410724400c0c450b150074001d28806241955428000b59120f510b4101e00b126401c143c841c4042107100c1e101c04009a07030040942d40702d0b2175a444e0080 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 337696178 1250 337694928 337694933
    0x31090c03030914090433020a03050f0f0714070b090106031401091505040309030203150406140c07060b03033f0f0703020d090803070c050705010503091e011512 70
    0x20200e5a40009814809104020300241d4600c030300b00d6040b58000d41c44052586d1000d52101010b8140c00c03074a44110301c480d64482c0c0001c0658083c2080b00d4498600744003a0b0307180c0d50a102c00010031200c4c94480c15018011400c13051140c000d80700015403201080c0c0c5404039544030040b420000301d40700c0354103039100c0b0418410044036403084244075480d18001e000801d03403075407940b0b17035540e4010492000b540c0e00c0380014140b40c4154200c3c001180c020302600e0003d4060003d07800c0342c0f6022641503840074201080010300d5141217171144d01c2242c600d0910340c140b0505a4034000501088800980d26200a2200d00640300410744401500d070604280d05880e9582c1c1e00c1107014680c5282034041d110745020702002410350f804038400ea1300106511300141ea411580038010014030851a000c0c21a400c04801c100d1800e81041489030054051404c07510000e980310300446140c80102d4804003a034000907400030020103040310080b40701c40d0040c004180c0c0303481300b10503110f040082d9025801007100310016905 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 337697428 1250 337696178 337696187
    0x4140a0b03030a0c06051b1b06160e060307030603080c030c06060604050f100201020c070b1b0703031b02030708030307050a080703090b0103080a170a02042331090c0303 74
    0x44094103070040d5060103d0100007a02d00442624060101500c1e5000201d035a4001c03030441c00040c90280099443d40002070740e01a40c0001c007980480e8920441c0c0114042c20700503c2c000800c8906566400060b800e041c0602c000c580020300088203143c1c65400110005020300c0c040d118803201c1c40011070b10f4500044007103142900c0505154090401044184900d484a03204407405c030406a49142c100f08419038100d00a214004000c4800d0003a0f42d000300e50b01016200030802072845040310412440089107507501c4407010f02c801004108030007140740052000068541c50b80340001c050303490107071b43c40c1c1549080d82c0c001c4695400080303001545010880e00100003982003d100c1c070b0108800d02c0c040c7c1d908144600c0600000c4c03c07a000c046814003120340310314800c85601925854092140c1407412100d40a90801d0294050043d01c0700f10310503800d40c2044c0d1070607018100411071103c00c9030320010a103410b1f00c000031910303083d0984030b20055429418001c034100d05200e1607401300d8075482e5040090 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 337698678 1250 337697428 337697441
    0xc031005060a170706030b01020f030d0b10020619051519051906080403051c09050601050411091302090d1b03150c0f0806010905100908120702030a0f060b04140a 71
    0x7020b03c00c0300c0021040050008200c01a600d00e4100050780514040c0103030f180081614100071148030010740742201e000700740c10509e520320f0300359210401101e024009076280c100480e0107122a80101c0c0c4840041d01c242d400140d003154038101c00f00e00c180c0e018000f14403007100041c811241d80c032107404204264145031590080b60003461000d140410f00740f80e4001c1c01940050006000c005020035110f040d441000394004004211003800c00c0f1402d013a01d09503840380c60034880c00f03101d01e103484580905c1b404c69034102c66641c4402001c6441200300d00291000035000b020b809134000c00820b1500001441c03c03444014960b071a144591241c624520b0f21421008010482011603030a0a60407401550018510070b01c4500c0c82c104084130b036480e18012108500180d2103c0d50000b092481000d409070410918000d95104a05481500c0c0d508411013080b8414008000d40590001c0d00c5c41010034482d2410911203449101c3c0840c544900c10b001805580d80881d01100d81082c0b1800e00000680501c03602 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 337699928 1250 337698678 337698689
    0x10909090305030612070b030109090c051e030607023d0e061807060807051c060617060901030203150c0904020a0f0f031103011203020a02100203040303090b030105060712020c031005060a 82
    0x7045481d00341f143c4140180010700c00c1040c0e05460b2241c0303e0401100c005c465028010107080820302c0440800a0200c403100c110016009010750360110303054500c00300e00288103c420001c00e4854408241d018801581420400304c0450403000c0c0c5031044500c0e5001d0701001801c0c01c03001306000d09040c0804a09403842d030506a8403503020b42000c022054000098603030240d01820016110010940d1386c507400205c402c42101c00e1481d0140125040f900300c00440d030b4905003848000702d035566000c184101d241083c000a54140e0004090001c011642d8050aa0051150701c519080c0300010000c02d0590304041034141c00305400304c080b040e010354024030201040c0620f10b4107012604524070b601c52144818050060003d40d1010341600b414002c00c1202c440e0750307010f815080c98034150b1100a450b5001404203d00040000f040003074540030009c15a0b0585400400d80f901c3c2003035594442180c0c002c440c0030081540240b1074031101c11342e018410048047c0d660400403c051400d041041030508058005 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 337701178 1250 337699928 337699933
    0x62104050604021807090902030903070b090303011403010905070512100e06060909060f1b04120c0f060906080a0203150607060e01110705030f0d20070c140f0f010909090305030612 79
    0x800070500c6d0300a0346002114504000180d9985506922909500c5002c0c40580b42004410a00c0345151000005504035010041e80c034403100617000825098400c0040042c3c059407140e003090005151610094402c2c1108030120342ca41110001c81d00c5c240d8000d842d0003482608100104040c508181050075485024034026008a242c03c80c1a59107003031025156000ca810f18144290b04113820788110350192800d00c0301340b8034504d03940c075001003528802d000302030604419040000e40345000f1510300040d00c04079104e00b017059440c2e1b14148001c0d00020b200a00d499650760310030b001500d561008200d154010304010030302070480c0c094107003550380a5100701c4007090204500000b0600120a480e0501d00e80da403402e9950003803082a8001c0c156502c3d031000d85010282c0704012940c400001006158480c507583c490340c43e40d50307070002c031034410141c0100c0d00f2030368459190b56540740c603600c10340c031520050401030411b80d2511150030440b8030300349085011880000500c41a0f1600c1000c291101c03003070000 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 337702428 1250 337701178 337701181
    0x1d10050117040821160305130b040204060e040803040c06020601060905010503100b16030806010804020109050f030a05030a050c0c090402150315060f07030e1e0621040506040218 78
    0xd201c0407a00e851006030301800c0e0042010016a001122500c00100c0d4090745003c40110318440c5900094540381d00c2c00c2c081000f1660128000c0c01400c3c46860003041c0c095480c150b40e00c079040d99101c0184101d03803003a0f46404c01f090b46040020604d02407400360031780986070310b814640309851160b2500244199400000101b0003954040c0d100707401e40d0800e03c3d01c0358607900c6100148080d8400d940000801d01c40c04500001c080b04001490b584c014001e076203c1f0031644038180151030410081e2000b90018422141c244542d0034200300c00144000c0c083c0c122030314146a5240c050458000080f044c002070000922444415010001040c60b07007401c031641030785030034140d0005100600750310b907080d0440301c0840083c01407603c0801072460480013921040d900c042080c0300b13041c10782c0305e0081100460150f002c0d003182ca007082c120b038400c484940441d06d07000100c0c03d403c000980c2c10280f140320f2031185d41541c465a841d02110b425000c0da00c03450041c9244d041034410402101702d00d2505220070391a000 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 337703678 1250 337702428 337702439
    0x1b0222180b15010c0b04030507051b090a091e0308150306010806130c0e0423030304020a05131e060311010c080a0f110a260c061617011d10 61
    0x91481e800050040b540703651001c0001c0141c0d01c00c1d850500140210b11307002c00300010f05810100070000c0a204e58141c80030401040c9500720242c1440d10300d2608100b040c1c1c002245070006500640000380600350100b00075604000d501d56044600e541107000808000500a6001940c50040f0202c407086001c1d08480d81403041c40b07a601d50000b001101508108a038803000d21000c00d00913005000380040c110340f24502410310744100e840403040001c254440060440345204080143c81c0681d42c01080c24040c01c0c0f40200b00590644054008200c1c55900d20402e0380c0150303d441c02001c2080410b10208a0a1550429105401c409014603050001c030700c040e60f0020304010103d881003c03060401c40703e04600b0617001c032200c00000003c0e003443c1c030a40302c00e0014401c509101010f5403800d14800d40100c07043d80000c0560340210101c140c142c2d0320050100304040303404030482000c6009450030381605a6608005602c114080c1d10110181da910707926448110b01d03544800d035101070f01004100101c2d1409 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 337704928 1250 337703678 337703693
    0x50a06020f0c090c04050d11100c0b04020108190f090605090307031202030702030f0d0209120c01090b0d021603120b01140406050a0e03060a0c020601241b022218 71
    0x2000c1682c4240f95500009960b0350340c080907100a0203014200d2807407070f1441d10789401d1042e103150056109404200ea00e09020344200d2207610741550151400117580c4881e40150383c4034002405880454101c508080e8400c98284181c1d910b000344140007040c40c03001802d20340201c820261808031250400c00000012a0708187c4038001115002c42c0142d9981d280213049085028401d048038080c6000105a01ca917601a0080c11042400b100d002c0f03c05030380449556902d107460075100c0e000c1429240c08010b000d0084010f0300036010b06500140c64003464290804d040b81a40c4421000700d40503d40c1c01d0100b800c0b5210700c44800c80c0c20700300390409011070115561980518415070007005400105100c210b4400c1c2a84c1070605006021103982c2e0510b08080380142a40c45030840044c49001d000295900507220044207410000c0a014a20300351144211440b006144500f075640a8290070800161a01804400000580d210101800c610007010703c0c180c0e449520a000d14003010b00c1c0d440d022071040d = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 337706178 1250 337704928 337704943
    0x905040c02030d140f040f05030c070f050909012a02011d0703050f1f02030408120117010e0a0f060908040e0103030e0406050f01020705040f0b061204210e010806010324050a06020f 79
    0x3100748244140c1d01e00503185200b5505650354a00074090f0009180c14cc08941d042964000c5800440540e14040d0300c83c04c03261543c44e40400402d603403011080708841551180003508442c400400c018814141c2401e19105850a2002c00d42c40f0b0326080003800414000401a95000c20180c1000c041703880741203080e880120b40c00c6039900c1d80080401c040100f01c4080701c40b203120502c015a040d60307403424142000d10904c0c4501d02d4650808603001c1c8a42408034107000c03550b40c0709040241004058840800502c81003001b00c07880b0074108808220306940002c8540214401d0340c80c045e5144082e814007065070b600d540414058000301d5880c00d402e030b801040000549800390b90006500e50743e0000d220241c600d29400e0303600448002611061240d070412514441c034050b03109581148401460303416401c8900c801e2000190070a41c80854641c4950082a0821030524002c40d02d41403100d02884124080307005490f400324000350800c510709000d41041c0007070010740082c007204400c425190b51103242 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 337707428 1250 337706178 337706183
    0x1101110304171e070f0320030109060b030705010e06030a11120a0b1f0807031a040608031305062b091e0b0106050f0a0509060403061404060509010b010c02100905040c02030d140f04 79
    0x7880c07071070787c1d500c800c2c0c4c0141c8000302c071401402409440804c0c00c140008011851101d402030041c3c050104581d4060880b8030b03100c1c0b001801407440d50b038400f50307900700502d1450400542c0810401400304004519200580920104040000d80140b06001c02003040d0740c1a80c1d10080c94071905040c44240d800550227940801e0b5400d02080100034102d003a0007588503021000e6215241600c0401c144000002409801082241242c20b1075210301c2000600d000d4107014a20261507130042202202100140441c455415100413894587c3c2d81c1c1c40a9a40243c031101d10711a42c481d008030814040b080c0036850040080c2c0c10302c02d15119207074450321518403e20300c40c40280580041c1e5000c1c00d072101d2044070000c54019404004400d004000342c402d450054034152900c030b04140114869400621444034100350584420003500500da0034080e05516a086074001e02004100c0060103445900941000f1002940903503901ca0146401d5011107030131201e50a0050502401c00c448a4031207860181c2107074 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 337708678 1250 337707428 337707443
    0x102405030a0b0a06030e01151a07030c020901170c0f0325150302041701110307030b0409050a06020901120e0703080c100204080105060a121101110304171e070f03 71
    0x1500c1c0207001001d42030b1800c04540210000d0b00001d42c00b0fa255004828011045009110082e034600660011042d10702640d4144120f859101400709400c2c1b0007010440e110303040c0169818050b03000030710a1072003613226141d000c404080390044407206000c50030f06842c080b030ba01c8071b4400019005c03958038a00140e000040703441013420303a00c1030814940d4000c000d020050008041410045d0004c003c0d40140c810b103070954031130005c403020018043c0154070303240c61034520b514210740e80c40108801a05003000c0894020355625140300c0442c60900c20240c080740198400340c0c0d164041c000040c03501136028011421903140c510311070000c5801140700d404a94006407499190406042c2c0e8a081213007800086180600c0014009a03600d0190403042c0315110450304103036856a15003080440300e44e640c0300141b4205223480c12000a6000f00c1058495803290801c40c0d00702903c84605011b0080003042445e450f41c00003091520249400041040c041b4031540542030292510310044682d03406404020b0451 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 337709928 1250 337708678 337708681
    0x51201053109050604060e060705030103150209010e130905070512061611030a0e0a0b030c030601080703180b0402090109020702060a050c01201e040609030f111810240503 75
    0x11090b004001403d0b0003000b55501030802d807910394020540c500028040380102400504958003030001d80e41265001340e1071106c044c03a185402c0009522803100241400000302600b005515460203148840c00a03040000340020075007091840c1140c268002d610031b0586144520015401150341508a44100500d8414030079126050355910340310414205e1a200111b5090100f552128040d94060400d642001c80d084e10f0f01600c4411b48801c44181c000ba00013040465419403250000300d51000142c6000100e80050746074420041c2280030068414000c410140300941c50000c14131801003400301021850031941d50b010405901503900240306101c0041840c0011040070340000610407058003034038800702d01803400e440468101c0062011107402d40c011180f1039801e270100301c1e015a81c00d512500e002c14075595460302d58a0443c6402c480b0030391001002040350311140a600004802c00c0509580e601d409419608000070550002004084010901c5410103144c0c0400c50301100c649040340e601d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 337711178 1250 337709928 337710019
    0x40605060409050405070306050412030513020d030804020d080406030b120d1403040f12050d1d1e0102130b040518190506180108010c03240b070c090c05120105 70
    0x421b01d403603201400450905003000b04011560031284401e2a96403000c01c40c130b423122081c0340300034414100001e400000001142c00441d001c2c400d201c0e80325200405d020951001651558503a40203039101e000440d8842c20003100782d1401c0150000b401c00810300802504101e810010320500a0481451440100002060502c224640d1051420341c0043c40c103451014071420080c229031245410789140b40c50a200d8042c1440440140c00112540600420890a80900040240c10005100c1c0c180799401c1181d40403218410110350b0080291000d1103864500d8003050248525441070b1000a8141903030811001c1c1500484103a040e0703825100c0007035035554100101e01e601c0544446444188440000043c540605411500d4002c010b5a81488585114910b4107004140781c05626940360701d0726420710402528074054000070303000700380300400255030350319040031100307001d001800041d4005000001c072403100c0012801010165401c694440318418a10b00c0b80000c050003200382070002500601 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 337712428 1250 337711178 337711183
    0x5030711070e060a09021912150f0609080d0801060309030507140c1203040302010c02040902180f06100f0e040c11120304020907021f05091c0518040605060409050405 73
    0x12800d940201c890094403584642e0080c2400c40c1c0052040c801d469020681c800c01d4000d45a00050300e19103a00054100c0c0425a0794104110919220079541c8629002118440f040d40b80105540005c035001c00c1e0410303000900300c1606400256007a032000c0801c81c00c01d0341c0509110b04407141032400007020380700340c501100c030b40c0b1541d50040c04d1440d103501c126648a2010800b50091001101c0050485400c40c0c0d51544a00440c0305c00790100342c0044d0400050b0400350000b1120910013844030b1020044441d0005c00601c090303850a003822168070401c2002e007840043c1c10074910042c10905032442a843c4000c1c542400d0045240c06180c9940c030b41006c090103951420307407aa200200341c4104d401c0e01e05820f0038603001214180d101d00040d002041d1303450300110300720101c100030200c41e125110042100a014010150503140b407403103408400340e203c1c0030029506540040c2070b17981a13940c440c682680c1440d0751b41403101c94882ca141030300c1000a541c07402c00320750846500d040d002c00c0595460414a0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 337713678 1250 337712428 337712447
    0x20d080a030f0e0d09030303090204020409050f070e04050f151201050c0a17131e0c150e03010b0a0512030d0213050a060302031003020f2e030b03060402030d050307 72
    0x20050180400d400c0030807a01908590750340c41c0030140070000c01030140c07140d0b40c2d40c034082251000440c4800500388040f034400d40000c11400d0028201602d072075900c1e8a6981112812564140302c20305090a0107400703035000d165100c510404803810712060900302d91303058600d00c015203044184004520f400b0700780d881d0441d200341c01c41d4440b00200020301d8140074005950f48500704000014044060340c2070b00741ca000302040c1c010b0162041c1400c1c031380b0315503586141c1d0454000300c0304040c0c4040007400c00001d038014540009800102400d4240104400c0054480424a0310340c03840b0740d05100e4203400d40c2c1c0311491400100c8404803080e10780100c00b10f550b00e09601c80d0030004441140001005000c03281e4900c600303c00c80e042940c4008e182603907424224101d02050300c803400c00305400d08042000d803914200c3d107500c10303100a007403505441d0300b014101c030a00d071803003a40d10803200e03c100c118890a0f01031146001e12801036010704482d1500760b001075250301c1411508400e0000c0840424010381c07013454400c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 337714928 1250 337713678 337713683
    0x50c030d1430010e1009090506061002070f090f0f0504051216020315060901320103140a0605040e010e1e120301030506040b0a060501021b010e06070f060506010c08070f020d 76
    0x1c2e86540c6541003110004000ca42c104138070351440b5000581d102ea18460b48510342d030080060b207040e40354207081200e00340c4400140c01c00c52090b4100403801922001c048001003180c03c000013411180481c02d00d041d0703804444000881c078600000c10003c40c1c80401c0c60380102203081c07141540c9048212040c440014010f101035003500c5901001442d20b000b040d1034a02410086424611a0b0b90740c01100240c0c003980e4884500d0700c102c0300e803078095404c00190f0100c40183c050401086e07684084440c0c00846401b203900200054070381c01c08004506092007101621030411000703004944e101c400495846000143e024001001c0d10854400b03404140a1003441354180c02c0c5107556560740f07040c0030750307038800c1550b00340c03503804c998000f0500340c01941c80303004121078060b009003041041144104070284d100c0729225050041d40b0488400a5440c00000c01181d031050021168a5905080500c11500000e0510381808032007030240300800ca039070003507800c1c0e0340c0d111310802003600e22032001c56150031005800 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 337716178 1250 337714928 337715017
    0xa1d01051903090506151e0103110316031407050a050c03040504110a02190c06081513090611030f190204050603241f1101020403050703050c030d14 65
    0x74904419815005003210501500c203e6810b030f121002c40040080000000036031001c8500c0502043c500b041c1c00b801d03c03050050400088001000044e030005901c210b811032620000305c00c541c1402c43c1c26100d50403850000201031825442c00400207081440f42050501c244080424441c40b032003010403c0b2405000064018030458140308422800d40d0070008105016001e803070704088808000c403207503001294000c198001011301d0a001a01c41100c042c2980d0003c45400084800307a40b25002100c0782c00c510070000080301e6549040c54000c039400d40a003020001c400b0814001d182c01d146992701e4000303261341d04400d031701806400a04028803036944815041400402000b00c071110440201030034540c20391800c5550b40e250002c2019298007500000e03402409207890903c003500c140d0030704440341c10302400189419220b0300c2e924039007050384c2d000715200c0d40305d0310f504815800d0a00c140003154402e41840d64814094270102512400343d10040b1029001150182c00281160400640c0c0c0007043c010 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 337717428 1250 337716178 337716217
    0x21902061606021b060603100905011b020d020706050f091009120b0a0507210e07030c081b01080106170705071b090b010e0303070b100503060f0108060a020a1d0105 72
    0xb00b58001e900581031400f204040500e030441500000702d415031050130000c0141c0465984890b03040020704100500341e459640c1e900481141d081130211040c502e010700c0d00101104501a90002d20f40200f58002000700842400690040384c0428165180114222100340440c550b010f004c9450464561041042c0000540f8840a100000045502501d0141c500380255a81c2d600199a5504c0e40c0d03d201400604a0303c04042248041d40070401c0ca8110300c1c280e8604607a00e80780c2c001e19a00c960040003c507002040000c40580d2021407010040c00c0a0030500003d43c507003900584050803a8140042c144c80800005443c3c0f8403c8003114000c1e80e219a40ba00041002d100308004a0307080d0190b6150a4a44907403281950b028800340b803030b1454010000c51500c0d000343d4544c0200b07071000c0e198074092001d40001081c941d8040c0401c034800e84a42c06050203541c507000005242c88030192404101620402002c1c4209c0d0384400c2017030781c401c0f218415000030350b00701d40100c0e154441e180118540f0854142e = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 337718678 1250 337717428 337717433
    0x30207080301061e030509030307030f0e010606020c242704020307020d03110f0405130e0d02060421141b030c0a03121116080921150103030219020616 66
    0x300b51064985a45090342c150404c000019800c03513a06540b0540d40c0ea2040c000650900e100e504012400696039130701140c60304d80c40c869182502d0729600020301603006039034540343c682803001e140c0c0301d062074000190010800b40f190828440c814500d40c503030307800540d0060048203154130051551503080540b0440d940c1c40c00ad40020b40301c100700403090340040c0c02c100d04403d04214080c141c40212401455880c03809160000b00185043c915800c480718a0700c541e04680c0039041401610080701c511b40160000f1714240c58000210324107003682c000012002c0204880b05a031022603125040b24508400707030740c2c0c804413158500b9410503141080c11b61000081c0000000408207074000c9240c0300b074075081140b06200f100030b02543c44a4079070800844d03050107240d4400240c0c031039440d80c0d540103110461401d11000c010400100304003000d00b09440f92071170030000c0d40381e0410600450b04101c80303004190354107568009441e01040404a040c2c085001140c03415551181c0c115007069454103a5a0003d49403072 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 337719928 1250 337718678 337718687
    0x70b0406140106051b060c040b0c151005092401080612060103060c020c0a05150f161a0916030611040909051c05040806010e040f06050709180c140a03020708030106 72
    0x2201c1791192611910340d078005500c0000f540740c0038507000b8240e9401d041c00c011010140360000020301419110300350300d08051040c5c00702c5c0c0c079001b000d00747e0020322443d041c007041c0451140081d00120b108107200002030041390002200c40ca00c07040900c1d01c80041d4032000009090301200c28590421809108000003c004003640a03404e089441d400707491610b001007080101c405c4a5110301d5030400c03400740c088503194030700e10005c1044011030000d840c102402e0503002000c0b82c5440c4000c4aa050300155140b414200b401d9413a6846248840146040c00e801000e8401c44040303440010109612070072030030088105042510082c2c90a0901000003080d981041a9034690342d030300b0b6800c5002c4000811004500c56000c44c3c065490910080c51182d10f841e01045c125100248240c4130b5210902d25100060198000e040c0a20b180b540c5020b03a19082c04108500d9001034102c0080f40d9141904511203e03801421110f402041075440c80d44403044e504054000c0d201c1d034200100849000400071543c10b400 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 337721178 1250 337719928 337719937
    0x40603230f090106050f130917041d06041a10050904020a090e1f0311010207090c0e21070b0304150507020d09050301052205070b0315040e12070b040614010605 70
    0x400013070218656500c18440001d802c1d80b015600a0700032000d41207407200c0c64221607a4144108c11030340003202c000c41c0c1c0b1002504140c0015980c2000044823289140101d034469130014003c841c100100b68034100200b100d08018202a402103c0d61014521528020340c107940c4950300c090019550303012041002401e03500c440c001c50060000b050b02041d8100007103920f0003184851030388200407090454694410402454500d141144250036010400c18403e001e40c0072404035944a2240d00d8581c2420000c1030111204078004505001800b0002c070750000444200302c41118144603600c2c4c0799814500c081c40c0851020501c13450401e000d00100507800a814200072405075558495561924105826600141d0702034000d41d4901c0268081550140c004403010b9200344201d40c000d503902c090070501da03002151171a4450100400d008070358102402620030f44a091005854031554440c0c030700341240180100070308200700c107000003410814a41e10807102421000780c01a0250f95415008006a00 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 337722428 1250 337721178 337721191
    0xa0c020a0f0f0816060503040b0a0915050108060906070f0c0c09140618040f1709041a120a0209070c020a030602030a0c110a0b040b0606070c0e010302180c040603230f 73
    0x1030043d07101c2c000851048800950700c086d6241442c54071191140120341d071000c0c000d0303014199500151f00009501c41c001c1b04903d03070308003000f0a04ad0300d040200e50901000410b00c5090390401400c00031001c3d401802c0380d900c48441d0611815041c0c46051080e40700106030000c0504601c0c2403c100c480c22640f1440768030814003103c0c01d40c0c1d0180c1281c0f00e0800d40e40300340c4006154080c0d081034900010303e0844051125085021541c0c1441604000a07064485115140032030400c1c48040c0342c5641044503540541005210080500525a6011680480740200301408001c00401110215503c035510315004640100c410764403800d065003078000805401080002041c2c0614644901820105003a214980c0040c2040342d680c1e070b141c03901200b105000304a01d5000c14100b240d400051580c0022230003800700408407034655815031041c44804240729860144017000b40003000168034445041300c090310064600404c12450344a40d240c0c030320907007001500ea07c40c071b2036041110b160302c1c90b00c41620507030 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 337723678 1250 337722428 337722433
    0x12010e070b030a0212040c0e06010c080306220912090b0715020306040b06040807050a050d0f0f060b060703090e0912030714090406080102090a050405150d080c06070c260a0c020a0f0f08 81
    0x2c480e27000542c0e040004c182e0040403002d06000007102c2e45810002c170583c80d48214050015644a071003050110f4543c2c2c0c40484034180250450900c0541c00203400d07025110f40002039141820310b4540501200e42c00300301c14a416000000a481610303140c101c515804030281546844a4890b4040343c1c96046501500d801010304100004441c0350860131002d0060704100b040184140a8a4580c506850500140c800307680b542112402a12490010422a4003a0fa226001d082c00c28071010504840582203904a0f4007030315403074020602410403680c00040c40c5c203302180c0b02070f60300c1007503040c001c550340c10b540301e850640c00280c0c4120640040861b80e000f111440e08030354480e010402100e900b0396212903c9004808000040c0c1410b01c40c00110a006141e1346007450088404249014800c88522000500c0700038004100040054800c10700d2918074100020b0b280c2040e040d0302da50103000b80c000c0402412004902c20b5440c0e001065000d44030b040c145540c8144c03101908112158a840b0707003120b51 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 337724928 1250 337723678 337723681
    0x10e01080c0d030e0409050a140d0909020c0624060301090b0405100303050d1107050316150e060601200f1b01030b090622090f0212010e070b030a0212040c0e 69
    0x145058203003150b10550603203c80d00305030540410700008091000d000c4915100c1d0f510784c8400f00709950191000c005242009000c066200c641c020255031060344a01059070050250759403a000c089412640605106805102d6011a1601003600705403000f006820240000011600030b401d80c10648043d80160340a01c41ca07280c000c05025030980e00c1c80041d0000308280020004020319821180d1a10780f40c0c0600342c1016055210281180d00c003081c02c00c9042e120204900c1004003d2004058007403000400308400d40320b4514040d201e40b40200900e040000b48165640d40d00b05031030b4082c00d4403640380111901b407285450b0081d940c4000f0340440b0001c4a041c400440103610a01070421207042c050041c1c4000c0d100c2800384664408503016018041041c028400c80d00c805a1041c48040d5000d1284240030708558010300001e603419803101c00f001d034101007001150810006e080700495001c0b507074030b969903910900703204000d0003049200c02240005078240400e1000720425502a9a913041c80807545 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 337726178 1250 337724928 337724953
    0x330103050711070b030907050a0801050a1d0d050307050f0d091e080f090f0303070c091d0d0e040f0c120c020d0c030e04060e0f0406050709061d0a030b010e0108 70
    0x310114a01d9520b031035108401c00d1003a038003040c01030b54210600300200ca00060303d540c001240d0300c0507134200000c141e6444081107005101030040c540d83e80c07110003025240d215103d00c2c868865000e100d40805010001010854591142e422600b5001a070030000c3d0312441d1340070303141c0080c280441c4140c88014030305403040721008940000c080c2d480d50080f140391609550300c28200ca82d800c003400195100d12007290b040481e0301c00388028040540305100d400c0302a800c00d00c8090454007445100440c1d07040c007504905d08400c000a038040c811a207401c101c50380d02c41c80c80c00a0050070b001403e079007000c2d0034509003500740742c0c020550201c5900c4183c3c0030b10281480440c22603449021242d000001171b001251700f000300340186085185950050404203181c0c0d1901c0c06051101c005842406200303092408101c14411503109054224020385003400342c1c5880d2440080030303500b01c43c9a01980030800c42460115607202d0500d00011075004110010643e515490400300c92024400d03d580c60041111f070100 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 337727428 1250 337726178 337726187
    0x504050408070614130b0408040b03070f23041215020d0915090f020d050f030406050a030e061006110a1203020a0914061c021c02130503070b030a02033301030507 71
    0x1c294807072017081e4103c0300d01c0c4d11441c0039042c025000ba42d54910400c00840ea02d41845c0c0110706ca42095103030b008110807407078401800d0401140619806c0307156490f0324814200501c04541c100c0d08a92400300e803001d454100245203480307241d51104810320004500e0625030316a044038000c00e0140c1a160214406072020400b55810341c0401071030031148440c031100500d0140020300842e400f5404540e40d46801c0da075020320315402074201c00c02003040420780c508800e074036000300318190b802d05020706803038106000020350304c149034000c000c10b000580c1c1c1c1540c6402c10401c088011035820242130801640100e20190003588030080c0300b0000f401c014070200396140300c1d00c9070006451014000702d20300380c5103081000030f0100321215690150340030001b644070070a0308444036021030030814006966500c04070303045401852980c0300e02c1c042e401c410003c100c000300000903a580200840f00c00341e92540d4036814817107900b81c0a1600c88015003515901442880c94562441c1428000e132020440c41d10f40c4001a203 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 337728678 1250 337727428 337727431
    0x191a04060e0f010909030c0b280c020d1d0307140a05030307050a0303020901110f060609090c011215031203020c0d080103020f241b070b09150906040504050408070614 73
    0x3020751030200c0104600c0070150b01175200d070b034044d15040e03605502650783c8104541040d102d06001001801014500c0e040170100d0001100700020100300c0d000401d0f034080e448070780700c8020380240322202400c1070452401846072007041c10f00805882610391034000c00204600c58104050280d0b01e6414007040c0c90030000120390806410500a0880c115560340c1100030394040848541008100356030110101010080b4501c0c50310648c011780024a42001484a00c40c0001c0011100d42e001204041c55a40c0061115104500122000c101d501d0303800750a0301c0c45444c80d84010702c000c0c99010b034070003040d03496130240030600360020940300801c070300034030031521410700b0b000203540f09000c68284513003450300f008101c00300311100b88507228003242c94604401035040702c25694a003840d0850381d1400351106210240c0076002c2000f802e800c0c4100311000c02c9107a24221030440e01741600080540300c0e55241d1703054600415005009001c1d40c541850b086100f0313080207904951183c280402e84800055114130b45 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 337729928 1250 337728678 337728691
    0xe1303020307120509090406050612061e09160806041103030906030c1c020f090f0a0e0f07020c0d151503170d060b0f03011508091203191a04060e 64
    0x40d82003607515200e07102030031000f02e445402d01c4001c116280d06501d42c0746a4a200390f00603000000d8a00c0c000302440210101c507a040c4110350011020004281702001c0900101054000b030300c0019034404000c2c3e850002000030f070310b118000b0304030000b0703120300c000403080d100b6841071000004440f144000d1569038041d001001d070340001d05200040942140d0b03006010318030754042c15241e140c4a501d8950040768010905106202000184582582060300500c003121505590315a071441c03900a02e0034500b5000f5182c0340780b0b290510045900580b080120340c4004400a00c8030802910030f00e03000c03a04104520b0032016003400c0c4580c1e0707044a09c646e010441102d80090a0380412031142521000d20b0b808003998030542a034500c2e003c205081c0080103001d41c03100510840c1e903254101000c804150030220030000c00c1080c1c2c41d08010b191680807030384c110b0554607030440d244c980d111903102c4184072140310500c00c95a4504040000d00b5400c2c140f0304400e48400303440c10821982c0b00c58a694003094219a00c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 337731178 1250 337729928 337729933
    0x20f03040305150903090a06180e060d0609020d1202060f2401050c010e070905040218090a060506120d0c0b06010207062109020a08010b0f04140402100203091503010e130302 76
    0x15000f15005000120350f101c0100c90540389440c0e1104001420340302241c1100000541403030120041408100d015400342c485003007215041e14103c1e00040c5d50310076140006240d1500e80d081041151200403003403100c66030003202c450707180b900103c0007035548800b102e04980c10040b8101041031045a40744004662203a075000d512003000d20f1006403202e030321400b4400025076a8595181403141d0902c031000240103042d80c0480da904080c0100520b0260488000b810000c0da01c0c18003c042e540020b242004d036030300241c041501d642e100300240001a200d480404c4034056040340710f101346d0380200c860320824841c503002c61040e1509001240d03228024001c400202d0f170032405070180c40c54030003140009213022032800310718a1402e0380440c2020000350700003691030391108400c030003610344022510001d042c2034608220b9000400c4c01d80e003c6c0500504007a005906204a00016a00c01d008850182e040984407004641a801d011705d1f01c0e5009203c0c0d03904403804500424296000304400c0d8140e550190300 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 337732428 1250 337731178 337731193
    0x7080919020a090204080a021206070c2603040506040201020d030b011b0c27140c12060a0e150901080c101215170c012d0507050312040201020f03040305 67
    0x680862044101003070b81e000010060004025500d0300080c4060b2000001400405c0d0071031050020500e20869000440e0300300380c040103181940650741e0103880e9005040e50b82c0c035140c1242400360b10420141000307601e14000082200f40000040c80a00461007079080360728502c81a2000c8044842c0071000a000491305600c2f0740c900082003003002c0c0700340d001d035000010b4165180105c0c03076801b41e8075154212280500d032202240c00744a110b112310840301c40d0f005000d2441c2a00b10119203200344042000031846020110380980c85200b48940900b24007440384001382008140512181480c2d1000c0348592226800030929507404952050a140050640c140850903a441503070100c003101c48651200b5650b6122051083c1c080c4c006400904860b020500c014180000480c01c1505041c1e48a06001c0603900d0961000c0c4e060032a038011409000c191100d0f8504403008403458410014041d009110100f5141c0320030100080d0307940183d02c01d8003210b1151849030860354882c0a070707120190039608482c0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 337733678 1250 337732428 337732453
    0x7050306100e0d0c1511030a031805010c03050a110c0604020607020d0803040803040309090b010c0b0615071a010509040521160c08060a06050a1206111908070809 71
    0x19080002446814802c201602e14404204100803001050b40d0b100d1619804015002d000c04d8020a80c0d201d03132420780c4030000b2182d800d594a03c6135500000c20036555840300e45000e8120881062211750020007031080c80070b200002006081d040d145144604c0ca841300301358126400c1c4044586440014015244550702ea8080102c075801035001680c00400d5a00b04d1000501104c00840c0f00e284500b42440d103e041c281402015804e440d042084040d00d09001e000560f80c01c401a48860741e400440c80c2019a20314021940d500314254214200d0400815031030704100c0c1c9280722000701101480d80340583c1c1c1e80d5104101c42414265409081504610341c1c02c001c2421100e0503100c1c011071400c0b07241c078240006030021080743e1610020360340218000d8040c00b50000911150717404c803004640070700805052200003902ca1055102e8010140f00c0c0440040402806400c80c888088003021069125504040d0346003841700c110b8140d100040c0c0384800940c0103401101c20a0080b8000001030900e4804076 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 337734928 1250 337733678 337733689
    0x604050402040b13020a08060405041509030905030f1c0305010f0905060d0803070305090f0d120e1c09150c08120a0e010c030e0c060301082a0604030c0303080f07050306 74
    0x10304281c0c0c120303440d400d82d86000e490f0341400c55510b040d240d00040c0e41c2c0b8038502d070042204502406091040341031209000200e4581004100c0302a0000b1001402c520289016100d02d82c55a11807a054001c0c0310b00c41d07444400101c0e9518903100e83c058404000c0755545030440c11680240a40300d0a0050400140a001d0aa40c09503602c1a405170013508442c40d00d417a6061f0b10740089501400094a52041008550090000010203041c0500030f040c02d1481140140c1034103d440464048156a0f007140300624008008101c04818018000b9035130030b0b05114014219061405010700450a4000096102d4807414078101410703000f500c11420002904d451101c82d0a000c7c01d040b64240d00d641130107000c06800c1c41114803445160301d0004111000440c8030b0f0520754901810f5101e40000d02c0100020304000c03039a511802e021511880305000700d0320041d8440c03442d005040b40c0064000c180403040081c0d0001c100c064038003903200c0e040d0503a43d04c039914070400401c48542c0002081800400c0701410403 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 337736178 1250 337734928 337734931
    0xf12070b2a070c0509040b0603100b06090d0c05150a02070e070e0402090103020d1410080309030d0c14120310120213020307230304110a060e0f150c100b0a0608060405 73
    0x2910f40d1100caa41e1400058511401030314260741c81e030204001d0003801d203010001a0316010104505011458080d000110a030080041190164451644c0d15007001100b6044c00e024100092442d600a08130b00800c82ca02d80080e0003480c0540308007600415180d5031074080314852841507441c0d465200040c4203000107034201c03000481c10b1680038450b840034201e49008501c1394404110b19000d03d440c00c01400015000c99900c00710f00b0740c00070000103403640c402140d104007280260074028170580292034200c0c081c520020340d81a041c020400b4420720008507400450095015403800c8209a0f128820718102c020000c000a6008150281c4e001541c982a0003442d8040014100342c140c2200800d40f20b4110720a000e00d90000540000c20003003080880900403160130710982e0112215400c0480c050314101c070400445104900300b0110707080559034401c602040703010011600d900c803016420b0300c2d0342c1e61207030191600b001030520f0052a200e00340600c02108481c2c60399034480c8507458000074030004100 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 337737428 1250 337736178 337736183
    0x51606081003200607060b040b04020a090e06030c030a0c03020f1827120319050903120a020f04080c09012c090304030c030f030e0f090403030e0f12070b2a07 69
    0x8841d04541e44c1d100006441094090100400c1d2114000704010807200c200140710b101e00c1c030500501150a40c0030071900d050712881c000c07030710003030720f0719000a03180c1000045800d41c1842091083c50800c8950340081c02140d1003039403515078101200c0108400d040103440159190141200041c0c405000d01580c083c0e40c001340c1844d000c3c540da40e02541810804810701200d101007000060182f50310300211405400440d407841002281099040c3c180c40c0d128059442003914a2100450345900c8075034103c40e07140703a00ea16410b54541c0da03a1019030b00c81e42414509803040e44176000018040a4050340d0301e402186403031700c84a09150017000111781400260101d0a03d1005010100c000f07505012003c0145006d110001da200b45c4914000340985138208909004074048281100b4907118260581d80165040c2000300b400c5410a041900d05100e00343e1a8610344621154040c0c8000703020000c2207030358052200d510a40e50b8000d82c4100c8540800a0580b455246a030401c00b5600c160015018191 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 337738678 1250 337737428 337737473
    0xb0711060a090e2e120b04030201020d0513022e0c030c0b0108070e100e070e0402120f1602010213030b0606070b1612091703060f0a03051606081003 65
    0x3602c507800340b01d070b1490407181588640b00c2e414804d40b12110074a004041000750761020341d252418103901c0410340b101c602000380303401214800300f000c1600070b4054071003442065804100c5407030101d81080c070036101000203900403096201010568008170540088040013418400403041ca040c01c225020740760301405904001248054030002024060303258000c01c4140001c044060901140d0f950031400a09031084d40e406581d02004081643e91001d80e001d652810018888042440490041d106614060b054000d241c82000b40e04100a00414050445002c10030b003139114000b002c2e400c170300c5003800b005140c40c22800104002914035403d00e620000140c0aa4200005079403641520360301039410007581d141036a1b10003146a80924000001141c0510a101c4846c141c3c44850a542503041c00380c100200000000300140c444042c01501090042c1400c0c840759503905046403180803060350506224010000086e91b2032042150364001d00741d80510020680c82c1d0355a5001d2000011644407000 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 337739928 1250 337738678 337738697
    0xe0a030210110102030f040204060f08120a140d0f0609020903060f0a15030506151e0405040c0b07081806090102030f03041e03020c0301060b03011401030902060c03031e010b0711060a 80
    0x101c0c0030300245010342e0b0810201c0c071b80c60070b0600c100030035244a504030b03d9043c40101020050300c680041c079036087c041c0c1443c2059070748052174030845985c08200d42d0040326650000d2000c0790301100b64800a503c116119040000c140c46400e10004da214030f229581e0315034003074070101d405103541d10040360700300f02c05080c00078500c0301500201c80d0011807640b050360142c0200040003260030101d000c001041c2e504461102142844000342c010030a003000c45680142d070b880000804001c2d15030f1002001d000101c84072a2a280d0f90300e880303d0036030300c613030142c1c0c6080f030301c24001c2c11803400c00c20700f92102c0c14016000b8504010503548400c641c1d40000b8408c2c0d800c03061000c800128000c1501e0b00c5d0030103e0203540070f403250807030300000e150030345a5a511800c3c2c01001040104032054600902e00c1d9011000d00e004145901a800050414020b11550703400300d010001c04d010f6003100e00708545501140302c5085070300320fa07659031143c00c0c00c4c000c1c4ca401410405441e981001d0602d481c00007440c00d010f10782407003d40d9 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 337741178 1250 337739928 337739957
    0x1009090209042301090501120b040b070c0b16020f0109110d030513030c05040b01020601060807140c060a09022412090a0b0c0a0306050a080a02062b0b010e010e0a030210 74
    0x102010f8500345402c04100341c00500480c1040e008050140c405140154004a100e0b44e0303081c039502c402040948030214820102e0000ca101e6410000c102d508040031486a0034805000d030008507808a105001d4801c191000340024018054000002d8001c02000d540c0000706080c0138451462203401c404000c0300b0084030b0000e080515000c0c0166005100050303120703081105200456009140742410340d405600104140da900584c51307a40a030041c50030300c54a55241d001401e040c084c00000b608280901b10401070004016800704004a000312400742c803503504c4100c5154030300100201c1c03000801041140311500300d40142d01c9030b04a2240c9007210761610b0036031260410002c0a4640395241140014100c009603854024a00034103811100c0404562a25852980d50700e08004000d000304400302c0c044240091500000071214250071082c4880c8140d0810940100001224240031a40c0d40d00c2905055108084001d034851000d041192040e047d602001309606840b10f04000304101400e81020 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 337742428 1250 337741178 337741211
    0x1f05070c080304051309170a050909011d0f0408040e070e040f1a0a08071509050a060903020312040506070f020301060f120b010b030610081005090c0711100909020904 73
    0x4041e003030007464407241044204135108403c455481c00e02070030030851384049002c41d8412440f2000c1c2400b40c2c1d545200e10041078926020300d84c00664011204800040d00601d204c024140c09000303050074614582e2080502e00741014166000707840f20700140010b114486840c48180d800c0301507401c10001c880c042070002000c1c2c51101c100304082035291400120314408520259110310707800c48002c0306450034030340d485940da070302803080071100b400e40b0030440a86409101c041e4040c01010b0b046603602c40d11081d02030504d03512448103d00034456160310144050320f00099800780d45000b4461407030b180d166294000303c0801c0b0754083e0780c995a2403000240e20024481007070018a415444491800168100210004d034140c0c052500803c00308200a040e50394207191010f0040c4904000789552203e080c800d68481c0c040d0461078001094805008103840204040c1800910404040c0901d9885a0a102a019241c040000400c0e0b80e1603003442100000e4021704500300015000142e0507409000b03084 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 337743678 1250 337742428 337742453
    0x2120703050c13140f010f05090105071401090f052506050c070b03070906120c17093306030706052a06070302040314060723070f1103010b01020c1f0507 67
    0x11100c0f00c085180c14500d040290101001005c2428500ca94030614000074216104030705245041103000103840d410000107400070004198944020814002036141200405209a4094440348144250403407403208021045610b4041070b41601200c9140c4401911990003501c03041d4030300d004000c1c01290000b410b101442c41644240d0b07a5054551905101a103a03c175400718421429050200b981c85880c0c105465810400c40401da2410070b540d00300c107113400c02808011520419000032840101c8081d610b2020b10b044500b50340c13071812511440100350355884644121000324106016032043d01140f4130200d540b500701441c06202c089100740225050010071683d07d00803d034046001d10038014241350310052651800700400c0c0c07a040c0201c01602c481d0601840d08200201e02500202e2170003018291003074603a00139180d158031030441c50701202c9080c40241e130178082d610301520302c0c1c2d0707541c400500458803120242c007154041c691401400c142c04042000c48082c03120420200c000104c80c8000b02 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 337744928 1250 337743678 337743689
    0x604030303021b06071d0d11060f0c0f060601030b031606030b030a06110409050f010b0d0c0e03030d05010302040e0106060e1009080d02030406080c071104050a06051206041502120703050c13 83
    0xb40303c01010f40c6c003000f851450b513405440c060104458000005410340310843d02030007040b01d034a40c5030450403020128600c211441444140500303019a00180400a4018080c41d02600d0500c00301620100341a9110750b0300e1440c14003502c0150040000354026441400701c0c202c0901600c8010710300b03403502401e403075030105642d081500c00502000300780880d218182d0800d210980014071940b5225010440e0f0184c641011a840d42c0c1e0f5050030281400340e81140c0e51a403000c2c0035292078148000400001740800d1000b0780c000d40c1800942e1510700010320900096907030350b03154100a601490280a100409c00b40080d050024a4502084006040000c0b50749c3c616668000d6039150300b00000140011000751800108a605120910004114030702502c0d218105840005050350f40d000140050700e050783c891500494020281e00c80b4690210b21144524042e81809020084043c41e08080b81704d490141e004ca500000d0100e01c0c42c074401d4014541180110004600705025a03180c035000c5840f40c0d028 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 337746178 1250 337744928 337744937
    0x30d18090e07080c010203070b040b0901140a1e0c02030a14130e070e04060e041407050405090a030201151a0d0204090c030207060c020d0f0f1b03080405060a020304020604030303021b0607 82
    0xf0090032000f040000720802c2d00b03102650600300c0c41d9444510020001c3c02c000d0550400c0000651040e6096114904042c034004402c82d00c5c1c00e0130f41c4100c005140c404800203039034400503040c000507809401500080c44641d0b000b12b20300702c5070190481c4d40310a8154911550001040603c1d61100300112020103000c81910010703403800c0040c40a090b00401d1800306005d1410724004005100300d022042e917002d40c014400350210ba51008100b41032042c070360401a4041e10f0402031220421000413000c12807407103034008103d840312062040304c02e450148107140443c10444450172619481c2c0019103040140c0340b8000d0304240c1c80303990a1042d11500600c00700020f50210b00c031801c1c003229020350150000b490001e48800c0b10b40e0400180b00c0c0c4a030142401c140160f14010305401c92040e03031002c5800034102c020140c20a80ca25008044160540f82965280718070000300341c00820610031039000300d50080460b494507145580a50194101107030781e0110581910340719070b03400010312205100700c0c0e05699 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 337747428 1250 337746178 337746193
    0xa0b03150a0510080706080601031d01060b09120118081c050703091a060d060c0e0a08031b030307020c1e09040f0201020613051504020d140105010f0501030b030d18090e 74
    0x450414070440341d807004400fa8480d45040007207e40152203d0b070050000e2901050400d5101d02005901100040f400d03481d41c41d00c040010300c0079401d4040e201808046a0010405988000300380c02d0f584140c0703800140031030311130b10800040ca02d10700034260440c4042c41c141d45140600310250856604958800c042515002c41c60208100c19264044403824000c2400f00c80c200540490110007060000420082c1d032107020301e45e894050b443c1c4890812000f861408003686908040e9181d40144420b91050b00c1041e81d0004a5200441039910500d000c2e801021403041207810407094407030340c0171040003c800b85510124140c8900c40c030640f01d1401a80380f21107401c1d640c0700081c5000c00061801445922042104001480110f000c0c1440c80c851031900070541c859000051000d03003c0e100040c46407034402c140c4014180190403690407a0070405030580b030107555000650950727280348407655150b001520040c1c60107002d01c11400041801c00442005152640d03100d0f0111450080c6502c01503001c5203 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 337748678 1250 337747428 337747441
    0x602010c0f03052205072303060609130305070c0509090c01170112170d1e05090a03140d09080f09040609060b03010e15030105161b03080a0b03150a05 66
    0x2020700103645180ca401c020600d8100300500076422001d404110f0260b003019414140081004180041c0511010000187c00c25031541202d0004007080107000e4040c4000040c41480c20301c003064425012140e049054810035502144c00354490070040381d40c40d0003500e000c03945840d0160120f1141e1008030041040702083c0d400584045c15001240c20000d00040c01130120421502d1302e00403040d8441d0b03268904448000e4610081d018500c21078030802e18024900d4005114207100580b01d005090f070400c001c0c0c4850364125110a01744401801241c10403150300ca00840c2b03c402003401280c0c0391070018400d1002d55448403da4800c0e1f8401c22002d01c00304180909141a106080040c040c00400700042407501c01c40010500051041c001e8900c0040d00240c0c560081c03081444a103034000300200140e1030580119210172403411104d4000540c100707600c400200c4401391490b0499090384031707845645e84c4c0c2001c450103032440010300d0b81c041c080c5c03511106154480d807421038003034200b0b0040442d017031070400d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 337749928 1250 337748678 337748687
    0xf06030827030c01050a020f032d0f0f07030e1f030b06131202030304030b010f0329061e061c0506190608060d05030a020c03010c09060219050f070602010c 68
    0x81c080044400c00105032007519640009420384001e000382021a21142c1c2c04100341e00b0410b02c0c0c0b4070140c0f82e01001840c06005030340c0407000d40c042860040c0650345501012805402801038101c0700010303007010040705060803070000107884a640309151003001d01d1a0540440c0301100c00102e24030b41d03060200d016003185501801a8103840909580c100c1c103140c400101c5040c00315541c03248400f80c0480c040d51409640701401200c3c040e540003c0c000c0c865580d01d5000e49106071541c8030544800300800128030600708d0407280c40c42d5a80c40c403010300030152209420004220a0050042e40340041080e04a800340c0b1242c015020722408807000c60406462003809405940e0010035040c86100409100031001880000100607500c0601c0c0c44215560703400d011034800780409001505178880894880c010039800554150a9041600240311900a8000c251066200b42c05041c3c0560084c03550300104d0544069000304580c000d808542410ba00f102c2581d062041d1a005800141d4490010b210200c5c1c01 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 337751178 1250 337749928 337749967
    0xa03062306100804020d081e040509070903151d0f010203040b070f0207030303021e0f07050d0e150f072117040812040512040617010906031106030a0f060308 69
    0x203881c120882444450b008000c0b1000802c000d10600d60180c082007408003240580f040000b05a201403007045020089000340d801611800d4810724280002904039072040d01c050f42120b84c04080c0c0703014180720b042041d020707000c0c654013204000080c0e414004075a1080100311040d0386800d000507601d04050400c141c44280040404042c02081012030403c0c6a001910a08403a050300e00140c9441041803510131946d8012a0003205402c08580000780940d0000188440340c45601100e0b08000845000e448620b06410341701c3d8462800081030006c080140d00411400c803185039040c0ca00030550b5250032002c06e2a0414549101d2005103001150344c1080250b00d2001da4103c48484501d080c0d6181040c900c5580c1560ba003001c20344002c18200202005100309a0b200c4002040d195a1165401080103d40514020103c1c0c201c6000241c107410700d101e8ae20950360000c2d4010321800d100400c2c00010382c0040c00da192802e036200580c050b548814030035407010314482c05099039203200346a45401c48681 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 337752428 1250 337751178 337751191
    0xf090a06050906041112090f030a030c0210090c14030c0901030605070206010614192c03070b0c06010603050415090503030a0e0102090108010509070309061109040c0516110a030623 79
    0x281180e001c5c024a102820303074101c00301440b02d400031999a05001404c00c4199050680c140c0f0010440000c0b00740c040d0000300d5809902d6013100c1c0507617400e1500c4001d4543e8007101601d40c9020020038041c07540c2c082c0908120f190040c080f51001c80100001c10060902644141c824650340e2051011281d070500036580104114035102d401000101c4006080d403040002040e0303094039600300184214000e0003000c20480f412543d22508004025041d90702c1c0b0713240b107030052090045102c003180f040b808905075000c501c058002030080da801d0840c150300800000c0d005079110010515800e040807800d0040f004428030030340140d82c0b6410306100070780035505100300340c0069134014440b500395640e0007005c1a045800031a10400d13a038854001c190000c18417810040d00081c01d150510300c0020301a001090b200206440401c460031900e4030450722070148558541019a040c181500402c460b039082c0761049400074070400f00a641c13079595204840403e0149422180302540203420002c1c174405c1c0b5a802076 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 337753678 1250 337752428 337752431
    0x902040c02030f030f07030e010509250812030c0408030a0f1409030a020108070e1207050906040c090611012d06080d0921050a030207090e15010902090f090a0605090604 74
    0x21120100d0000744c0c000100b03081820201800010100f034481d401100010803030000030881801d0101c4403c0c1c80300c1c00c01340412003000c00300102000440044801074220340340c00002e4000034109000c190200d5201a02102d0508414400411151020f00041c2000f141c981c072079849842c02e500d0003500f40e281c1000b4503d1800c42c14010007040d52004680030140701e50910b0903294669500f042070703402c01e085800705504a5a50b01800c164140300051010a41d042164502c1003551084104400e480c883d540c0c130300c001051140104042c034090300171030001902c80d1001144190248590403105000c2020140140d100309810304628159841003802824104001d400b191103440b0010340046035520407000110040320341d24200643e04400200500d0384034080e1010440503090080d40d0780d427140160010a850300b40700c003145510000e10501280314100d01100d8503840c11007804000e420001a2903003100601d0040350090303a400c0042d81c801c1c000b80303074001080b5082400344265508014040d0b40281e = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 337754928 1250 337753678 337753687
    0x60a110c0105070807060e1f06180b0303070b090a150222050604060f030f0e06010302031b010c17191d010810050603040c0b07030201021207230a021e010902040c0203 73
    0x604c9260443e041e841d0404c2000c41c1c00c04d4551519450210365003035022500c2e082e18600194900603400100460f1034012070060050040103075082107504032006580d05600401851001031103084102da8040c1059060303800034419070711303580f06c1e0780c0c06108880843e59000403400c0c8240f00400c080d045c0038038050300c05491181484003140c01441540210400d02c8844110085c52600c00c1d040440b4544141100b03000b00d618801600780d0326142170000320b00c28099041400f008080d8065000100c3c013050b500d1303403103218580e22500d0b09100e40104004800a0070400742c0920034018411441000f141c0d83c840221100842c51084030701c00b22100c0383d041018034814031400300803000c0783c9070940d081201c610b5a207031502e2034484003036405980040705a08010070a1014142c040d03010300b88140035403d0142050744c80f02c0301290420b0752403092182042840c1241402d00e00301030080d0075080c0c1580110703615401404282c91440c12a0141c5000d0340e91103401550440c101401502c0006040d40000c41c10b1 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 337756178 1250 337754928 337754933
    0x518060901031403130b09031e0d03020702060c030a1107120308010b090f0307030b01211203090804091103090115060f0e13020d14090304181a060a110c010507 70
    0x200a042c44050905040390710030703c010107070a1007140c4181132046404134205a035944c600305c054101d20340c510b1003802060b1002000802035040003807218480c202509804c051480250700035040a00140e8105609100000d400d41042000749041c0409440d80106002c0400303010f0300e440d0880d0860148200a140300c00c00083e040728a0505407500012466183c03141400420a000d500c0480c00394548107086001050184c0018900d05840031000c2404003082145c101051850380c680c0020301d1442080f0140c400540b207039000b41c0c0802d1040b000d00d072420355224148429140d0300740d00c19035050800400d0002c2e06030248592074a4000354a050707030006151040c00b60036005050f0001081c4101c0604540c03041e590000100f00e080e4503c42c0845d11414100c0144008000f50a000100e010316070b004517200340c07000025a821564000d031545140b4604640500c050180c02988840092080b540402c984e504c07440601070310b40d0325644206212603410403141c40c0091011655041c4101000030102 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 337757428 1250 337756178 337756189
    0x2701080c01020d1b08030c1801090609050906010e030313051908070b030705070602040e0115090b030a0f02070c350703030c05030d1b170609131a040309051806 70
    0x40d02c50320308040b9131118901c240b40c4608103441c0b40051400750b000041000c01c031a000060514802d00b16481101450080011745e111102c1e030050001150611804002c5403500c031110b282d02c00010700d450007400da49500840c2c035540200003105010030313102c1d60078001801c06141d0450742d400304c038000311143c600c2e0001e4039456034510b01a2042002c0c0000002c0c40103070082084490741540b0010455940782e5480c051a4081002c1c040da0f41c00e0a03021020030310080c0700d81c90440c00c0d5804429518610b440d030300101d100a2030a040805c140e1a001d00c1210301043d00f4148240003003800728225035001e2104100072590400c0801030310503000f000310a94100881c002001802c0d40c0d81341c2408241c10b96a800d055180d4005c58803695000340c2400000c0d02c107401c0080f44000400c07400e8440301ca03103824031002894a050115500ca400102a03800500000b0841040d061038078020752825510080086101c440d03084200c030705601260740620704001608041c000c40c2e007580704028a849560812200145 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 337758678 1250 337757428 337757443
    0x90e180a0803070e090115111608060711060f070e01020a0b100314060f0703021303020d110109080f0a0215040e04030302122d1005030f07030b0a0b0d060903020307022701080c0102 79
    0x100000c081523620f04002c10842030359400211104202c0881da9846020ba44410880740b900020f460300822404c1841c0002d40303140949901040102c0940c0c4881c5c048030903040c2c6045060440c03007000c03440340102d001080058003c1010100c10380506045042c1049064410b450011450340700004010b80e105554102e160003407001c0c1307005030f900c80e60180c8035400451143c10103503006907082080c4040000c0380c4005d400c0c800007a03c4881e81c0c0c40da81c3c240142c131201c6a000924003900640045030051514041c0707010000d207071000b103c1c2401e8030340016a181c801c0c22101100030a1340056080f1050300300064140e48101519070300031440008101030300c00d07080713440a90703000c0107141804145030051300305029000d02006002c4500b00e0b00c1000f0055501d0300d952101b6520b130a445004075043d2020341c05802c0301c2c0500030f0f1080d0340010281e5944c1c00142500300f01a400c6001c207115600040c1c2c0c81d81c1c00b03104607c00f903d40300c20300d4402401151008003030681c446211355101042103016a42c0225041 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 337759928 1250 337758678 337758719
    0x150613030b0a0b040f0903031413020d0203010f180c090c050d150e13020108060f0a1a0d0203161b11150d0507090e010f0303090e180a0803070e0901 65
    0x2804140c984800e0315024081074100e659101741062a8030307070004441d51000c540746010748d509000c0140070b441541c0c070001068540340f8030171551210590160404000251429202038000541510424400c0023168080000005038841000ca00d03001d000c84491807601406202904100010202e940600a40b24000d04105019100c1c0c06400e10b0304540580640100314401c5246039600d00444900300e102650b40d0128049003084010070320030b0518a200c64940003001c0c03c46000603042440ba100e281a081c42079001348003081041d501c07000003500255010342d00e03d5040b0f142c068081900a4040c29036400705408200d081c0c4450070214031030f81d10000118009a0701c0301003d40d80116454100d1113480c1c038200f042414401405000c6501500d41c030f00300d404d0741c12846601d07604c6011841c020009840050300003580040b05000754008202a07a401c101da14004001e400031821440f07040c81490300007500c804c0e04c0801040144c0703400a080100396801120100e401c0d6040103131750868982003030342da13 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 337761178 1250 337759928 337759943
    0x30f0a0c0e03100519061a03090a050d0804061d1f020d240608041703131a01030302010f091a0606120c09010306050f011d0f150315061303 61
    0x408240c016540009040c01c00703000c0e18840d10925143d400030b040b06850440181643c1d500c0c42c0c02040c1035119002c10348035a0500b503407006404003003c80309a040a4640074140c0101c280600008200700080d0b03510341c0464488001615043c00c0c00ca0844102d0240e452003440c08116021004101041030081000c1c00075240350b0300070101150740024042d0300c07602c3c0501e40c03501208021040380481420910108140014015901c45e001152a14003d4600401c2c906411190181459113000038651181143c5110a040c1029840e2000308110200c6a4072081e00914010b209055081c0030784801c42015000c24400e541c000d90340c5101d600c042e01000009000e904011072090b540c1c000c1201d50040c91414140c08034108210b80720440c1c3d1040e025240404d05e002400203150030500d40027000400140c480d0350b100c04c4800030503110092107180150b0301034031100001220756114050300c000644d0821415490b03140c40141a0f0005c04401c0c0700074482d00080c4020303440c610410b603103001601c3c0e01502 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 337762428 1250 337761178 337761191
    0x3020105060d211808010605120109030807030203060607020604090903030b01020d0e0d0503090301060f09200f0d060e07020a05060c070b011e030503161208060f1203070c080105160302030f0a 84
    0x201181ea0740420312030b109035a40000400217201d0415000541600c608880140e00e034400040c1d220300302d440d0418000d022507108400509428000e90155034440e20103001c20303260100a5002a01c250b1264108000c0345075151703280e40c00c0c1a4948a400c4440d81c00780001c00031041c003060003030440b00c120180684607415119622007001030900c152845c1c008003130002e002c01034603048004880030403805400451403611320202448540c4854211010509007902840d100301d552141d0381e1903000e951090314080c2c46140c00241080f001c821140316220560143c80c0744609440c00a003802405811112814000d02901c0301003101000032a0440313090300b442004d4941420188170120845600213003032400003107041040341409004900c2418407a00200c0001c1d1908607081d07a1000c802d80b180780c0c1000e400600c00c151424004402c01e000700c56042100d0034032005035941d0103200e0f500d4101040c103945582c207000801101008420030020182025400c5185c001814008400c00a0455a00588541 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 337763678 1250 337762428 337762493
    0xd0b01030b03012c011a0d030e090c090f010504030b0c0a1427030303090a2d050c030d11060a050c070b0412080c070201090e0411090f010303020105060d 67
    0x40c44100d2007000603009201c403400e010f03802152210081c5880d01d000040c5984543c500c0703018400c9040480403080810b000c90281800e20022190404044052140a0080306c2d01950340007607103880f5206130301c40300b0b0341c40c0254418000401c1241c03051034140320080c80180000344603404190b900c044c1066403070343c0320150000c046815a8800440d1400c0190024403444c010001c0740e001013a02e01041c48a000012100c41450303500e03c0101d4031100650080c11610000402070050f00900001d440391045c11f04101045c0c1342c4064014010803142d0b9400a0324030302840c24184606001d401c43c0d0704106660004408059480f4107000b04102c0180d0382d504001403884109a0035100843e8100702514990701d090b00c1c241401562a41c4e010021071140d1000071b00120003403007200c42c00395041c2d4904c81c96500e0008054030703038113006c0e104480e503d41e003c100084a84036948943c4c070070314503400014429455810007070308442010b000f550203020308600c24408228060134000141600101c4d560481c951071 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 337764928 1250 337763678 337763681
    0xc050906071a010303020a1109060d06200a050d050112021503040618030c1a07050409050c0702100801030614040c15022b0813050c060d0b06031006030518030d0b0103 73
    0x1e10365040da5042c408004828103500103003e0349201e1003216550401c5c1d00c0501008440002100e103103600000400c01c0d880040d0b0f0bc0e03006003e840542d1001140211003e0b200e507480d9810900340b010000e200450760b0695900070780140c3e8010400c500000e00e6041c1c2903004500040b40004142268405c0000490200025584210000c4c6c90604680c0044002860000c0211500c0d000540b441040490300c41148000501c0540c0104420f4a40600e02460644c2c80005050010560341c02e02c1003e00404015841d418154102020207940e0100150b040d85446012030301c0d021a01441d406010341040000765000231080306881603051000f41c4410b002400328948514032454110031100301c001140c90100b42458090121036580341d42c0050b954031000c154101f144c818016103d0b6020420205107421301074000c21001e0900b20300480d29001c0e440100f95203510643c3c1c3c0703d1900d6000c050802045a05219082d00b103078038141200a030101b003141c00b079074034080c20341d0304c4942eaa0740d4000c85619030300a = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 337766178 1250 337764928 337764953
    0x30c050c13020301081e0d0c030215100f1202010c081c0906230c07030c1b0b0a03051303020601030b1e010b0904150608070e04091b0501020706030c05090607 69
    0x100007018400500c070310880650404e12a280c0c43c0c0c400c0d9003d0509244400032001840d403100d80080c114069a501c049480000b003810036004d501450492100c3e103014841024481d255001c11041d1b05882d2684541c425500c03075114543d004011885000146c2c0e02c81c01d0104040d401449968441100240d0122800d1544040940341803030301c42c11000f0000710341c1107801070502d0741d11300011400d008002c1c00c5640c00121070340d00e40290100540000a401558440501c0340a201400c1c242c251217110112015055045040140740104803c80c881d3303030500500360301002d9150040c4040300250b8000c0c5d56021706000c014000c20f5904000b80c03601d21905c03814522460300c158001e0195940e03084e6520150b11040d01240601d0078100903078042413070b81c8440012180139a03207104440d51003420071118554615101c070360213074403003104102144460507145c04410660041c20032152522001a03d0300c038031680000149810205480d07015031704003050b180030841c1986c10710b41c0c901d203502e004921280c1 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 337767428 1250 337766178 337766203
    0x30306040906021b01090b09010b210c03030a18050f0907031d01090f110a080307060e0a0822050102061618030516030308010e150103020a180605090a090c020a030c05 73
    0x6001898281d01001500060162801f8420042d41601c4100c030880c01da60441c0403407904480c94660354040182c80b50904c14140781c0800695009103c000700080c1103510000d968400500e002072820040f0036242c20040050004650752110900100041070549400501c2c0009040c0e035580c050b1014103100083e0041101c04034002c0002505074074041c0140c07555490280c41c2c00c451186c8400c003a0810300311040a80d442240150305045290f9580009070205001c10501405001e90b404002103080003d01744500c60020b100040a00c0700d4880355190101e503000904651041c820321908402806145860380102d00d0301c482800801e0b60224452410b682c4001d000c1e10a04182d48541c0104202c4442a40e10aa42d51032860b603332484805610002681c441c480e0040382c9044000560180c3e005244021f410700b070442600108440e0f15040a80e1a800b0002041b00040c1012851074914006030191610420400ca07016128a000b5590500181d00600b4042c010014000b40102084107150818 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 337768678 1250 337767428 337767457
    0x1120c110708012a020c240f07020f0f06030a0e0a02060a20030906091e0d111c050a08090604080601060519051219020409050c07050606100203030604090602 69
    0x1e5851201c14001c1034484c03801c001082c18100d070080503000ca00d00d4141c110019500801410548500f013050248070038100d134080d294144001881e01c0390303e0002d040e81030381041030240c44c0c04075401030107590004480c1c1e1520400d0308098804c0740d5075030182581e80202040d0340019240301e0300061540ba045001c00040e5001c04003140d07101c80f103603001d28035203001c4110480300d4a490b40b5194140d5600c1c0a082809a40000b0901132359620f410202d00c001c0c2ca0100707408021040c3c41405010685c402900c080a890040d10f540a04056040000d0140c85221201018103400c428580b281620348052200040207043d0001c4c00c020a41d8444003a50042e14884095070f103556505c500141c05a408400e107200e1030240c045014005a0284090b03440d5a50600d4181c201d0b651501400c4d24101d0985e0030045c00d41d5421302012400c101180715162003611a86100c96881d25a03080581c40c03c40c0080240f489200864600c010840e404002d598004406a0300803511103160b00d0100040d01410040c0c0e0b82d0700 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 337769784 1106 337768678 337768693
    0x90403050a050d18030804060507050c0715030b0307080105010e060916030b0303041503060513060812071a13150e250e07050304050f0102040501120c11 67
    0x7411183c1c00007107014640c1e024100c0120251403d0740010306042c00c00003001041c5c41390a03001074560078100d04040d8418156692401c4500803011000c44031400e0a6a250080d0030090981d2401400e035070005444d0100340f80201002d10803a43d29011010115095080031b844050180002c07c2ea200c4800c00394a50960280c800f000c0c02daa014481080300207420912500e0382468512541c0d4045003181c50b020030030410708140024580c60903c0d10b001040041000a403144981c426050030b1501c07000749007066402c641c0c281e140c00040c801c08000700800d64001044420b04903100300c5d41d0320700507503c10000c0c5044901c0403146040c1a0f0000c050090380b80031040500075103805000c28892840c0d140d0000c03804188060b211302001c1070000c0b043c0403c02c0310a110021540089000850405243c031000a1080e00c1500f112020740355100000d42d03005200701b061458014141080701c485 = true := by decide +kernel

theorem cover : BRFrame.Cov 337589928 337769784 := by
  have h0 := BRFrame.cov_init 337589928
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337589928 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337589928 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337589928 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337589928 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337589928 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337589928 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337589928 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337589928 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337589928 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337589928 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337589928 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337589928 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337589928 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337589928 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337589928 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337589928 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337589928 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337589928 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337589928 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337589928 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337589928 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337589928 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337589928 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337589928 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337589928 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337589928 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337589928 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337589928 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337589928 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337589928 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337589928 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337589928 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337589928 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337589928 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337589928 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337589928 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337589928 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337589928 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337589928 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337589928 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337589928 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337589928 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337589928 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337589928 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337589928 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337589928 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337589928 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337589928 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337589928 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337589928 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337589928 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337589928 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337589928 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337589928 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337589928 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337589928 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337589928 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337589928 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337589928 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337589928 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337589928 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337589928 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337589928 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337589928 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337589928 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337589928 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337589928 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337589928 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337589928 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337589928 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337589928 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337589928 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337589928 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337589928 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337589928 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337589928 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337589928 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337589928 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337589928 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337589928 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337589928 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337589928 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337589928 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337589928 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337589928 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337589928 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337589928 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337589928 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337589928 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337589928 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337589928 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337589928 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337589928 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337589928 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337589928 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337589928 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337589928 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337589928 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337589928 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337589928 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337589928 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337589928 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337589928 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337589928 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337589928 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337589928 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337589928 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337589928 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337589928 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337589928 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337589928 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337589928 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337589928 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337589928 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337589928 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337589928 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337589928 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337589928 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337589928 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337589928 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337589928 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337589928 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337589928 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337589928 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337589928 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337589928 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337589928 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337589928 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337589928 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337589928 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337589928 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337589928 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337589928 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337589928 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337589928 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337589928 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337589928 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337589928 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337589928 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337589928 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337589928 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337589928 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337589928 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337589928 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 337589928 ≤ n) (h2 : n < 337769784) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
