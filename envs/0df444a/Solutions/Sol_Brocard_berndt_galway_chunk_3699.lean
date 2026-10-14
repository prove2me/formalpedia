-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3699
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:25:00.556138+00:00
-- url     : https://prove2.me/submissions/6e94a290-31d6-4a08-9ca2-de1a61f2e582

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 665107913 ≤ n < 665287769 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 665109163 1250 665107913 665107931
    0xe0d0e01030c02030d063201080601030b190305100f02120f060d0b161b030e010503071701080a1a0403080126011e1a0a1205190311120418 61
    0x10804c1903c10745842401d00300421601c6075400900e000358104c0c02000d0f00840305515140c42d034101210300e2110010303102d21145403503400064002e002d01e1455103400041480e01c0211141981004c00025401400034149036126810b51005880e19060504290f0f40100844030070411781c1110700760312038044c041c0b0211644030940040c10104015001400414081040c03294420340b00d0154402aa141d0321460100e011140c807500701c0842c04100a40451a2070156107082d500603c0151351014561a04010007a5525809112140d003a00705007a40d0f48400d07096020001003040c10b42100f4101190b5407824901598000c02078601409480030800c0e001f0034420080b84d10000503500746440000a0000a004036070803000c101c0c80d06d00003015581442d40c840c04180100c81d620000355000b07080d80a190307081c40881d901d1442c03503480895180c8280400740a94844000b0391590700c501c0795031a06040000c6003403240c07a003440c50340140107002c0100800c00000c8031000903c4001c1c1010b12000c01c050380 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 665110413 1250 665109163 665109167
    0x1a0705070503040605090a05012d020c031510060203040e0c0d020d0509030706060f14010806061b06010e01080d0903030f11010c050c1902181312030e010e0d0e01030c 73
    0x166030340100948008900401c9154001000d00b400a100740c9040c1003595981e4011103076840d140c80410302d800018907214004150182c92a104141140115a48281b000f00820720f040c261583c0191001400ca040c021052840c00e01000208001e1004500301403c005640a00c124050710640e1200d00020b074040c0d10410b140c040c1d820648082108100030324083d00310756200d9201c1e84040340d03014607091002c62051282d0300b001042c0c8500394043c0500c10399540066828100160807154455800d010240c20a141180300c282100d0101c8042e1a8a5260410000c41c040040c0c11070038582c3c1000d40075081c21a803095150301242d42528044e0546002ca040c180d40420b0742d80da10710815420981c00140142c0c01c2001000c980c80380d0411100e071003002c19081c0d943d224050500a500101e4100040b40341c0c00c8492486404c124903070030308145010740340d86055400840710080d5021135111000903e036404c00b80325100544c074240003d80400405a03800a02c00d0025080d45030525680d00c8900045038 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 665111663 1250 665110413 665110417
    0x609120f060106120f0c050d110409020c0703030f0503010602062d0c27030709090c090e0d030c020a02090a020c070803030408040f05032a15031609121a0705 69
    0x880e5500c1641e855503140e0f01c004100803840050400450b007440d44048031a1154030134201c02c07058a9407040d0602d001c806800b0003403c1d1880f0300c01400482480b0214400c0100e20050140a15000003890114a50728010313010400028200043c400b040c801000420380219546a0140340b080000e00085081003408928000070381d801c0e00f808208408001d0043d43c204007e0600384000c080c238042c19082030301c280c18580503003507400c2e40580003003d040020f12000c0c0c0283c032965103d0410041c4c015180c07100c403c1202c1e004401012a6440407801088040d018400d20300c164005201414100702e56402180103080094640c0c14020b90000342450194002e001d600050080041540c0d680d00706410080341540240c0102c0321946841e803800960391a0004a07840d2007002e0010004000815a9161038840d40c2c1c04111600311788243c004100c00c02007030001718030495145ea1001404180b0003401006031850740c00c00c2400b48000040200403500b102c00007100d0512040340d05103996075600f000c41d418 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 665112913 1250 665111663 665111683
    0xc030204180f060606140406050d02030a111204031e080f070525061406011b080906070308271f09020604060804030e030c01121a0a0f0303120b060912 66
    0x100484080100b1070650040b5040b82c01329641c0320802c0c6c1e603203900b483c042d100c0d520070742e0040fa508015204c80320301140c01942c0d000d101c03030400040b02140c0345861109a070110000342c00c000642002c120800d07810041c085000b034410150304c0e161004400d005000b00740c01400c032110b408004000155402d1080c030454140547c040354032091275040182800485035800c2c4212002400d0948090041580890040c41444140e4646016040745106148100c034101000d8485500030050348490740c944d60010b01c0308038400d82d07c920355450540d610803965010883c4040325840342d1445a00c1c5000b0000350001081c40b0b15000310100b10b05601601c000380302c80c80009402c8000420001075103031300304c4017052066029440b4042d40c0f0101c0e8042544404030211500c0c04101d03501414000c07401d9991000c2c6511042408003065850780100258001206034446d03551034540c03103806d0040543c00300400c03480c1c4400100a00c40107100b44005541d0780600d116017402000d041508126403041040300c403040c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 665114163 1250 665112913 665112923
    0xa1508010b2115100306031106071a070201091e111002030f18040c0309020102070e090604150f0906020d0f0504080405120718140612061627080d0c0c03020418 70
    0x2150904c2e10f03000d80a401c07a480161207402d542c2d1214442c0b03060000403928039a50004514141e42001c0540c5404804060480d034119940d4449100000340100348000b880740c24521203900c0280c40d0f12f00640b0243c104401e45001d080891446240e0503000001d6070524a0311807401c41c1c82d0042a0703140103039982101c40d200c0d8000c0c14120843d04003905a40003181d03c90003a420703290303055241c40c0000c19144040c2d170010203650042002901081100c1e00c48805030307050328400300321510b500080009541302610255a0154005040310b92042c19218958013a11611418405403915884803240c900440c40b905000d031000e001c034003400e10380c14800c3e40c019140440440f8541002d00162800401000000c4802440c000c004240c0610702401001c402d03240120041c007981d501c2c0d9078508091149188000c0600400000010252205400c03081540d103000158000700d45c91300c80717290b00d0b107024a040b04d403e1100311092a00070500c80e0750f80d081a00c1c4c0569010843c500002e040010901500070082e207 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 665115413 1250 665114163 665114179
    0x70e04060308090a08060c030c070309030b0f060102061e150607020d2004061202010c0c05030717060c0a051e07020411090901170a0b150a1508010b2115 67
    0x1000034240142c00f011805607401a41d89481d208000d940300b17000c1d5043c000d01d070b50500001e01d550b009200200200c3c2d10a190001c4160b540c2d235505c1e44181d00035100d0000300282c00d0f04000103960b04102c83c41e0f2103032420b110014048904c01d02404109005003512404070365803089414940c545108961f0b4850340582222040d40756401c0180c3c100d0215031030304020604000b904c03146407505001f420107076448014a02c0f9070711420790042d1046050010201d0301c814a48800040341c1d5024000300005020a0701046981812454080d003040c1c40205806065442803150042080c0d0003010ba03480c911b08406c6280566070950314a00c4640108240203600909258003c0d041c02e640724040c2030941c83c107540000e031503603c0e00035903001d59218461a0714568800389541c0c020940500c4803d030000d10310135460704c0185001d00401e80740d66554110070b050518000300070301400e501c40080d600410164000300d06101e0110350000d10703400092403c00001c809400800d1240105120404070003600511380c40d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 665116663 1250 665115413 665115419
    0x6010c080a0522120b090a12050403050d0e01050a2601062a0b010506030a020409060b040e0f07140706020d05040606030c06050901050a0f1e03061e050303040303051b0105040303090c0b07031403070e0406 89
    0x9c0044e441390200311014000c255118442d05d01440c440010200142c6800c2d0030040c0f401d5003211100d186c0715a8080800d01c44010403a064945141c0e98064000c0b40c2d9090b181903aa181018080c25110b885000300c00c902204000200359002c18041c1943c000300c2d600340e80c07a151590440041d020700c1c1c00000d003140c88c241c40040c43c90780940c014400c45403166a402c0c060384e18039600d030034015001c9800341c000c02c0010040c0c41d01242550018221248600001401d0540d829110303004c69038201e804079031495440c2c50500500552200782d038014056841d002c1c1c074000303580d00001c14600070b409524042c008400010640b090089035101582081800415071802c90789100802400301071048180280e01030040c032064800800c510342c140c8402a005528092171558119041e80c000d4526460081c0460401c00c0011001c1c05038a0059009560214411500d42800d00b0798a0159200c148815800c04c5110006038200341082d0400120f000c40d942c03255a03483c070030340d034000019061035801031800c2008 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 665117913 1250 665116663 665116667
    0x1031214220e0109290301060e0a05010305011b0f0c0c0e100f050409020a0b031b0412030806062502011209060f060f03080d020306010c080a0522120b090a12 69
    0x25000319108810b0b120311590360382d09a801103d05c00e000c441c1c162444030403480320011281c2001c0403c0c100190000441941c0c9240300c00d4003c03803d4505283d80c13600c600041062080c2406141540040e20009000121034518058006644501c0100601c610180d100d0284904041500c009150030845884903142c4114600061480c074014074129240080c004509414188602c00341e0941c05030103000080c0c00c1800500064000500a1a1500007090303642544000503010380010004000d07000813000f02d5141c0640f1185c0010031080c0600000d10203900c02c00c5401354070b08403c1c14940039079585c03641c10380012140c0f08401c5110800843c20310030031108020075070344601c00600f8582c40801c400c545444950070300c1c420a10000c2c041e14410f018140c80403449900564000d1014180ba080300901c030f603101700d12500002c0101000c10b5000c28527101105400c20300c3d40080380b5040c4500c031040d00348010300f500c05000310000340c0340000307010014100810420410304469041642601907a008901c0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 665119163 1250 665117913 665117977
    0x60906050c0903073c08010615020d08042a080318010801080f0a03050c010618090204140603030a0c030e1306150212030708090307170307030e0601031214 68
    0x501d8028814000c00003400000d02c0a031002d041d9100c411800c0440c5d4800e004003410f14141c0345941600f80c1ca00c000185440240b05030b00081c9412402c0404000c1d074400064181707c281e00791403042c001d0030010407002815002680e2540d9284030319016a559583d803a0710b010b1343c0b0640011807a480001101d003480b07040c00b1158001c461090f0384e0b480d4a40e8940380307136544803240719034140603503484500404006400740020780104c000c0213000180c5190780d4403510280d4002c0c011030116035681c036169941503080c03038010b800c4515210201c14080d03040101c0426641c0c41529503603c02c1044217030303d4804051007100b030a844144010319a01400c0c01c2c042458004100612484400703d111a9007101d0090000c104680c168903201889415551219010354110300000d0550b80700b40410090203002484c03000550f26140c80c1001000d44034640b211015003115101c011041344c66001000410000e08101c4070b45401041520309204141c0d1194844496800f0f040b620b05d6440704035100511202d404124 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 665120413 1250 665119163 665119177
    0x60c0901090b0d150f08010b0409150504050a050d0504210f0305181f020d0212070b0613020705060f01140901050d11060c0a0b060108040b060108060a1703090a0f08030a0c060906050c 80
    0x30081250321030000c2000304036401c08ac8020111f86600c4c0300004035881d42d074410b40d4007901460603590091400c0e0344d00d6061680008510000c604042814800724400521000c0c03400400d175116000d027010303505c0e181001d5200510040801c000040c600380c050846140d04c03800c1c08400340542a205414100745040800f03417035101001032059100c9203820030310005441c2c0c2d81d0081102d2051811a00d6156407009541c024155501f05c1d81d1400c8109034400345200414166000e5000780c0f00604240a0500e40c140b410380c800c5001071905a0700c810302e40d6500305018111207003100c01c041d8418251501e4004d078000502074039809007000c40d441c01d4516003c580160307264440d80980c0810381c1d0741c000540302001c1c143ca02a00d89030000c2c0c0041d00d554009e00000741c1100c001000f1800b42592171140691524a0491038021500302044c030f801c46041903044a0041d018800f4400c42440c1410034003030707607405000c4011080001032075503002032000c07551184400b144c1006091120f4501079842083c141d00c00c42d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 665121663 1250 665120413 665120429
    0x30203040305010b030a0b040b0618130c051009090e0c120d0305130803070f1106070f09081c0c030905041b1106070237030f02060c0901090b0d150f 65
    0x20301c80903040d01e4046121b07186550b0094108060f42c94948800840100040140d6009942c64121541caa20700c101e125214002c40e02c128503842c55a0314104481009075840b6601900000c904110a16003280c60003044c3c3c1d0416000248038564007904c246061460880250070183e8510341c4c401c0d03100041038175600744940b51010f00c11a00c1c0e040f0f0703420725100e50702d00c0503014190034004105914840c0400e10603070303046440c01c0500301803008c0945040c044161460390100300d00113800300c00e4036007100d002c0001307044c000080d1024401003104000304030040552582041001090141090b01500200c0080c02c0064400c209151402030a40307015000c000245000c1012012915403802c000036120307100d19600d50291000d10440304c20281e208260084040c000400d940b6070b200d620b16840c40c4d0452240c081d54850030070f0000c03c070000c0d061450103800703400044400c104086103a41c100840100726000710a641381d0b01e91031540102c00404550040942c6c0810101000078a0314001c025001038406107 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 665122913 1250 665121663 665121671
    0x10e090103060213140d0b040521090315091504080c0106140f030a032c06070b01090e061515040e090105040c080309090c070501060b040e0702100b010512040302070b0703020304030501 81
    0x680d105c002015a240d0b400782d200710b6401c82c0c54000340000d87e0094010f4170407011074805001581446c0324100e20b1841000c003100c004074900f80185001c000b0104600c980d62100202800d10200154070ba044100142d000382903070304080390810601d00200d40c8004000c1008008032604c0390703003a0b0600010080628418070048081d44254540440c008030440e600d40c03155451028101e41c540c00c11403180648102c0801e0b1180540c60640317484000705a8184244804062981070680c480b0490311056280c807201d0340b2400410400030750050761059254402c841800b07040f0b0403200e58694511aa412030000540c00c0010710003c5401500440e01440c818140940019103030b504a43d500c0c0500821250301c0071248000c2600c4254003070050203078030301034000820350a8441d0040e082940c41a4082d014045103401003050f099070600c07003842c1500e040141030251000c4140000c0041c00b03100703809000e000f0703a40c001c1420580208003540042c00b40b400c03465110080e60030065100e400501c03080c1c51035424 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 665124163 1250 665122913 665122919
    0x1e03030209180f0a11040504060f0306050c0c030d092906241c060902072415061808070609031b0e070f020102040503100f0b040902090601030b010e090103060213 71
    0x4400390340f0422440704410300660720020a031010740f0061050002d40305003088041030741c2c1c495019040c05481c04411161084d440c500e03011044420080c40b24241da80d0500890b0441e54012080702c00301c404261021642c60300c02e0400c0d2841c883c2601840300030b50f101d101001c00280660320f01c50700c291401c40d910b427080e070280c0000c85050421090b00400c1c4a07002c0088192601c10200000d441100354540040d005459800c800b040717a01001e026101d01c00150f403181288060701c0110151450001d00912101c5400030b005011720806008003024499141e4105042c1e16154002c02d0003400b01c0070844814568800b0003074854425804141ca900c941d082290701e502a0f015090f0b03080301d024841d07a41d070039a5000c0084079882480310f281803c554003040005100d5504208140940d0f102e0712001030344800405582044405620b41c440c0aa810320501b03102603030b2520f0140c0c0e4000300a081c0803514040d0940100e58600308066003035846644c00001000748101a400740c00d80d40e41c405210103803562 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 665125413 1250 665124163 665124199
    0x210204090e06150a05101412011806030c030f080705060709090c05093f011e0b0a050906031005040b0f07080103050a08250f02091003020a121e03030209 67
    0x4964091580c101401200402560500706c1220498510301d141500141c03111540c201340e1075002800b9000e01408500060060480d0f014142d003880e20140701c1004078070b123103680d83e0503034241511004c1c015180c00e00e0b070303502401986c500f11030102ea8048140c48561070000700103005060307180184d0594514051701141d00c0e6000318200d4a80c3c1d10011f0030050856003280042c00302040001103c5101100d160825043e115000150300b895081100041802d905404808541a040071045030505040a138a00a44c0e21103c0600b019118181c13111142a514540031030301e060641043c0076034081c80c010403c401d0000e1506003900603131852140303582c0707521080002c40700080c00303000107000c6030440c80c1d449001802000c02019aa4031250a1507516003035003c2c01c0c0c0114100c0a42521440e16540c0d02600314644007161a0380200d40400c1610b4807401e68012540d014803d01a00700d402d003400790300509005a44103649a82d100340300b21188003058625004000e500070f03d00e071901400b4106d8072084120 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 665126663 1250 665125413 665125441
    0x302071a07050a0f06020f030a0c0221090f0102120c010902120607021504031701030b07030e06010f120501090c180c0306030809090a090b0c040e010b0304080a210204090e06 76
    0x40d00440100981003c40d15281d805840d141d004591155080084001501d00c04004d54072407404550300040d0a030802d54064185810007240b40140b580309000c4286560b001825074408e0070090319808280d16030000140e113425000b500c00c0100d41d102261100c030b03028054000a101c1e510a88100340e400280010a03603a03240f09135449000b43e0401900e4000000380d04600c00e0388140240740074004c044050f003810091038002e0304241c0e030054850341084161901800303150310540070325004220540c54100c10040d000e00c5070040e1540c3c800f4040182c0305000094110b0070015400ca4141c086865030740b501c000494111184c06070081d8200405110024003a209010880ea00068907502c0c00340c42c0710400410724002042c00d40d010390743d45600004154912800c9125000044015030f4035400c1c0106001803940590147d5841c8004004010006210000784c1d5280e07076040c24103e0182c0d0041030061050500f081100810f2440440d000030540a160460f6010000c20010f50f040c03a01e400324441804 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 665127913 1250 665126663 665126677
    0xa090f020405010e4609060305010e071505070302010609020a260f0c07021f021e07080d0302071e0614060f0f0603091f09050705030d080a0203060103020403020301090302071a 77
    0x11714100150311044034105008080c544040c000902c01c1001d0040c81400284413030300844002603640c0d0062082007024403561074074092007802414190b00c3c005180c04950043c0004404100c40440c42d1402c040c001d40040e0003401d0110002e545074122020024100303a4040c2003220740e005034200401198080c1c42119004041c9040c0000c00303070340c502c43c099195a110360022070704500b000120028040c440916003190001c0740e809002c180c1d1042013103600e00150404280c2407504043d0040000c640c0000e0b0580995040c0d040140c0c4500007410000340c040e07440e400e03884403030009032941020080a0f0703000c005040d03030003031041c0307025200d107020701540500f50146660003200e1010300140c94507150000c0c0d03a000800e0400c443d0a10781c0c1c0f80e4400d5187d0049004034540644840c030001c1040300c180306000180005500030082036254170401017110360043c0020b4000707540007010440d40e9104e07404440c05560094000d02085143d807500075a207042d01d105000003840b00e40c500c2280742c1e01072030841e417034 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 665129163 1250 665127913 665127949
    0x22704110c15060909070918080c0d0e1e04051503060907151707181203050408280303050402011407050a030807031a040209060409110a0e030307020a0e060a090f020405010e 76
    0x487d0400540304001e00c041c41c0700e007082c00503036246880000c5100006001854080010704102280d00c4000f415500941036818815504d9600524034440c240c112641500b0044070b01050b1a1264a140c0d05001440702c3c3c41794060154100700481c50702c00142c0041100d5003609501d0488a0107142190340030a0104c2d080b0ba00244c030f030045103420703201d04501c03510824034100c2c103150a5510441d060894038410001c50220f540170404010120007403003410364040c4950100c2ca500b40e10090513002c40082280014141075840c0003260030369220703034a181d01450100710b005580c0c4040e030070655984c80385100c044000614410000c0d0305144280507c009812410060040c0700d0103070f80c1044065000003540607080b00083c40000346141d1103018200d000d1603003110555907540030600040c034540ca0802518000d0340100500700050701d44500000483d003007545200701035212400000c4480c80c032a80705900c0c04d07040ca041d882e903c0342c0d550b0061044403c240c031042c01c0e4911400a020b402515440c1c0090 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 665130413 1250 665129163 665129173
    0xc0308180a060e0d1b08011a0d05150a020708030403030e0d020a120c14062d221e0302010b030f06011505030720150a022704110c15060909 61
    0x509070420a80d1102c0b00d40c862421000e004800002d5049006640c3c6d00c40a95a91554000d058003940b20000001c9400b050f550401d0002c485e0f10f0306540c40842c81d40310300264a0f6900001c9611b0400d60550b0303042c6500c07104d0140c1c1c07800c06040c0100648003140c0320841318040c00e200c50754190300000f1040c0006238030041410b2095101042650a060442e005440c40650404141c0a1140c01e1010501c41c10b18039030081e00d09118100d80008c43c0303078a40e401111035071700e050074030591701c00c6022b005041200140c03012000c0b084034946600d0951003044489560707004040010708054041d00310b4003211500b502210320a40810206c9680c9801c02e1003031040303440503440344002c00b030f11400040d0b52024490925500391040d40c8082441c6006a0308401d042c0e8000d501c0b040200d0340f620301581d8004111600035401c1c5504690652499241092100004001c80400900310f446580021540c01003a003030580e01d1b44030134050140c40d180e03412025010400c06000298051070013501c201c0c080c10701400204 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 665131663 1250 665130413 665130437
    0x11010e030a11120313150807050c07031212020d09140c0d06090c0305150702100c0509042708030f1605031506040b1b0c1e0105030a090c0308180a06 65
    0x1102c0a81c03020243d4506020030001c55980030b0781c84c0d41060007801c1c90078500a42211402006180c030030003030700341010041d003001200341100b070000d0242c082d03c0e0000308100a05000c1c0134151800c50000030644105400840c100c2d01c01c42859100d00c0281d03000c0c0d0710158000c0c115500303450f12820034460b0342e90b2206400141da40440c0050380074404182c8192052205c6a449880300c1c4e14055400d000c00c036041050b68108101168180170b4a000d914640d0000d008105201c0806040740c06040c444030300950761029441080300c009200c100000480c02803081c016074030380c1060306440c1d00c00c682034038108040c1c80c041100c1140800c25250850440c0ea0b4071420b60311070790744000440c0d1f009603100303a10840c10300001c25008000d400610000000d0250f4501c0903480e03106031820015002c0c0c156101d0b00c0c01710348103000441c0a5940414121091074460382d46d6403080c020900401201001500c0d0506a140c00720030800b1000003800e41c0308051041c450142002010000b200801c1e00030400011010039100f = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 665132913 1250 665131663 665131669
    0x703020d1b0e030609030d0213080a0506040c05041b0f140c0d031503020105070f030c06050c07021810090c121d1b03070b0904140a06051003140c071e11010e030a11 72
    0x40c03c0b09d68850981050380f40d540e0a14070f480d002d40000e00740d4451304404e040c0010065400802002000251418400c00f04a4a100c66111105041040c240315a50f500c50001e240314403901d0710490012400d040d1220700c0500b004d0b81e50200104564080303032604e1181005092100018002c59505030350311441d000b0302e9551000c20401282c1300300c06000340e0003280d00c00185540500c520600390140015101d564500400c91900c1107000c90000c90302c124020b100c140e10744481150107407002ea00300812902060181102c040c0e0300d0401440090f842e040d1903075000e0980401807e070f00713240348044512031451120050328441000e8100c5903d94015a030400084050102521003e50020b00005840b00d010b5920074180000300c40801f0550303030769002440705151400002e00c1d907084520b420080391151454040c051030014000c0341e41c41c0808282841001f4406c090403181403290008098402e082d464901c0e850614500703000c1c0826070030540210307141000114110300640200301c0c014a050f4520038 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 665134163 1250 665132913 665132917
    0x2f03220e06040c0507080a0302090a050103090525050a080105010807050114090f0d060e07050306131a040c23030106050607030507060c1407050c040c081e0703020d1b0e030609030d02 80
    0x204400d00c2011721070200424443c00c054a00506640c6000da5102c131198100300800c003841c0c00c400e051604c0c2c9490000403a40010307003080c0941c404c40103010150550030344020040310035400207070f2250064002155110040d041036049542d998101e0720425200c200640e441c00c03c6850b1030198600c244035080d80b518002c90b0640390944050110400c40e074075602e075002a10310140035482c040d400040b0400007420200446680603402000001a0740300d50b03602c65441590000074810304120140c08a0240160500d01c88000d108807203c01c104450b1001c0e030341c04a01c1d0002c002038400c1d40b0700314000445d402c280c0704642c242d0303600d40e64041c42d103c502c0c0c1e41c03900105a503004401c20010711070320440e220b03840ca00050400a0140c0d00401185c4a51420007054480000b045003c1140b44410300060403501c0040c07501820f48030041074900e80d142e4600714001c0c0141215120001c0c14007650807840c0c4244424001c2c5100169585114050403005040d83c500050301c0d80441a40204001d420003403490740 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 665135413 1250 665134163 665134181
    0x20c19110d030503040803071403040614090105010b070206090a0b130321120203090c040c03090c2c09030c010c08070e031f0207020612040804170105010509010302012f03220e0604 79
    0x3c0800ba0200c2809c51044190012138007264803035036807602000c100b50029946580104090002c1c4841d6041c051181c11500800c54028014400404c100307649a4a200c40c15000d0701c1760141050720380c05405030848c1620014442600e4110034803807110317840e50900803c1880b00c8059281ca0080811101d0054001d602c0100007440c50301034910162159500c03802010550f2942c4c1d40c0100c1d02c0b03002800c01455410326075000c8a80c205220650002c4214901422050100d656240a00c0c0e50340d160444c500314030442180100b254a000110110349170030901090107054596107441d50700045009050b61004800318440408208550503207208089800501d515031010340a40d06240001a207107900b0320301918100d40e4064003203000d010488001b218170303c0c814a410001c2c0b00c0c551400010a108040602029041101845010b100c9440c159890a10860003c4030044944800e03032800b0b44135008804450194018400c481d0500e40410750f000042d20003d8007128000d8a0300c1003008020042c0e04 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 665136663 1250 665135413 665135417
    0x406051e01063507110706080603100e0a17030106030c0203090d061a0315011e0e1b1c1e090c1707031401060609050a06020a1104020c19110d03050304080307 69
    0x103c180046540d00b82000c90140d00551900e034060415500342c0382c10706d100d0303805c141d003080010010000c081d070300000c1013010218100f00001c1e081d4401060b09052201a04028002d1401c1007a0008117815410055049845980c0c2c10044009000c0040780c80348203001001f80d10041c40c480e4040403175030907840902e8010300c030890f00448040090200342030080301080100b5000100d00100030640411880403005090080003c0c541030424401c100d5004010b03240b0030f200c82541000d0007503020100e04a900c1003414070940d40c6160303600c1d48850082c2c0342c440c3e0722179602c080c006403000329071a0030f0250004040d07100c42d03400394880c1440001d2501940c0600c2d05500b920880c00d0010124040d82c000d0705481e114400041141810440d01500402d496071200b401811640c034204181903001c106034112550040314884145600c1000401a01074259000040d01a00710f001c06040030341c13a12540424403910340c0c2c50344003d1110400c50800090000a408200304000140024900b1002503601408034 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 665137913 1250 665136663 665136737
    0x10030803041403091207050906011407060213090f1506091a0f1201031b0515090907020a0c180f02040303020a02061c110307030510061b02060f030406051e0106 70
    0xc01c00105203000c0000c17440520317002050300348903500b403007105207920130028203203401c0e03c01080315803031481d2041c0080507101d60303408124002000010000c0800034043c110052150400220201c40246550074200c2c4880d6410407002421314040c17940d2404644010101e0588141c003582c0072031080d44031155500d101681040303000c074202c00701c000d4680610700401503540c0a41c2542605825a1007075004648101c0c410300304201c00c0d80c0c13900126020580300341d034955540d80b01d042050703141031030700d6034020824000d071100071503078100c582500b84400102010038000745151581c01412481070f8000034005810088180002d818404010003800000602800182002003840750403600e00000c54031040200005121030340d0ba05014558100d00c4540c84101e9492070401c0c00351441000400d26628440b2090004047d5500d541c2a6080c0c110701040856076842c1c185481d100400044489000349a148401050041e0350101c07a24103a0350b9a0711207403111207898800051629a860001d0b03035030028 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 665139163 1250 665137913 665137927
    0x5160914010c020a031101092301140705010c120b150711150304030503150108091506150c0c0103181a0a0207080d050f07032c07150c020910030803041403 68
    0xb0200307504002c60044400c00d00074106c1500041c5040b90710f6200b480004041300c002d8416002c40c418130009200242040c04840b00c598554188601600e8405040c551070f144000e00582d80014407142401c180c0001049500c0701c04003002a43d1810246c00810f10302c05102c00c0000271002c480700c00d8003400041090014014504003004560300881d4214005040807003800b03500048103180e048618024240745180c0c0c038004103090f44e50701e80e11148440c072007142c0e0b000c40d06d0b64443c1c1042c40c0a08440449540e6140740004210703a4030340000f462140060300e4581c40325a000c80042d9405030466100c00101d41040c03a803440c0f030210140c0503051400c21a401c10038003000640c4d000040480c281a4603002c50b03140b0303286081651241c0028440424581080795800c090545031100c0b20401c1c201d0352000d00000250559685480c03032941100d084801c000705c0d140b0082c8d8010320311a02c124401c4408006599500d5032a12408106100044c8090000d101103800200c1c800001d90b00041c85904585c14011 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 665140413 1250 665139163 665139169
    0x307030204120f02032419020912070f09060303140a031401092408190f0230030f0301051002010b1e0915031c0c05070f0905160914010c02 61
    0x1042c0100701c80c4049800302120860800b44000203c000c800925800701c0030000648195220380200811000c0503c070403034032801c1d0a9070341070340c0d020302c40580801030207a410011155900001e0040540c0349051a400182101482c0604804e1705c0d41a0ba59401d000c0d40107001d032030340f500700340750303a4040c5511803445402110314001c42500074034110360042821140200365101031182c0341c200340f041000084003400180000203250900342113148640c61140402e013400404c070b00a072000294405c1c1510714130800d201800c654100b200e94106050b180000c40601a15a00e100d10f0030000c03489a4184010003c40c40c00190010241c0340038000411440c00e080002840a082440c5584040e0b100c1001d603200740c20500171003580020154204400c5e8899200000d0f60384400c10300050844420a0f003c03c0c4480c07103032800301da0090b880021181800e45860100e8001055409031420082c50240082c40101011181c26106a550345401800c03e08210010003555619250681401107044039080140c03 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 665141663 1250 665140413 665140439
    0x40c030b072106151d0d03030204080d020c0a0605030601050d1506020f070b070b0603120c03071109040b010303030f0b0a09061a0f031603090803040b0405120a0507080307030204 78
    0x1078103554165140324450003440500301000d05541049203003003070511840c4101140e0303003803400f085d080116800c107846100000441c0c8050f6580e401401c0d04080404064041c1c01070006c1d904044203030740c030403001120101d94656010b81c03030a0f40200702400c1004511b0007040215000380061410b01d140a1824103910b0565014000703081c00c143c20784004205482d03041c0484000e024400c0040c15545150022055090042d0f01001c2c111041d440003189040e5000c000c1c07101005481c00354240c647c0002c14001d41c40742c00121050f10300e0b405000c0104210b25042e1201c1d482258410032690442e421610110010319500b100f240c00705540e5407400340c03560b5483c04000c00a19110401044040c01c01e03545081000c441e00d400c4d01d588405000451419581209807035200890050848104142020440140c0a103100182c14a00000180b0040c8000c40482300c5c4224001c1c000c4804107038040c001e03543d1a100b0440340d00c0026030140304150000b94020003c540000e0300349005800e2981310715600100f5 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 665142913 1250 665141663 665141671
    0x1030b01050705010c0c03020d2607030204080d020c1309030203070b040602090d0f12052703030d1a090c0306031e01110307080106110c0d081e040902040509010503190209040c030b 79
    0xc100100291820076504000c9103002c5112761a0000300c0000c0311322565600700202003980e004401000019400d2880399040e0750060101900711418510048400b03034980300601e0000e4001c1c0f03407101c00c1c1000c4c4407560040d9104207602d0344c02180351a48988911100d460b000c3c0c0115070f0980c080000c0c03120b136941c018001d110700307005011550040b00546480c251b0340c580304030484288032003446400034400d44000c900d4801c400350760b0801c00ca10070100c00a811440b50740d500c03510301850061010864103d06020480e5408103817200c1c01181c40e5a05c094115000403995964140e02040140b20100c035000960700b0702088080000c035400150101071003a0b60811201107000813182d000401009602c07850602002c61050b0151051003c0100455500c07246000c01910302c40d00003a911094090386640401c0122120300c1040d103547d1100000f00c007035403142c4140c9218000510000c0780354500821841c600da8421041e00d51006101d5090100000008205403180d02c0c0c4000d0020124011100d500c0c1700e = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 665144163 1250 665142913 665142917
    0x1b171c0c02010e15060f0d081201090204081006320603040503030402011d01020a080703050d110a141303020f0a080d0305040c080604020901090e01020408010f140711070501030b01050705010c 84
    0x8000c1e43c0092580303056440700b0031000c104628000d00030291a60303819112a2502a15104100e48407401c110000e0702c5100c00c00e0b060303500c0480c0000b4003d00d05602030416103141000396881c0303000c0310504078281c1d010341c0101c00e60f80112302a0380841a1040208241c03502414406034401c40c010f1001071559001141c00761110b0300000200811580d00c03044400c02b007100c0a100841d4041c106c40001c0d51120702100c003d00c0c450000440c6400d1501a2040c0e404110f0030250504c1144c401010400054004030304070404501c15443e07860440f000c01060b5441c0d40042540301000c1c2d0719680812000c240c3c4600d14a800c01c41400c408145145c0034400200141e0054401040906091400c400d01002e00d50144038030390811002d200060761001c1445d41107800000000c200040100249402440b550f44000629860000c0f002c8103103003107410402d0500e01c01001283e9a40e210001a50995900313000c0403e2500056000d014540c002d600c02841d02c1ca062410508000c5141d8517542106c0c140602c3d540 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 665145413 1250 665144163 665144171
    0x60913050a080d051f030b0601120e07080d050c0c06180907030e12160b060433050411040b0a09030f0f051c020c010305180a030f1b171c0c0201 63
    0x1071054894001d80d03401040d001c9045c103c50b040680078000412590100520405100700881d420340c2c822040a2451118068200709a010f41c2c600d11341d82d00c0c44c1d4801c50000f8001c03080e002020038011004e54020f602050081c204800c903001c1081010350214800114452102910081a4861140f4644140c1641d03c0010b05030054503034052038102d20170400d03080020200000b80d1500d40509003120324552008442515031110800a000752454001090900e10000001c5200400c200c1590240414840f0410b00d095120000e21040c2c4906a0806103104010001005000490001008201114908240074945079519074201d14420308098400d41e2552502000703002c0c00380113071b0f40c415218a80010840480c0080a5204c04114010b02d050580e10030000d600c0200c01415030780d03d0010901603c654907017a00e0f010f40101a95416000001e00e01c045281c0e000491941d0720a1143e040451062844001c400c9a1256889100040c180c440d0781240200c1144042c0520850f4403541e4001003 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 665146663 1250 665145413 665145427
    0x2010809070b0f1c06052107080d030207020405090c0603190b06070c0302040b03012a022b090608060a1a190206011e0e0705071a010e041514060913050a08 68
    0x3c4e89000340b0706001a83c0c40d1070070030b041001f030ba917034000d5915074182074003e45180c50500042905140351984220f40b18001c190400c0740c0e095059000f00b850620841d020009600d07004c036115503840c10035810350382203c020030101d44d20728080401e0317402c43c020802c070209010b5034001c003203075450300195000c40781c0d440f010b6014011460240550b81c40303c03074194020084000c01c611290050751000510070910141c0c0c41d8080704a5100340010031801d0780b904c0c60790690207024404211962400060200041d4201c680440c01070701c100d00d60742c001c1d4070040242c550f40e414110b040c5050141c040207901d966404000a000345071070900d04460340c0c0b0294028003110b40c9011541004103190074421079116021700c0e024041c9450700d203003640d00103d20703150a0b41c4a01d81440c3c00300103035852507070080034001c000000144035882e0014440c4110f106007011003492124041000686010540241086901c2c0c00000c0c0b96041003441142d0080c80725400190305d086c562035060034500c0001003640c1c01e050000f03c00c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 665147913 1250 665146663 665146687
    0x20619050409050906091e07080a0b040b1b09100306150f09120201020709021602090133080406110f1206120307020102030301090b0a0905070215070203041202010809070b0f 76
    0x542d92140c59003000d0201031401c0090682c6914035401607a146070310381281c54040d030761f0800000d00a00500e10442e007103841c45050141103400300b02c83c1150300400304000200500c9059210300c5c81c410003000000d080c28105000c00c481c089801003100201035030b6000001c0c0e500300b011611b060084031307074849500142441100415482c415000358690140383c100000040c1da00295030811945000b0006842c1d94014000c98000b0b0130b80e180c041d502c40110b40001c40d80000b00c05404039002c2c40401c0d0386080501d20545080018914100000032404000019011986c40d800060b045a680c7c80d040707182041c0b140810180b0f402c40c03200d10802d8031401040005030700f80b003d200e60784604494015414101170b035000035501d1005004900515031190800100c50311221200400b07403903850b41c00e000629001310000e56500e1040000500903454202042055002204a03403c1d92003c10948882c108240c005461400000e091000d0521505000045151a210191000c0c0c3c2c00d8100e0320b9a922065064 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 665149163 1250 665147913 665147921
    0x1207050d11180a0c080a23150307060f020d080c040902090307091802040b030708070612111c0c090e0c0c1e06090d030507020601050f011b0303020d06090209030a0f020619050409 78
    0x78440e6245407c103044055283e00c2e5842ea0501105200759050b0b598103180515691640d052094140c171601138082007064028003440110061542154892054005c046813910340c296036a80c00500e003000103000500450300142841c92007d011180ca0030760f02c1d2115400c44810220018041209250007411480c19004800c01290300b100148200350500c040e10b512410248a54002c1c040d0443c004c0c1c80140680d001142e50105c00c110072901c0b0240380410704946001010314900a40c94800300b0905103018007210001d443c06500c825000383c6e1407262201c260f910140d4501c02c0d51140c08180c031109a00c00c1c1441d100c00c00054003401d0181044d0700041c0c5071110300b000c0a0189400e0004003d202c690002d420750440c0c1e01120f1211103400c0590040c0c41d66021562645030300d54501c0040028160941c00074080000030070010001c00f035450400c10101c0c0620041d41e6490b030000360000d00421394204100071800c1c00100640d140000411072242c2506c080d146443c007003040414100a0750f0990b1203 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 665150413 1250 665149163 665149171
    0xe01051813150e06030d0c2415090e0a02100302090a12020102240a0902060702030615030c01021b040507090e0103060603030e060304052d011a1207050d11180a0c08 72
    0x10305070024186400042c0e211900c0703148001c05c008400203002c0170320251440f07894000745c07a51741411238034110f142940083c0405000d690003030f60380d109000802c4030703c9104041d00604c601014081c00c0d50240e003007200d48144003441d8001c168080c40144400c5e0303100590f00006021011b41101c0c8891b40d40b00290401d111a040650f1104c80c011084640c1e006407001c459020071101c0000030002c1092000074003a008070380d000380d014441c0c18100601a107504080302d0030a4811030031203508007064001247d43c3c803e51100d040d00004008415022400c1c541c102681122090805614542d224550658405001da01c169690360b00d0301001c00a168001026052041080d201c0702c0c40c40ca070030b44900d50358448c0140d903080f0781c40e11101c480c003680c480c621032030014200c003000a00c80003020001280c2503d50240059101c1da90f00380100d5040f1000040e86000c03280090302c068010344d02901c5403c038002003a12519004042c1c0c0311845180841244010703c1000801c500142c00c940e9940018000c800c028 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 665151663 1250 665150413 665150429
    0x10030603021f08011401120e01020901031a030a1509291003020f09060f1e12010c02150c1912050609151207080615180105010e0105181315 61
    0x16008042d50303070711400c0302d030660701c0c2c104e22100c4030300001004998114800b00d440048515001d4188003004041d0014810800242c2c1c060040d21b080d0b8002030400c0c0040c40605505030b22a04e00480081c1c1c07150144e0b083d0500c502c500103030846080d10b488404035003d40105505013132201c1502403030694248150742226249662039040d82c1140c0c04500044068004584034034410707800681151344008001701c000601501d0008401c40c4109402c19000307804040502c6501c0c0c14907500340740c880521a203500503e0719401068800c8202c0595201c52002074103180d20500104140e0440d4040090010040a40d65070303109150948035034800d0459101901e0203104d1034180c0306200628039100c201451491086039094460204005c000349480d0740b43d4032a04880c0034480400c0b001d01110000b15501034000d039801300f0001c0c6001e40741b80101c0c030240109404032340e51004944055203c0c0340908052100174101e05102840310001889810400f440d40751047c0d103949069116100e980e0220009203510b03 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 665152913 1250 665151663 665151709
    0xf060509010f080a09020d060b031506100305042901051c030f0311070507030510050c0304052509021309060b070b0103060f1107060203150904050a030c111003060302 73
    0x5400001c05860811100030200a860008640d9141c0c050b4030503000c80346e00030084100020b4503c1d08001820712000c02601c280598035003071804901c0d417440c0b0751040c00000c1c419254035042e8802030b4014040540242c079070b48030600c04602001e0704954214032161140260000e01d43c503103070802000c0a030088461508500410301d0300f00081d04000001207165240c01e000c10001e40107101e0151a004285c0d01801e984500c1d040042481004141600c1030100e001c024840756840c00b80c030300ca0f20701c000c1c0d40041c0103502c80100d0700702d00103038100407080c00000e4510011240780d69001003c00c1c0e800404801450b405c80038800c0104032480e02c1800010901850f034281000e0840d102c06003018414407024150a40710320719051052201d03170000c40b00d00030581c0c440c1d8840101e810024003e40040394503401c00306000310080c049181c92034502d44501c1d4000011b02002c3d52690781103481c0e11010104850040303421109501c41d6541d4131a40e25061388a0743e0000b140c1780355004002c03002c0008124085507242d4 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 665154163 1250 665152913 665152927
    0x106053f0a06091a0303030a0c140d020c0601060e1e01140c0d080a05010810020c010b04090c09050604021303030e0a0e13061d2a04090c050306070305071e020f070305070f0605 77
    0x300550b23074000001d000c006403011201d2001d407080400c0001e01035140301d0001d948001d491840d030180840b08420821242182e80350242500c1d00e0307407070041e0140c0c0004085030307140b003003400d81460300700303080040c904803002e06c0302d00340012265009140317100d4403a0071440c1004000c2d94010140350340200b400000303002d0380d40352142d00c90f1501c4030139038a541c0703140c1c00151000c40320b40c00350829801031101401c20060441c850a2402e50444d460091443d2142400e0100d4503a10709030094030030044541501035182071840d030341500c00e170410200b1103030001e00a0000103081c1c610a20304501c1104020542c0f007540e1441c1c54a0001c6440003000f10001e42c1c00d5040d00200d503400021400080e007420380d882040642031a000241c852401582d20741e0050a0941075410002125125012140c00f42c0c00c07198a901c800d12700b5016603008682d1200000c9490754a044d2401030300841c20903030b041600580790302d945920741840c101800354000382d94030f6200900401c0308280b01c441c840001c1100b490709a00b0444 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 665155413 1250 665154163 665154169
    0xf0708070912030903050f0106051e01020706030c0c05070b0406020d0203041409040515070309062322080403050c0f01090308031b0d0903020708060106053f0a06091a 73
    0x40c10303025001202c0155070304482094062003015010b075401400b1601e2060041d0b0140e40600723024064107026a1044a28861112840b41d1407540f800050300988071700b0b810410101d00a20300c1a124104000d54a014940410400d0100102030701c00d001c2d5450b070711810080043d03e0602c03240400305c219070040008001060003081044010b46046409802c1c544450400d1460010507050410940d10b40c0c03404d0080e41900342d8404180284a0300040c05100038040000000a5400c4083d01d04044c074103000030200a44d1a41c1100b50860442c0b01e1000c1c2826500c1d071a1903074209800485541d40194103400552419100f00e406889091a0540d0840d0940e0360b0720045010141040c0d8158038403140004614048805483c0c104020b54010041c61101f41070080d41c1e0300061040c0f800354001c1c0400868024460001c50340070702641e00d40c40340c0d00c54182c00c1c1c4003d1031060810640c501840000454541944040e44600807806120045a1242020940c03000c40301e248815074444c60704445c41003e992 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 665156663 1250 665155413 665155427
    0x81606110412080d0b12210c060f040623010e0f010f0909050307020409080307030c09080a030e0a030203060705030412050a14090f090108011d010603030c080c12030a02030f070807 79
    0x20f6440003c0c01e0715085410481809461682d0300564413020a455500010350001889400b00e41d082c0303290300c051214059070462a100b4035910b49035030b40207000041c448510303840702141c1003403040c5000076131171072810420000010151502602e00014100400c41100080c601c0d54000304041540c90142d4502010526080c0d540d201c1c8024041d1582000f130140281482658003198024006000684180ca0140d40d83d900865460b4046440c0806518403144200d125200340d883c0000104621602600d003981c20841c00e0f501c3d82d5100c2c11001010006860500c0040d011b0642510303500d1f200d0403c1d1900d00c02c50029280914100301b4240300701000c0d668080e2a20803032044c1c84801070f550303000d03a03004620881c3e201000c0c00e41007c008070000540400c1503000d48080713040030240c060982d0449002d1070070f80f5920312002d00040d9140b0140c0d004a002840188480842c001c100c0f07100400215072202c041e0000c0310f04401165000c01000070400c0d0040d911a40aa02490810b010f40f8010700c01601c01 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 665157913 1250 665156663 665156699
    0x80111090904030309021f260c0904020d1803110105070504050f030f0d020c12010b030d140d0e0709051f09051b03160e06030c040b0310030816061104 66
    0x1c510240218090500a03485040f0558001d04003111030030381104504c0740c3d016410b05d6040000c035400c0b000b030009480301035195002d10407200550159282c40010b112690081403503a40e105600b00004505179820344604a107886119056000d000004e04000d0802c580000900c2c140307034100b0040140c942d41c403400726005d90344215141c000380e4442d500800e140044003950709040f07114881202c07407142e8002660b0318130b4820441b00e100803026503001f0b180c00c1e54500c184e19178156209540c0b03003642902500c103e04100c00202d005a007031034031094a0401347c42440503882455002900148200b00c0d032130141e00e601180032554881c8e0020088480e1459884030f00c1002c0205980f240402c006241840510062110324100b0680301d052181038104119036070480c400100d058401d19070483c1c100030003540d101b07001d50026541440d180c40100710250f8002001d003400c2280710100440014001d0001e40080c042e81d0541c2ca1402d211880c0510840f94445601051548140410003103a01d4420002000c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 665159163 1250 665157913 665157919
    0xc0510050703061e1e03030518030f07030f0203121216050c0102041e06110d0e0411041d010602030c0c280e150607032c03060106051308011109 63
    0x40e503250700d0124000e02d501d402c03103028070049000103a035070801030340b82c07006860f03103a10304007040d44c1c0c01201c81e1461402444000c002c40d2003480036903100d0132201584440e61402030286c8002901003a101c50501126800072108550424600e00640c101005158080701c2c038080001e2910700003407580c03040c05034010200800e410014405c2218148600142d84200c6a45d4000359161902d030500748040d00580601d106c1048041c0c400003803101c0c45180007039002440e06011300301d6001801d03c1210324003000791601c0c0e0820f403101514050f2014040060000303010b4850441031030040c0000c0c014000c90306900c100304640c0284244001c1e00d002168840c02e480e000c6540d240b020805e40c1998001008100c105110544a0312002446002000d607040c400d245030825118414846810403c1070b01600d80041c000820034070100400740c522000010301041d0078000180250426000680b07440d40036045000060004103101c004039640440e408050010b003c02485070801c03444048516006181c2e40c0c80c8 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 665160413 1250 665159163 665159171
    0xf1e020a0b1b03191704020604030f0512070818190909060f06120203120a080406090f0f2d0b07051308010f050121051234030206070c0510 61
    0xc000b80000604100c0c003850b8054070340b6500e01404c00b50051510215210224003426481c05880b4104000395101e03d50080c50076042c141103031110540d02000c2c42045402d0320403090b007119041ca90401030550a481a40745982e1111440510140c03441f803084180d0203603100e40c180c8070030f0820380303c505130030f0307400203500001e02e6016030030a100070701201e590044004c0c0c503008021804200400c10401e60b140280c1c1160b242012050030000350f80f06a008560000c0c8110303001c100080d0a6410107141d01c3d00980b900c03110f2010644403201c1104042008a03502000959401421005008454410f04840410080011082c2c035040040103004110008100c400949040e8080d1504504009012203400070030a004400b0200c07001450207000d0f4840080328940d810407040c22007550002c1c115448805051380c000c4688058a26411a00e55645074a100686282480c0b860300b2617840a00740c59100a08040701504000c2c0c149030024201c0c00400c108119600081200003070100503101d0b543c00002 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 665161663 1250 665160413 665160427
    0x1208090304091104050a062a0807051006030204060f060c2907080a1407020d0804020102011d0709060e0f010303181203020309150a0906030f14040f1e020a0b 69
    0x80c210300c281e401144280345004610345004068402401c182e51007507641c01c21540d1103030001d444aa040d0701000748a1040c0080d5032a212a40386580801d040c480d01001c0d05225840d59a58101030b081c10514041e00e81e200310800c2035180074054080101100c09514544a0800c00000d20041c5006030192800080a448045c5844960a0b00c0c42030004581040740b030741803014004115040544950301c48a01b081700100e0340e030501d50795403409a81f40c0e40007800b0300101400140c0c0c107028005c1007a03042d035580e000c020512032840d0502c0e9080c1e054280c0501562814400c1c0402124515000403c60440c1001002030030008080524152500741c10024038aa00000846089a4a40e0403059240d481c2c80040400c168000028044c660b504a0f04620000d00b241003c10b51409820b0101000800c038140030018035000b940301c40c01d01c0e10660400b0808170080c01d480000d0316002d0300c04941d1100310319009000e118420800f000b2000c11411841d50450990b00007445124043c025413010040014081e = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 665162913 1250 665161663 665161681
    0xf0e1510050a0539010c0e0604090e5205060304110d060f0c18060f030207061518020304050a230604050f0d020f1c09090203010b04050414041208 64
    0x4d4108201d0b40d402820750300c91540720141c0300c0034900381e07540710540c00c128281210328000c904011320100003824075820310345844c40c2a80a015a0f90013a0f005015156221400c1d04074000003c26904071710710b5010038100da110745418940142c0056607500d10200600701c0c102c04018880707030121001202d0550300c0340c64508101d1301e19050880c12560142e0755500714420000160080707845211440020089141c60300710540307003801400c0903c46411081003062050500602d80c5c2d0341c5654403450010306040081c2d0712141100c80a202d0100c403121480010400100c06005070b040c486500242036080d81483d0741d4540c1e940b0b034403210061900d2804548001d200a0100542e40404820000c803990350602d0300344141c5800e20072914014a01503464010491800024208a054010030081900e090307104022180c0c0d0503044100d17000c00c00707c02c2001401044030300195000c1d100c0440d840d41d4491508080004a0b2698050740f00c0e2540e0410030070000c00e1071030303072100300003007041c1440c1100765509590 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 665164163 1250 665162913 665162947
    0x1302030715170a1427160e1617043e1002060612160305060f01050d030507111903080d1104081207020a0f0e1510050a05 53
    0x2055100c2101a901101c50303590001c0040c140700c8041d8040551621801c8583c0181d5155408965000d0a0312000c1241071200b182c0b02e5084107a9481010020000003884c0750900214075005042d1450284040c4031104858141c030b9000190041071901e61901d001010389200761116074019814400c40000301802400c00030030403081a030303d26020041600158035901e0b1203030740050030183c106c00d015041c000d0401c2c078000c140922003600246420394941040081d00079405049503050b0050703852850b184000000000095031040c6c002c1c01d298034010703034840001d031070591249100b003a0300c500401c0465001400c54030400d07000f40032540c4840100000c5600000300b080c12a03034805114000000f4810b090000c1d03c8048074006082c82074410403030300c00400340107501580d081500704c010308440d48021600144120f41c030245c1407a501036031f14041e1030107240c0b050b03000392170280c5500d0401c400041c1c480c10b1059045012030303802521200d0098010080d00880c0c107080e05100f400211020b0310545580 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 665165413 1250 665164163 665164169
    0x81f090f0b0c130602011a0103060605270d050f0c06090d11240a0305010b040b0406050a020c040204170f0f0d030e0709090606030b0c160b040201031506050915040e13020307 76
    0x240f50400b907659000d000303009000700c05241c03a00c1c1003180210850f030340c0710b4000d500c00c5070142c0c2c3c0c4090904e4070059228628550400364520783c003030b010300740c0300507600e809403c2d58000c0d004a0203010740031000700c00581040c1600350700b2842100300b042454020740d81d0251907080d440d000101e610b15882d5410106841040602d601049a0038500d8034640c110b0540d0000d010000056400380020b990740c0e4414021170107035015000110310b041c042071105610a8001d0803003c42c10b4811038001041c4800032404a0303100303802c000d540760700703c0c088014082002c04c40b0301807003c2c81c5c1d4018600d503041c3c11165500d403201d8560040405803544080005088208140c0c0064000380c0d8080040a06520b0620010109403204540c1000220001040c0e20088015101022401e0f210000c119106031b840c980c0981c00144101d050544c0d0300c0c44581e40c0c89400c9200e0340500380b545c03100da54448055080000c2c14841c1c001c2c001189a0030403050220b6400031000c0b0750041c1c08040701c05010103107440005e040c444260 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 665166663 1250 665165413 665165437
    0x80703110a1212051602090406021e0315150d0501080c040605061602041113080309010806011805090a11032e030f150e0d03060f1203201006081f090f0b0c 68
    0x102072009202d5270707a0080107090328112034801054416581d8030781902080768407000c0c6142c100640f900354142002e6195004130051946440d1401d03000c9100d0490f01c00303030000380703d50340030180005081c180f51040310050a01140c000e0b0601400c4a103006d120380403100700a00864a900d540300303070030075203e05a60b6032910340084807810380d4907104d103160f0b260032001ca5140045c8610000ca00e041d4051462459034a0300c0c80d14505201d0708207401d10211b01006405884119542d8255601081000340910b00400b40e2442040c0b81e00018000c02c5000240390350304402e80d121000003040010310300080310682940c4594460260701c01281c1040c001c090195012665000e071070112502203038158043d07415610740a416050040e1580031924000180940003004900f12070a2040180c204071020703005003203540e04031103001003451544019609640d100d902c4a80c4110218a140d03201c0f40d0f6060b44440c9804010899001c1a072130310504140d0921014248104c0007000c50a4004114111012404a0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 665167913 1250 665166663 665166679
    0x13060c02330d09060614060301030305031021030e0405243d030c090608150a121a04031b0807060603080319150b0a09080703110a1212051602 62
    0x101c1e00c0b801c0a8403e008007214201c1c80c100b00421403405904c40d451040f140541180c0c1542c0c00c503a02030340c050380003400054105545a40024810a08480b2207521105803c24000d2100c0c9625004d04a402d11a410a01c030300e0074581000800f01c0441500502100c50340004001641c001c1c01160a03240e40f070200ca05015015400340310245119800003158000d480302c50070410300b03070800c22022a20403815440010300402c00808c60303c0e20581d106a040f6208880100e9100140000641035252551140903040c00000300f41c0300b48043d910004104401c0c105203403016142c25a80244410720810380250515207800c0614180301e1031506550446a0080c0d040240c0c9850342410b87d0f16030011590400240340428100010039002d000300000741c60b00750305c0d050130701c0d04002d02140a500000301c41c008011810200040e501c1d0700300003c1c002140155004130900f420001400500c1c0c3c0076412003140700032012100f00010b00c075000c0042965803146803054440c640020605400000d655001e9800460 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 665169163 1250 665167913 665167927
    0x1b05220b0c011e0b0604030609080903010f05011509030812040312050411130c080c090102150a090c061103030415020c060f240d1b1a13060c0233 64
    0x55014501904008124007100e4800750030036419548100001e91700500c090000b080001d0036600903044591040c4ca105040540c43c1c0e0100742100c11903101091140d8460004110841c1e420b00d0207031846420b45014000c05083d13446491492103400e003284200200d1400207000e0620400d0f034800d100030194000c1c807440c00c0504101000c40743d100081c1c0c0c800d0465031172a002c0e0001c0ca2240c104240340c541c84400440e030320031054950940020010f603040d8040c2c00341c6658583c090002c164404d880342da00000741d240c140c3c01c1c07150940002f600031505014000709400740e043e1000040d2944154490071b445443c96001c1c1c1c03004041e005c0c8000f9862a44542020b11010408113a5442c0c81490700045034032060440340d05a1030f82819211040303070001085a0180e011480c0d10707400d2000c0e05150302049280580e58224100c111103081c0030590080c40100398807500b201c0c610fa5101c02000540391241000792586c00055104021403160000300702590395444440008007208084500710080c101d0702c81030 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 665170413 1250 665169163 665169187
    0xd03090302040b060309060a0b01050c012a030509060a090503120a0f0e071202060306062a0d030c0e06130e0703060906150e061305030313091b05220b 66
    0x61a000c101d1086003850200354075402e002c1c1c01e0b03900c00d42c244070060003103071589648070004200710b0707404604202c010024000e002100f4041c20340e911401c620092000305182082d28144041070700f00200b0141001c060040400d00002c54503004149007800050781000351034030f00c3c0740d1710442920f071240122880410080110355407101c0c600c01480281030018803507140540342c6603801c602804010540208440d0301600341038015603032041c0041c1c0340600d0108084842d0202650a4142c1440b9010343c00e05001a82c00900a170001442c00b42000c1c400200c20800184c8600340d51200140148000b040c802c600c00111a6850010040301c041c4030282c3c01d04032401000707401540200715850341041c0c00001d030300f452a1481148803566a56014400c16034900300b00d0315078482c1103900c0804a0000300890a980c06100800c80d00c0000c145030354259241c031162a068408010f0f001c003070701c0705400706001650342090440e02c84130740034907248403c0c50034098500202c07015034100c100d20110200340d000c1620 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 665171663 1250 665170413 665170427
    0x3102606180f01090506070c080904020d0207150c020d14370203030402090604110403060204090b040e0a020a260712060605030304030f020922050706090506040e04200d03 75
    0x2100d50070a54548100590003a400e89201440c001d00540c442800241001c2c401e0410301a03503403080030201d244c01040000902aa0000d040c4010501c0c0d0019191040040951340e2035801540c4601c1408140c00480010b52941e81040040f02403001c043c1040c2e90203080d14089818400e890300542d8003a0b1314845100c5011980952240b081c40310a00d400700fa030600000c2a13a214550041c2183c0e616a00c40c41488040e00c010240c06104440c240700100000d005800500040c103121140091444001400c01054444074079109007a40c00000b580005030b02c41c14840002e4400e40400010190800f03090b01d00400c40076045001d46002d14403001c10010581a640780380c4da40525814440d482e10f81d0704243d141e20461000070000340ba09008680181000c080c9264016008490303042110090034481c0d240c1d64014000f01d80c0c60300154020304c46142c011039058040d01c070660721a03080904101c100911520040e00240180c4541d9441e05640350b0b2143c1000124480545000c90100c114900a00a4 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 665172913 1250 665171663 665171701
    0x703080f070c2003070b0708180411090d11100903061a061e12041b06020c010212090d020a0308040e13030c0f030c240f0203102606 58
    0x600c01200c0496005445004800c0c40c058010704241d4400d140c0e80040005800581006034041c01407620003c2c1c0c03504107401500840d4040c0c1c5103203075550101e00203020180030152420f4852072900b203d51030b86440480690b0034039402034426415542282c1412801c030300e81504441e5124908c10340b01e0305850740c000094000c59200344c0044c802c105042c500c0c01c401c4540c1e0905160050010b100e40b4210100c41d901c410860403034180714034680000e581c58103200ea082283c0a844a51740c0d070503562601103a201403100202114400740c1103030f03128100002e44600d656031000d01c01d0880454088059550548140300260b8003c1401200a580380f4040000382c00500c40c1e24254000080000d001c4c00a10201e03e2000b076055686002001c025a55200c644c50101b0043e810441c07000c04690005480c6040c14103805003240c05c5844d805030f0194131000359004a01401c4030303180107200740440303585d020344044281e4910328000c04e0004c0d40d000d00c05804051854501c270f4030340300b444240003615001800603918 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 665174163 1250 665172913 665172931
    0x10c12210c2007210c1503090201020f0715030e100627111204061509150602070b03060609010c0501110301051002060423010603050a0b0f0f0c0406120e03070308 71
    0x1070700c1d4034000700325180c10300351044400c1464101c00108000c42400c868090780c034840e08141760040c0e107400c100900710701040d0260f0040390743c5a0105056603010084000e900154000903c0554202404078020540c200e640c03106050f19603030454130050080c00807008c4000d02c1502041440e685400c0701805200103080f4070000b4016550070040d0005034014040f4064448419500c0c05050f50202e60201c03070f004105641880d6120041c401c071100b40310400c1300030400b82c8008600f075a12a8080b00541205a2103607055500481d400c1105194001c1503030ba104004859041d05c0f012402c0c01650349004e400390040855113440d15078000c5a0090014505039141174038000c4421206000a9a403580c1c1510050324524581101d4403000209100041c102c07412200081074041d502da581c41e1411502003c2240c41400740020040440341040c921548840c0201d110007640c00c000e0701400161040c2d008031020007502100c1032100f00100d03007009003c420b003841101e42d50601810014081402038070a900 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 665175413 1250 665174163 665174207
    0x1318060e16080112111e0103061d0a09020105040e0c18060903100905011d011a030c0a031506030f1109010503031804091a040c0e0105010c12210c 64
    0x1000e40307070040509030000a440d02500d503420407100d5036110034010011644010400003c4420362030710100d40100011402d001c400b0340f00c510002400f541d105402190300300c1d07107040f0110341e85040c64001d590060703a6402c0024401030103000403503062049402c400101c0303201c041440310b044a01002000070401c6080d1020300100000108142442110129641940102046403040030303140d01001d5084d00c0b40d40005420711003080312200e107a07038086240d05640d40d201c4408a2000d4841035540a149049001d8210005120001850062140800b61140e2001004c4c07040d40c2007203601203c00b40d5040004c4071402d1426140085d52408120f510600812148000251604000050f6403034039140348001442c482000c814000103041800c0c0560380c0d400e5110070008240940042e9070300807801415542c0760b1900302108002e1050041c1d00c40c604005148070108041516440714100c04902132400c0302020341544001c0c50004403401800911510300321b51201d40b140c000085160110154000c14 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 665176663 1250 665175413 665175421
    0x8030315010801062f120a1d030a0305070303060e0103080c1005010f051003061806080f0a05060c0a030b040c05090f0103110a05160b0a1a0d0c09021318060e 69
    0x142d8540080c03280b0350124241d5280c40710b000340c0354404001c0101c1507010884035a04003090b114038010100c50010054040090302c0032019500c0b80d0541c0e094000c178104200001210004aa0307200f0f090740003d42004408902142058420f40109004041c0d43c407103d18503503141d0404034002d40c01854500900c0c401d10041e60038848082c05098101c4001120526080713141c0780c103210218490745620703801c140d9150008942600c840310301c10312803070004038006516800d0080244c0380c6944001901d401b940044c214a0010300f0025510354007107202c4403450b80b12040d400e400d4025103a612400c9600500b8a0f00880300340d41e2200140218070000c60f542609170503c08010341c100c81c01c090344400e5a80040106c0b03065a405040241424802e528100c4460700285e10340d4083c100d82a2000c089441c2c503002444900c51108000f8010b101d81100c8100b011100c5580b024075800302842422021900420518100d00b40c100d0178000402c41e030202c2500000c900d4449400918007402440304401030b08000c5 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 665177913 1250 665176663 665176667
    0x708070f031701031b0e1b0901260924040204021312030c03030617032709010e01050907050f070b1504020c0105060306070906052b020f19110a14070308040803031501 73
    0x1140c082c008035000710076468140d554213156940400e48a40c1800ad40e01c404150703041c1c00c2c09000c0f145258104e4801040d00b00103900310b040840d022511001c143c0d0104030b403010006e0015001b500154101c07001070765100290380302c0f880344416a018495441c01402c9440903d40c010b180e020070a40300340c0e401c000d00d54035561031214151080303001008640c020302044148846d07189a0741100740104049a1001104400041180700260049503041c0d0710752004000e01d041001c0c0c0706800c04200d060490619002011440c0107028810002c0d1007402e00e00041600305001c3e50781c0b0540021702030402e6544001e0140228081c001c2560301c02c2c000c0c41120300150040e4480c07a049402c1d26002e80d101d51034011440a4080b80b5010108007001c5000e024625810705040c80c4000c03c01c0c0c540f2511401c1e15500310041001280d02841080818003444a046c50001c540100e414150160b20540d00a03100304847c075007c0c90286103410040c400440000d000c29041c9000010b140b044c20881c82034205c02d4806001 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 665179163 1250 665177913 665177939
    0xa0f020301080105061023180303130906050609010e1c05100209011403040b0f0a0b03011a03060609060a090207050f0307050106051c03020c01081f1e05060708070f031701031b 77
    0x401010340c04481d801e07220810140010540c01801c0108030b00c01c08000d2300000c1c1198000d890030700b40881d22131002c01c281031150144034002d00c000c4800f0f50803c1c80140c0081d00d4800305040031841b62042c16041d2440481f118581c7d160942c024003111000c1e200c44001c00000d6000011141c0410444022010701f041040200d07440780c3c0c1d000c83c81c145aa2038041e20541c10703c0002d050180802e48038250750410b40c50134840c000f0110302e6258000160040c82c0141402c100340506403d015078104400c220180e1104440c200480703d003101c0040e034520071424580e09001081110f0403040c080051b00b2400d001054010805403a42110260b100188030080407074085200d0310001d01580010400c0c404560007184400e0340200c041401041140e0740c245510310320f44c8150810b003131440196109013040c00a8492040162609955092904503a91112000c80c014520020155842c10442d0310405108451120b00642258001412541c491030f210250f07049451414020784052040000d4483c0d0f0510 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 665180413 1250 665179163 665179187
    0x20319050610030207030c0b07021513020d08090109030c030605060a1508150a08061905150a1401050408030d050103050c06250c0f0f08011103041a0a0f0203010801050610 75
    0xc01030010710307480b18096002c2d40281d00e0076414440078210040c04549000555440782c017007580940096100002207004900d0040c003030401c103a01348441c2c0f00068417225118151550441c25881e11100c0000048443c05482d8100611806010030b0000070880c0a820040c06a10300b291411041911940314020201504d1003a4001440320f00110f50300800b901c00d134400240b40603208828158440481900d170450590f44004644421524402c20303280b02e120301600024400581042e0351070758030000b9502d2100307003c2d20440c54403289008403940e02600803600140304480c107603500c0d040102c0100307000340340920090710a802140c1070300c05546440c100b10341c080e0038025a20880c00780804854082031803100d03411140005034240108218849030000310051080104440b001303418803070f125080d92600e02d00d1445d542000e005100005801642090100c1034820000031943e45090340200500020074076001094070010000c2160081900014071540c42a40c89854800030204c045401d04440a = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 665181663 1250 665180413 665180419
    0x11e140408160c120f0b0c03070f120902041103100b0405060d1e021303051212070f020c0a09060e0f060109060513090501080f0d0e0607060c020a050604060203190506 73
    0x5180e441c070b8007084100458901409040b04184d440307060900c0e6135000c800081e0748000191020f88200008540c0c4103034070800f4801e015046d03080503000601141d0707681d04c01405000d00300d0b8013100019a242d110341001d98000704103005c0c00d580e180785e041e020f0b0304c10f0780e0318444c640e00345401144041d81c0c602103078104d840c003400c02440c1c2440c41700403d0042943c3c010741d400000049544424140d070b2400500100c880c903445c408940352a624101c0c2c0b4119069014042c14001840030050f81c408018044d82e000302c16041222901c09214812818400b002c41699032180c01e0010101d00c100c119030100d8240e8600d00003004181d100c20480025030f035000ca44150000b0300c1d082060100c01d04c118040c100072074514202e100f1603a141c2c440300b8280da000740c1120314950b0041c0c00d070741c17907030030080000c14540042410320080004021010803581d02c240c01002d00385a80303c61808124510800143c03d01070b400a0682d07840381031600d4540080d42c400d484421140d4621209600302d1000d52061500802c401 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 665182913 1250 665181663 665181667
    0x303050a1101090f0b10061704020f190801050f070e10030f0b13020705011107051513080a030c030f061d090a1e0210110a0f0c0503011e140408 63
    0x114004454184106007008400d54841440000007a45000c1a14920b44211420452440c011646204a44480c2c1c021401c00c100071200085e031009480c44141c01139019a07659a5040d00d40f00425040751400951900d19544040001190041903000c60b014407240180400d464071221401c41c3c40484c549052a8402c1c1c0303242c01c405140d402907200b00004900b41c4400300381091135800155580484100d0004107540015003141005800e200303200e03002d40300c410007606155003921074540c2c40340121207422074100c000011030b0f00c0b0540d1880e041d01e0b407176000700002e0380c85028440040c0541590290400070070700b0120343d411240e1040c010007082d44e9560b104003003030300c0c0c910f9021400c0d9100503015007080d015421a07600455010030100c6508400d400b581252018244180014010b04011100410215a508540c05400400d80003806078101840c2b0008661a05200381108040e520065140d0320300300d00c855000741520352540484420250030030047d020402000d441c05400c480040041000b = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 665184163 1250 665182913 665182927
    0x20106121a0601090b04240c0b0a05091906090b0117100506060c062d0c03070c050106081905150f040818030313080d0e01080a0207050c03030304080c060709030305 72
    0xda040150b4485014076154110325a60200c401c3e90340d1064120507028040d010900200124422458001a10910f0a4100714403151074035150900301074540e51200e0b03110408910348005c10410f0105403605100545d0702202103150400003041c0152045071015258400010150101c2d020b030784154400002901c07820070f010410300020403004280c950b00403002c0c003d010b200c090130003203988030b484031041e81d4171080408080714080d098980c2d0460801401602003106000746803040d41e411072406d0608084030031151034594090b15840d0000b90a44c445c09409030440149141c404004902800a954298404804800460034100c482c49540050140841c001440382801411058036143d44d003c041d4000c43d000038203540c070075040c14044114001051201d004203000003980c121081c00d00005c003860110018205d40401060400e1065002c50341c10140141800940307045c0038000c05880d41c91138107107081c0180b90040b4104c500d0340d11030440001c1c2c02d6030203014200c0c02c2d2509031311070b00d08000b0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 665185413 1250 665184163 665184203
    0x1305012a0f0203072009011502030a0302031503060a0b0f09040c120516080610050603060906130207081c1b05031f05030d0c02040c050a09030204020708070b040b01030302010612 78
    0x4500e6907032108503c4100010004145000b8034142d914031089651800c210328030082001180068000c40c9001456101507070b640ba800200300d90302c403044c0b4200580c0784d54481f0031a0100302c1c030000450f0b0b0940135040030015010f04560014440e240c0855000c1d0344440c80d2010b1104c1d07040704a500a2404c5410841801081c240b0940d41d5081d40c403c40031202c0310380555414520407100b0383e008007515402142840b2442e54101d0260b80941025904142140342003000038601080203803585020b00c030840419003c0c581a501140ca400c6d0304070581c940d451004900341c10070342d1002c1110490240c035100348a811020702007000145003030280c0c1e0b1141140c45091248072401c40c286140740c07000d8000c500018450718140000c400c464425122503000c0e22060051006071410400580100601001004c400c00d40000d46241929010f8070300588469042c60010440d04c1201da02900301e50014041000300088400704074140c2e4800c2d4001c0c40000d0741d075141c03079510342940c0d82c0091000100c0302c2c0c19003200f1 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 665186663 1250 665185413 665185427
    0xa0507141309081306020c010e060703120902240702040605040204060801090b03010f0c23040b0a110c090f0103060605031f0207050a0819230f0d06030b1305012a 71
    0x16000701011450004060040c0070384c540b8070350046001d0317008131004203410f60300320000006901080c0d400500c1c03da8660780c014050041c1846403035805030f807a1003200a54031380804400c80b11503807006039940400c0c03100402402e6004480c1c102c0c0300700c2c108800420f19040038001e560403518281c946c100d09900b4000510041e184601456400d90350354a00c1c0441ea10300e50007100315030341d0191240540445110300041d90185080760f02003000004000400080d0302e035804460b01607805180405042284c01001030070102001c106590242118007130100c010b050490070780c100c0741300c0d203020030003070741d41d00b044c55141e41c80c4043c0c0110100d843c2d010700ba0f4406580d001010356601c100144c61104002c1d6503812010781000c40c0c10442e00706038003038030005150402042e60540c4e80401d0406c0c08a503090000307458910810f100b0032101040469204808611900001c0246501c1609010f45203448000e580500302001400e07101907003000144e84002505140e04500b05c041069a441d5948000d14159085 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 665187913 1250 665186663 665186681
    0xb03130605070507111801140a0806010906050a08010504020109060e0f18060f01080c09012102030c28080c0a0e060c0d030b01050a05180a050409050a05071413 70
    0x8510404181800154548207542c441d6009841d595114100d6044c240007800b113012160b8041d1041c02c0d03640c01c2c4400b911031114111b461014500c0143c000c0c1c800402e280320469031111103141314030000442c00220301c0d006101940c109032038003110b1342d40d01d401c498240c91050350082d000c034000c00801c0c00f544c0d202d0fa01310100c541c030280c100c80380382400307202140b101c43c00e02d03040004049022013480b0b19440e16042c844280902480d0105041c2002d0412040a100d0359142c1414400d84000d80d02d010012505030082031000900308549074905070301100402d81c44000407460b15860500c0e10710560320000700c40000c65180e03942c1c40d030340e0396602000c0c030110b0340c008030756001803180710152a541aa5114010040c0548040103400881100c103c0501a203445030149814010107000c8e080d075059201007502e6084070f021082e4043d002c400c0c3d010800013569070b0000b50304541468110401e210000802d43c030020311400413568444c1d41d4030514141c419041c039580351300075002c040d580c40d0906950032a403c0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 665189163 1250 665187913 665187931
    0xe070206011d06040b10020c120102070201020304050f01020c0a03030c170c030d0e010e01090602180f0d061a06160c05060301060e01050309100e100b0603070905040e0c0a0801021803070305070b03 86
    0x8108400000a1820620101b80c0c0005030301c079407514042130801c0c8c1418448004100d00035810103515074000303500ca00580c02098000c0c0c100d002d89400c02d030f2003085029040700001c4c0c0001d181640f20700700182040e003071600954018040c0b40d6100e04c207408071022604c6204266001d1401c1100304807400740a00500c00841c4801d41d00c0b1000d03039561880030700c111507495108000040e0b4603081d44031056004040c8810701441081212000b00103a1600b0703400802e60756100c000051402141000c3d810080c0340d4040c903541000000c5162101048484480106203000e16107606031030396030b03004108907444240603a400040b840080a2902d50181001d590000e0044c4140c9801818201001c03003150842da90031501c1d90b0010340d01030085140d40c8103501504070281c403400d16528252030050040c07600da10409002c0c0ea580c000c80d00080c0c005100e100c0b0319034802020700d4003403641c420819001c2d4000c0d0018020214104c0c48003c030b00e242c009256412290f212010b007200074035002641c0d50b2500000c1001d00 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 665190413 1250 665189163 665189171
    0xb0103080310170a17030606090d0f050a0308041e12050d06180c080702030403110d030309050610151b14100e0a1218170102071b0e070206011d0604 65
    0x20001040446803031000c4a0f80010440303079601d41803403c040112580001003030b44080082c85410340366101203842c10f680035600885910030901c0c2c590b1107060002400380c5213002e14582401055800380c100f500903405801049080315420115018007591a08020400c4110361441d40107240500060301d100b824008002400350307600ca14407000c02070a5451416507580e101059071056802080e09500035480c0e10041d8246811596140b02da2000810100e20408030113015500700b51203600300b410303100e500138107032401410054100301d4101c40754000c080425036a440031340c121521925000c03503c40020044403442c0080e5444021911050b0381000071240a480c0c8400f031040540e000d00000c1580d0000103005000c16801c006a4202e4140940d8003009034140d81c1c90650686e005600041d0344104c0c1c1a8089030078003030042070080c42103450041c1400000c10700c00c04100a010b14a808480c1d200841030305968854404036111002401406030050442c00c4004040c00c5042003140c0c81280608005 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 665191663 1250 665190413 665190419
    0x14041e05060f0604050c041a09041113050a08120316030e030f04230105070201030e010204170309040501061806030e2d210a05090a03020406060c03020f06040b0103080310 75
    0x390506404550550070b45000d4401e0010fa41081d00c05e150740840b2640c40305042504240103a03103003610b100d100f4030300c030803011a28070b8213039803194031100c04c144106010b00c0c1c5e240c841c403550700241d00081c8501ca20410045400041c030130030201c0c1480690080307030001031442e03560105014000e40041c415108043d41c0315011086408d08100034400d14083d80ca01c141c542d4540110b02c2d40701803c0d02d00d0108080640e600c119803e903000402c0e602e01e60350908010030a0021400c083d030083c010742d48903042101e4003048501c0e0b100300100c0107148078607040d502482241e80b0cc0e441521180700c0c18a4424034a1481201008941c1c80b17076119400050084055421218a08c01150000001d22425880078000b4003482c0c0d8000000304081c21304542c0c82c2c0c6a0110f541000c0643c003016018400f645c1c4203000d000902e80c9455035440301c10002840c0d0040c410800b02d920340000610807000a513044001d48079900300d0880107000001c03d1845a64003081240c04c40e820350f82c03095115080604184403c1d40401c00c04 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 665192913 1250 665191663 665191673
    0x1308040b120714030103030c0303111605070504050c0304140f0d121b050d1508030703020307020319210509100305150a0f260a0f0b0a14041e 62
    0x208010440300340041d8454104506980078250058030308018000080203061440c0c40c20019281140d416041111040300c0ea81410b401402c2c01c8250551510390000310785440c00c10780d00d03030030084034020011510030a49580030f12044400035610761111140c10320024002031200c101100c0c102c2100402d4800c00c8882124032840c1603000b81601010804907410000c00c44a68496000903012450403440e591060700b84c0605a813003010a6150110745a00303c400090300c424145100a110605c1220385e54121420300030b480386c0150104034824022880b0800780806c0281d140c0c002507070000016010300041c0900001080c016a102d01d0910805000044056442518079040c01001d600e000c1428504800040580c00e80c1444d1540b041c80d00c48400e00814070200c020708d0a032243c0401034440030980c0e40302503005024010b000342480c45444046d2040200840e000c0c1841d62061680000da07468484001c401c1d02d9503050b181d52441e240100140101d04059100c0c0c025503000012101100f15079110 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 665194163 1250 665192913 665192917
    0x219140a05120909090d0806090709120f050d020a0809040906060902120703061d0a050705040302130c121404020f01110118051603021806031e0c031002090609091308 73
    0x508110b00da0089040f04072401c09540b6580e100401c440a822804451031000d8170251700034141c18051004103000514190180303040340054240c01d8010b1119801300e142c4115600e1008404940e240580741d10307032540c240009450008103078001d1a179802c0501d191b090100a0950440c2070f40d20580310440010b10002d00c0c801001d054800c2002c1c1070036842c240c00068181c07200c2d0761150002d030201c03021004001a4900710260440340d112404510754580c580100c525004c1c0c0e03013000c0d50209190751903444040d4154443c0664000503102c5102818013080d207a4102c0f555844d40030308072000107000400601d000e42020300c0c00b00050406103400601e0318106401c4483c3c92000d142144205000c540602504210101c800034460b1448800d00c0d08641c04111500100c01b2816401c85a0b5000b00388190344c00d000e501c0c2c8130103000c81c050f0b0b42090b600c078415941d02e40b804511802070280c0204080758444e207008494982c880908a00d1507c54080b0130f0240d0628014a0b1100700b407c0d03019030070009616030b00 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 665195413 1250 665194163 665194183
    0x1e09030201060f090c02070b13050409080405041b020105070503041a060411040b07050c0a1505160b0a05071e1d011101020406080402130603051504020301020c1213060219140a05 78
    0x100080c0b400218201174a8010680c2190040c0c0c2c0e002d202c8240b43c0c40c9d41c00307225810740e24191008a008500c03413801c2040c1d8096a000913601905109000c40381420b03420502e000801740394000d0046e6200d49209507020b200948026203002069120090035480415401c1d4100c00042e000045080d00d100a00c0c2031030f0440d40151654a40025980f400d00c2010850050030b000c0c101c456901551400801480f044502c000312414484042440c22a4110416614a0703203500440c41c0011454069504c00050400300d030510003003040c880750100c2c04101e00b5440d0301611125101d00c50316940d03542004405500c01c802c2e642c10061010070784190403c0a001400c02006161034940060805204228104d0940343c440f41d451458840100046072000401002c00c03004030301e0301111510740340080384c0644142c074020340052052b0083c5060300c9040a0040000c24010311082005c43d80f43c0c4412a00e8000005440c4040103943c18801d010600404e12034007024001421204020784541e10f46060a0280d4 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 665196663 1250 665195413 665195429
    0x200309190321050a14090c04090201020709090c06032406080919051b0315040204050c090301091203050603010902150a050c060a06030201020d1119020f12011e1e09030201060f 77
    0x4044c03003040b201c1c0b40518141031903401d0307200850b80f514003001c0d595000311070301301031040381c0b02c200b0802503900034441d500140412090501c008801801c00704c96a01040c416540040d1902d07003d00c680700d9294000480120810028440c40380c500b140464244501501c20b82041c000c84080035100c004e10300e801d2103107600c01c1c80600540c5407a65140c907188110f68400034040d400011a05683c00044042950320950480d8001207a48610040300034034014040c0340c1d41c240d0310b009008000e000c0d10201c0780b00460455501403000d5983d0200341402c0c1c1d010f40c4802500080c0c15a0031211640c0aa07014001d0300b100e13481c04c0c500f00350556062901c0c001c826100e041000355100d109006559040c0882e034160081c1d4140a44511a407450b6103035156608640880140c10b051808011551119100261382e50001c254000b8030041a600500034189a030404017151100c0d031a03800e02610f1405481034200440d00b400c50b004010075a4480a0304840030200c0465507030350700111701550b0320b00140700901610 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 665197913 1250 665196663 665196671
    0xc020f0d11011103090715030b040c0206090c120a060908070c03140f1209120111040b210601050901050c010f091208090106140d0c08030d200309190321 67
    0x120000e42110703896103c0d00440030042041000442c000999242220611102c070181c2d4156641d044000f003030801070455001742015070007034074141e0008480b4010f003102000d40d0003030314005007004086031041c000c08255801104205012494070760240e5140c900400c00546010800e6450b5812043d0341c1d00229800c542000581c4c0001608200417501600040002d04586050909084450041c056128410808003100030f41c0d4260a400014008004000c52600c035600c0e49800c001039045a100c1e490006120224603100c401066080c034026601a15100c1c948007041c4011502c59010038403008440d0748915000d9011134052252482c0e0078050185a084c500011200800340306018000503c10381c1004d40074403032000300d00f0300b200c1608000c4071600e00c452101d01c2d0403a0040c007590710510850101042c021480c541507003101d06501d180250f01c0c0c1844103600f04036029408223849030b4429a100c800b601c41080ca05c00a40d1407514041e04001610026103038078144001403a090f000115522 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 665199163 1250 665197913 665197937
    0x13150303110307080412110a0b0405040c050708040603090c0e04050307020103052a09040609020d27031d0a080a050d0e01030b010203030a090305090a03030309120e0105030402040c020f0d 82
    0x4800703107100385020301c180618505240d90f141c042c40e50140d0b00a0110744000c805003c0100310308003015084068024001072049030391000c056941d6000f91040c00d0140703040225200e4028403600446504540c020251070400d820003d048004101d0030804070740209148802041401c9012a203d00c40c5100b40c00850380c80100b803000406480024003150080e1046241d02c06051400c04403000b103c0c50101c8040c0e0f12031703080b180002e0281c4019401a5069403000401132034220064016600f2030484030ba22245d01107010303030540d00c0005009005000550149020044070265003441071800c08020718030203043d40c4030f111a0b8181010640304490300d500c818000c1c80e146410030440c180c980e4090030204403580318180081d40f20b11000706902480c41c2d03076010b40300400d40220142c86a80c1e90151600c03080740c0e22072034050014001c940e01962201d103c000c000c0b51043c420090400f8145042e904c0c80d0564880381d00348400381c03949410917825400741340500305160000b0402000c1e035520b00c1e9503250300700034 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 665200413 1250 665199163 665199167
    0x150d080c0d030b0406050306060d0303180f050705180c030c0403020a060512010b0408191a01030308091002130b09010e1525050a021003110a0305070e09040c050f13150303 75
    0x85103c2010f40110305188040003140d034003240180e400340060307031804081c1166141c101c00038105900b1110207885004584170070700002d6400603011900c540112113801e5221020800c0c121400101c00c03566070001400503541d00860000f40d500403164a50003401d00d0b880e81e0004400e914550813040000b1000b241c0304001c1d4200d0480c0d58010041c2d401d4062038030b070504041d075448540c104010410018040e00711020001880c2c240c40f40b10210a404401c0e40d43c403454000c00c200c03010ba91040140c800e842031705c02621154404c807000802107440c0c004009281202c09000b903009490724a042c003140e440b01e80c0407a102d110300142c0c130082c0d40c8901a070300c240c40d10a10580c0d280201d5102c03694030300c589254001601c0001c081080700c0e01124801031a0306071a80403405894040c0b05400c60070400701c1d400c0e02181c1c264120500a0b241a00d69400e0364807400b0038440540750840c0d0140068417628070400160400105c140b46141d00588150690b9410404071030030340f405080a00c419042d040c008100b455 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 665201663 1250 665200413 665200421
    0xe01061119021c08040302040908031b0a020c090a0e0706051306030506030a170d0216110301090c06050a030605090108030c12040e0f18060405010603120512150d080c0d03 75
    0x3810941d160720440e14a40200320094241c40040c01038603180c80c480001c2c0103000302928000d5038001e00500c51203600d0b19016001e1340090722101140b070015100c1c0101c01d00d00c00b055401c241855401040d8440c002d504008513000c01070090305045603110152480c4450a203e840c001d4480c42e11810b6032034112401d800224040e0364001c1c000c0618010a002c110799011035400c01c0d1030303004130482c6801da04280020045104010030204442d100003503c1b6a8042c9a45c506a4198010003010844100e00b0040c1802d0b9070b40280000c0155540c0402440881e00560250a51245503d000510282c0b40c0c2e022034048502130f04540a0f0303a0000c07809421080041000e448002400e13004a810076203031501381c40600e100581001460554a00000e015650901d0340075004000c0c0e408481141c100ba08200d80249001c5c08242c420150101e00710400b00e000d241119440c0300440707540b0100b641d45c0d50788032030034880c010505903002050042e840003240300b030300c043c0c856001980041c0c120080c0545010f4205c0d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 665202913 1250 665201663 665201683
    0x818030c07051507031d0102190b10090603020f150d06140a06051201060c11090a1409070810050a18030f0305160c02010831030210050603030405190e010611 69
    0xf01d0070040c080000380c0c0b105507000700380c111511107202642c1d01c00040c2d041c804028500c04101d2080e00c80c0a00b4400e850010134000d182440284400340c1d03d42c80d207202501d005000283d0042c109a6060400b8200450070116000c10010f03031908220704080103206480555003e040e89841107401d0b0070380307880c001c808440100642d0400074a403003601401405114014131070401806240110384003400084910180d40c01c40042425100380fa001600703000908a031a00c161003000031400094400d02c0002d182e401399584440140f18071241d9001c03c0014200080c08c0f664030649a011844540785110341d00c0c045188280c9502a60702c803642c50080446400400300a02c621201606940654000c41040400c039020700c1c00d0035640d5039541c0e000c160740c8645015001c82c110044408070172003150301d02a540040c400e50030760314141c1c01344c42c07900155107055440a40c103400401c000c104624100e50011440c21a045454807c81d07555100b150b10300800364400004510144140c0700d690105001210356 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 665204163 1250 665202913 665202949
    0x1109090f070c170f0409050a0f05091b0d02060d02031f03020a030303020f0c0a0302010e1618150e0a050402010e0102030703020604150e0109060c0f1e0818030c0705 72
    0x518a04090002c2408842c500060b080c0c1128015035400c1e02070100803a0495901c0c0654182e0300c503924040c8200031f0008403151200140b814034404032003842409000d0060401c0c9004205022060b01110214140780f04044c0d480f4118020083c010f85400001e0b00203860307180001070300c0303141c1f00704400414040c550258101580485091005955000c400360030b50307400d07250060f12600c0c03a0030310700014401c50713803028054030030000044201a41500005010070215043e52105021804480c61800140c05402c604500c2c4420883c0100c032903510000360a0a1841e07a9508150f03154079186611700b082c6d401c059010703142c00401080d540c0000d641040000c003803000718501030803620000e40780d4030b0182004082d40c0300c0d2912060b1000c2903410080503010040c0081000811500c2c0000080050104500100758100144807245000e01e216000d041c002585500d80e15030030840c111044003005250410740704801c90061001c1100700301808508441c44020b00b905400c007400c00c044010503500004d2 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 665205413 1250 665204163 665204191
    0x6091803090e0702031c02040e1503100b030c100e060d0b040c0c08070b100f09020d050601020a03051905040f0801020a1e050d23100e0a18030c1401110909 68
    0x705940002180e06c03040048840e14080740c1d07044802c034040d00c0b4a501101742c40080d03809101c0300004c7d0009000000c0705c00c0301140c8940d00122a0802920049007800e54160010221224241414030212503c001c4500e48002d0715403070a0001805c80e044003190860880c0e0301c29040d19a401c140c400e00d25501c1d000d0a0042c2011420f40d28005e00380714601006020044138070120720380659482c0c490340580003640b00707007540a80303848040c4000c0d0000c0d55400161070800b404500039500100303c0c00c0207141c1690340d4610f00688030b1080704c07050a030b4020300c8042020130080002d561001c082510042c2c5100c0002690ba69040c8000400e031990500e8040d501c3c0d20f034a4624102e042d003000c2200d0038072900e108081030b030101c00306107444400d40c9a2104200c7c0c2684500f000b02c000040000f002c01c1d42d460007007950080e1600c0e0440d04c200c60b514502d103842c03290032501c202c000c40e00920b140a000342c81000301c01500307410341c080182076840701417840049490226091406142020006a00142c1208003007 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 665206663 1250 665205413 665205421
    0xe060c03100506250c0503060934170f0106030311060a11030a0903020316050102031b0301120305160c090b0f042f211503010e060a0b010306091803090e 67
    0x4c100b21010761508616403003040d691070400041d090440000e05000b010307a40c0340c0c0b03003503803800b41ca81002820440041c0b0031451f01a1144958800044600d4442c5c0c510242007820121982e05a004104c42400103100706c40d0364003c50709007401140041d504c20341d0b0b841e44c2c1000806003103140100c00b401004401d0300b0608000041840340c0280c9900054281c000b00d030b0400769050607410f40c49198505002c0e0072a4121080030b200054008500900080e00f000340783d00820150700b44103020a016040103202e030085c4502c0802c0c440c40240c0241d8144840e80181d01c0361036035a08550403070640c024200c2540341c000b56081840c1c413111002c3c210000381c80c01d2020807509071511840b00400f00701e40800c200410480781098192a09031501061001c090401804d9500320101c0709003021606d09611b02c401c60216403142c101802094140c101000c02417030035803200818000034107107261586040540d1550b00041c80c0709240a9048442291a2000b00301600ca04004011003055040081c40c8a0444140 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 665207913 1250 665206663 665206687
    0x3903101e1502030c060a0b0d0c0b031b190e0a051c140d0c17040b0d091203091e02010e0a03031107080706080c2a012a020705130e060c03100506 63
    0x400d5210b001000c0018a610247c000038802c5190040d000c1c0c160074401d40040307102e50b5404000c50240081304143c40401100c0e9010388840e00c1011221102c002485980406182c0645104401d00030300420b0b200b4040d4032400850b40740c4180312441c00d1041c40c0303c1c0c480401e000c1c1d2512003150380501100640b0900040d480064026200060014118204420040030462128065902400d000041c99a82e204000708070005000e01c104242c43e00d451203c1d00f090080c1c00b80c407850044552046041629400c80c9880300d5070b2a4238400c0981c14810710301c81003491580c07499511710146100b501c482c44c01d4040080c40c24030380341440c0c000382d9042d0b1100c141400f80075000308450343c1c0301040940c103a07038038090380b00300484052030f8154814246407200f0b0265407601040d041400030694003401d01a4112039071940c0d000042040450401580042000b84a54208458030611403401c0c2d00c00800c48030018a0341c1840d04404503807100d41f8541c040280403e11829180700344c000c010071201d1604010b100440 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 665209163 1250 665207913 665207923
    0x20d2012010c090b1b011d0f06060d060b04060e0702160e01050a170703050714030136050a050f01090b0106050f040506091809063903101e1502030c 65
    0xc0c4c80c0003e10086030300404d041d11100c0451a19038608028809090111068260603501e0f502c10345140c00350301c40344550080001086841050001c2110962920a0b01d83c04001c0014003d45600a0784440002c13444070104107410f402058154000e03e40191900c01a55440b4610341014607001280c5004002542e50682c445090b034000d550205101c4c0344242c44180b40810a030700050060142400014150704151503e0030341c4c100c150000c0c020404210789080c8011141010042ca082e034250001c0c0c0310181c248104c081443c454422a02d0849031031302d682d858214030040c032203102c3c0e444004a000f0494401c03003041c0103000b0380c00c0490030040b46400c4080c0303d01a500405001e114042011078003960f941c00303900300740c412100c03254039242802c082c96603ea01c1d0844800c1035a007200310006800c0c3c400e042901129102c0202c00c091054100c5092080a500c094008103901c1d00c180c6000c44d0499401d246111541c900036503240301c50380303403c0d85180d99080c86821107041d034200b481007505215012030 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 665210413 1250 665209163 665209169
    0x60c0503070209181f0b010206040c1401050f0715110c060a09031403070207140a1206020306040e070806150a080d0c03210603020f031216020d2012010c09 68
    0x41e0307100144c0c0d10002c240d25500c00d1040c10b9001c500c251404809925030680381c0602100800308207210000e049001644e64000550307008001407503401007040850645042d80510040c14500245000c0d5140202c0015402c11101514030605890b84d00b01504800c0c424640084024180941002003a02e034050322040c0041502d03049a132582c0500d400c051280a01c00010701c0c00c0301e841512814503410080d5521205d0007035000700420200b02200500c0c0141d00032048801d07603081c2c4120030040343e58200194001a00041e08180c41300b803482541d0030b0a00c0050302a040181c010111890a240c0c405070b40c00c0404240303030013241590713000c0c0a41e0704040380c0c20145111600700880d00f5115482c08071106071403800b06803c1d52451070014044402c05800c11310859000b1209400340541e0f8100701901c829202c0000e0070400020400e0a84680b03803000094003450004003081040644c0c0d484c0c407200310f400b10504244041075a00800414507103252400c642c1c0300741c84002c100d42e03500580007502d4101d41d40 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 665211663 1250 665210413 665210419
    0x90b04150b070309090c081b09060d020903010f09051507030203330405130b0108070803041710050a050105040e0a0507050114071202030703020d03141602030c15010f060c05030702 79
    0x61140c145405a04c2c0d120003020300e82410000c0d4901c00c4002409201d0540c0c1011540c54042200c076812400b10f015503019120061080303240c40b29100d142c10095014244d080d4055485054282c4041c4062040038540c600030301c050023004102c0724550a90400080c640420b2520510501005405c01903012810340302c21005042981e4040b0780c0d0401b4240c507400c40c280e22034101400c01c0440b812110303280c2070061140300d001100340d0f00d8104d0291254064003d00c0030310f5000b400200036100c0348010f444c00d2074295006441c0c40d0301c405444c000980c4c10031182c100c403407511200100540d041500c9000d81508441014000c211600d1b580d0f2902c942c100e10825041080702d215040c1580d801c1401c40749031686c0440c034803014401250010f501c980211038241c000d0b0040c48981056540a8004c030f010300c03100b060303260110b59210b0110345482c0c4030354981002188828440d030b618a8000b00700d40c0399401d400c01038200c09585880555440f001c11074210004000c01418400001030b000010f540170541c0c12 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 665212913 1250 665211663 665211667
    0x180810020702060706110c1234120206071d030a1115270603010305060103170d050712110703050301050904060b0d06050907090608102004060306090b04150b 69
    0x30b4000a240c601600780054941860312540e200031284460041c6141140325040e02d090760b00e9061248402d000f000001c100d4844c003003400010465200250f00c010b111030444120004000b900d402000030310742402c0034050b03840f1790240603115070001441c907030b08109116005189001040420307103844030310701e0081080681a0320700b0001e555000c09084150783e00aa001e40b40d12081c007041c0000291842080c01c40c0a0410b446032184c2403410032241a80c0d0401c0c0201682e91941d40d603001503a03040d450074140040d080c042402a2515030203414080c0c0c08680d6a84138500301c600e0100c044480769821703c0300d80c0004020582c0066042801e80b030459908032501a116a01c500303001d0098540c00d1801a840640301078542d04010722944082c7c0902424821108800d0326080144100e6120307000b14161644a0b281d07160b900705140d004041c0501c0030008008071440e03c00c0c581c0390a41c101d034000e000800e448030024042110f0900c0f42901c034540881c0c041c04000140d0440d0f00b8407225900aa2034900b0300 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 665214163 1250 665212913 665212927
    0x501141e040b03030c1014040807030c060b18060306070201060f0603240e0403170123030c0a06020d080a05070c0206070309050a0b1801020106060e010e1206040308010618081002 78
    0x11a4000741c1c40300c50107001e41750754040c010700c0c10f52600e2101a14a0815150040d061202c400d903110032440780303605c400e070340b8541106510141c40804010380102d940c1070700d450b120520f03138503164070342c40c031030210b2039400c92190800204050501400030006011689000010050090038419183c1218500c0c00c0000300400201d1085103003a60311640d2200a041202d030000322007280e116450b11550082d40ca0070601c04030fa5003950428002889441c1d03038110b41c02c0781c412a21f0060740160005480003012940410719210120341c40e205164403440c0581c20000081003010340140744160700c8000d15104000c00e28001d5000340c411545100b02038002c1c84041020f004250203248544e01903e03005094010f241c6d80c3c0c84081c0115030041c01800d5103007018040c00401940140102400d4a9113a140da0307115401d60001111030810788014607500c6100307000381c1109035106114081c0581d000c0d0b03447c84c49943c103180b00502a0a15448400080c028a110400480c0307030210710f0607040088820b000d07988043c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 665215413 1250 665214163 665214169
    0x1d0316020f060406050903101b03020f0c0106060e010311070203060c070f0b010e06010e01020307051b0f22180803010909141006060206060a0b0301090f02071401020705010501141e 79
    0x40082401c0c0d8100034000b4020078141c1d048005403010800c00c9040f200d91066400725078090307481d0800380741d03c0501183c80741401213010342c018100d001803503c1302506080d14543d8542c2900c1c07440c0d00a8001c079166581020319542c0c18011151105401040300740f400c8101d41c0442c6d41c2c0c40e0002c0051100301c0d0049800b50820150006034100590000440304855071140844203c005041d942d89011500d4002c0381d9000354008410b4581c09504070010b0a00c900602e008000703010100c11010fa880030a192000c01c041d6515020005190040404217420940b2a00c0213404c84890182501c2814055408180000c00300407c03207054400b21600400d6a4210340f40407100107645c00ca1441280c0900c3d1200001080d107688410300301c801950807254103803100400d01c04103e002d4002c0e0311155104000500021545800c0702d1207605288500529251a5840310203040301442c100c2d480694001a071002409001d002c1c442c050401170302e603069070b1480d01000030034007000c184020950300180800c445050b9 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 665216663 1250 665215413 665215429
    0x1b0304020906122b09080c0d02030709020a0e090a0b1e031903080403020709050c1e041d0a05070509010c11010903150c020f0109030c08071b03080d1d031602 69
    0x29500f0b800c8840840104565070b01500804480c608899480189801114440da000c3c80441e1080340240200c00c841c0800d07c681d501d41040c0c240d030144261900014008030500c02410b820050741d60361801e40d1403a10400c28000006098a0902410442450240c1e035071140040101c800c1410840703c0402520003081c10b020400f400e042044000c0d84691080c1900300c0a25071141348658251607086881c3d519240480d20180c3d114100b211007440120110100d900c1ea000c0d50105800b00701d804c0540e42c0c640c02c40b825a036031003500329080004007400080303550b0b80078060300210b6904006042c19045c00000703040280b02c010203450068603031005107060b4090400ca501035508580e4407440d203200300c83c40c500a4000c5110020040c800c540c0300041040341032080d4454142d140d565180306da19581c807100129000310381c0544200d05180400c000000902001c0342c01584621102078070781c201914801c003152401000a41142c40d0f01428a000c03101c040110746143c690480e45100c2e4041d1800031940361 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 665217913 1250 665216663 665216689
    0x30803190e0d03020d0c1e0509010504080d030606020d0804020105030c070218012301031a010c031206030f12180905150607060509012703030b0d020607060906051b0304020906 77
    0x2400b03203020207400c02d03034544c004021514440714280003903003480d5002c87d50701351b5880c1d0072840110a441e481c010280f01c2d02c02400300c80e10514110703003001c1c0ca5240306820114100c102c040400e0380c0710390420480740c041c0300104102640d0f080c448107500d000e80002e4112702c40200300503058000051034600710741d5008601d000346501031082e90030702e607100c1140303040c80d000380c0c1c0b141108024101382005280d0311034040c02001c44100f5604c401076032500001520a840c11540480034404a00b0507440124241c0c8140ca0045021303415128a8441070b0030a4018094281d880380200145000340c442c41d0303140c0c04c2844045481300000020030356112401c031040a000031a160354030940004040040c425250000c1e4040e00c10b400003081640c0d101000070114581d01180c60140b1090b800c00080030134020307804015142406000038000216684c009903055001c550110707500750359061700e2401c1c40303070707a00c1880e600403e01c1403072100180366900f280307030b01c2d001c000d100a01c41c2103003000280c10740e120120501e2030 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 665219163 1250 665217913 665217941
    0x50901030912030b150708090d141912140a0c060b03011a0306060405190504020f060d200a090306020903070509091b010f0903020d0f0512090906060403080319 70
    0x600040900401030025014518807174001c280617500002041800c4880c400e5108106c2e500d010503400500010150010f0156042d0701211814a02c4a505200b04d00c15220b51030842c114450461400414446120010f0320812012409646054001001321030790182d1506110310717040980c0c42c1c0b8402a1106c205056019402d00322050143d4465404540400d070084040d0b0f50742e99070f0281403004035502140e003240380c422004000595408641d120715049400605107000c42005031011070340c0755210960082015a50708580071040d19044000411803c081c419a46810608280200584028000501410b82c00241f41032550380c10000140108000f03408003080b440e100403000e460702e4844030910b041c85003a500c10390556210b1040b4021600b2a5140c0c0d0385014110340921a60f140e084004403503104034110b0690204108211010b0f0350180500881d50360b0b03e0603018021488409070256020700c0c010b000c18400280310200b507a078400603100c1071a50005821080c00c014159403602c0e415 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 665220413 1250 665219163 665219183
    0x60309120f040620031213120c02040c030b060306042723010c12020f16080a0908070b03070513090c03020403020f0603100311060d0f0b0a080a030801060509010309 72
    0x802903a03540082d000300c0e00c1039141c08107498040406040c04c4500d98042c000150010007041a50780c41541c40a03800c00c800351040800035000741d0340d500c605031144850308082206d0500007021071916000e43d1340040018a002d20102e0f05010100d031075400042c0c0118811510b410106240040c2c0c40e122401070040c1348103100f100d09543c00d00b8440300401100c41d20790603000c0c0c5504500c801050007407580b8500c1da680c40c44103011140180800035005529444100b00c003c000703400804c1005034188013814000c6010340e035075001042005d000071605900c07200607034210100401131a0410000d82c0e42c80701c0d050a04556070f04a41d28440c817502072503081003802c24504080c2640503a8564090320a503807082d11030782045011242005403a000407912202c20314121076040c030004501045039014800d0141c491030411428100c4041a52040505104c00b5030707903800300002510303054088800070041c00001c4e015001030f03030300c00070600342d4140145000d022002400c2034447c1d1003544002c07089500072004003 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 665221663 1250 665220413 665220427
    0xd0b060d0203060f041b0806061905090414062a07050c060409050a060e090a060b0f3c010c1407090501180b060c15040204020706020406080403030e010203060f06030912 74
    0x4d0602601554280e500d8000c001c0880805410aa942c03c141c403400c40c010f00040d503440e010403104a07104038940c09894080d90f0000b400c0e0f00c0302d01070f4500031331240c50340c1309801c54080c42d65890020010000c2d03494120039100440c41e040007110b00900d0080c0c0d0b118983da50030246c08d0507483c0004155005810072800540011108000d901560088030a800e040c40255078420350200005016100c410082c2c000c1c0320568009511030703000a000007405800861103c00b03420000d051850711004040f04c0098803040c00806a162040c0020503c0e072444609408100002c002042018480002401864424021050004100400c40041c04281e100380041e607159202c0c0138603200d501c02042005401d0084d207503194a449003d540c8052124001450041000c00c0c20098241002d00280d8000d0f80c20007016002c1601400284094900703500c8180741c5003454a401021500c0101058099034414402c2c0401c80d9102450618800400c803800358130f9450b29840703141440076003442d01800e080005801 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 665222913 1250 665221663 665221681
    0xc0d0f0c0209181518012703090e07020a0506342706020c12121c060807151704020d050c03010609062108040605161a0a0b040b0d0b060d020306 63
    0x10300c0c0b1510030b40780000842c2c00900703031741421f80307400b5404d40108101103044528007480301c07803001401500920b0884c10043e528040b18502c0041601c07080e0042c1c1001c9488028043c0402c00d564110320110300380c69000d240c0318100c00c000b0003100041107205855181d88040c01e0700c2007a40010400036552801c040d0340504010541c180c589108140240c014041500524540407140141040c2c004014001400c03285040b2040c6522100d0200c0790000008085040130110341304150252403200e00806076181440f0202041822942e030101c20040e058807003015440401c215550007683c16551040c1030922440d1030b0342000b254050480d010361819000182108c80c42e041003044881c4262401c114a8210311300d01c06003200920050402141040104501d91041e40101700e4030704207042944561035143d545440440000b00d03101082c0c2040c1041c0f2034607948078070400b1100d80b812030701001a081c16602180d80311101510150004c80442c0019049488090290003510b41c01810380e0610320b890118 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 665224163 1250 665222913 665222953
    0x512010e0117010203060916020a0c0305210301080a0201050a09051804021509010507110307030c03050105071202070f030e06130806040b090a170a0909060602030c0d0f0c020918 78
    0x190202d25200200352200070101882140e0290340003500c54880e517a81d903a60909a00c04a088110841c41400c0740310b0f01043d0311600e03420140d8894005004000d0050182841400e0850340c518101e0307404100400c17241d803001403140f5001340d080c20000d440e01003514040e10780000644c001500080404141c4801c4180c00229520561007110620b00000e000e4440360054015009041d011500400144c0d002c58503203002c80c0d6079000014100c444094903507544000c0c0710900d40c41100c44d030f911002440b20a0350486606960081e00d0030301141401110703180d41c0000c2c1d09068018080c0903200d020650303d52611011116142843c20800d490303590b0f1005460350f1040100c9007594048103031004074070700020201d0800c141681190f40c400007140742ca03888111660000301c01900340a00c000d00020001c40030300030500181072a8001d561a8030000c402d060a00c40219000300421074403142002d2440d8204019554054054408034402d54482d841000c603805224107404c0319205030003c02c60241e5442d40 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 665225413 1250 665224163 665224169
    0x6060201140705030c0403110409020d0c1d043f02102406120207021914010c03050f0702010309020d0822051804051005101a0313080a0512010e01 64
    0xa0740075964890100e61034081038a0318200c8940400041000c107010103c0304218240041000030b0248588d4001200c0101a103c100c8481e03a44001c108003503402403050110f0410341c000405010700c4c1c961783c0c00d800b8124039014905442980c6101001c102140301d040306102030303806100d025903a000080a50340b8040407005680d00750501d4902c0c046c2040c44503c20f50744086141601400c0ca003008001e441c00d2240004a1070640e500344040d030301690301c4000b4048241088070040b4200c1d828040130064041010f094181840148c400010009501c402143c614068014071142c80c0c45040c40120041c200700314000c5c1d07010b80012000c00902403580001c00481c0780020b141c100560840445400201c0030744035840c0e0000320080750300c5203d000e070343c051a40702d0302c500705803a0f0540e510b84a1000300d50717064540e4904071072068030278000c00c648601540303020710f1004076450071480e1003050350468008400c0000d00d599008990580050b000303034203a5a12200344192403416607114244504a400244 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 665226663 1250 665225413 665225441
    0x4060f0605010903120509060d090b0709090b01020d0e0307030501020d0b0f0a0605030412120509070627050d03180806071713030c08040b0d05040b090c031e070906060201 75
    0x6034a600030f820490440703500c0106140840c044050a8a00780c000086864104401300105186d4402c64460122220320408e982e03212070611342d42c01002d003540d90b001394100034601100c01c8140d82e000556000340510600c0c2c4200c071506e100c40800e0802e1841e40c0300a00c03560000c94060b41c040c209402164a10605540001a4040400c2000080c021034811000459030070004500070840c0d60492040fa4840c60400741b10390b05e032841c009021614116981011500010000d101c11070713010201c080f414a6820000720a0408451440f0300400180b00302c5210b001120f50a000301802038880f02e0984108420380140d0f20ba640c54010b031aa002100e07a400000c1d038040aa070701003a60210300a00426545120181c2954559015100f0b03105000080d52000d00c1800001a00b0003028020164913000c0c40300403603139040c1450011015072001d4001c14041d04020381c2440d550b1400104100c5d0b110100e600c41c4000b115640400c0d092001c0707034001800d44c41c105000490038940540040c100310601c5 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 665227913 1250 665226663 665226671
    0x21305060f182d0c03070309080415090e0105150903100c090f0503070b0405060903101b1407020906010c080409050c03060102060a1b030b0114040e0f011512021602030604060f 77
    0x3503c0b4a8110071000480541a2a000200d980c0750b0003100139660050b0541000a6044002d481d131801a4105502210000074240400070a80f98005c000f4402032510862010032541400c001848000c421085800054008180425596800c111070510102e483c4000c00c006000c404000308401a40d00807261803251880c070003d55814001800750444211040d0a41081d040c4000c204455020010f85580b511420000324142e103a18031a61102604200c4070300c04010304100c014000d01e0061444043d8032100b44090700240c1c0341d00b0107041e40904240390801c0b1080c0310f850080a180156008200d0700351a010401c19243d5030b000080d800340c50f00f6022160183c0c0e4080074030042c1c400229480743d10380419011403100b42e0103900880500710301414501d1110244c80749400c3c032604190b001c0807140030140184016040c101e40400e0141c8490360440c80b46c0204120054050000500d111a4403540060704400f00b40300c20548031125a40102510550f06150400e1405005602d4460001d0761070 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 665229163 1250 665227913 665227951
    0x24140129030403021c05070c08011a060705150c0d0507020106091a032527060b0f03011e17010e0714033003040f0b0c0403021305060f18 60
    0x2030203069a101d40c0e0301d07600500a40d0380882c14403a040850a456405001080c048040000c280000100180c1414000004d20500072007403072561409280310280166810030522021450200710044803c0081241d0845900c1e0485011010722801505103496854030040c044a298103400860031a017040b84140942d4a01044091110690320592985640024a40031950300109024101044c0041a42e1001c50b541d031011210301020085c0a81e0809d4030101d0030080d084144100401b4141c501e10b130a00702000f40000c2a110b00c0107005100e1040c84059020b404c0b003840e00400300241007805503040442280710f842d02c0c0030f41002d03840000c481c010004003081c01310a201240455007002130040c61078926160f00c82c00d5142030700b54100c2d40f5450303000307400e04800b0b0310000441c003035845680040204006400c2054082e8001740c640c002c5590700b00030400c090b0f0348000358078800e000003070070015050729130b580000c4801d01c0042131075820034204a1143e80c00ca030f000500c1485400d41894121040c0b003 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 665230413 1250 665229163 665229239
    0x309130e0d03091401090c081005160e03010f0204180f0203060328140303100801050f011e08010f0f140403080f04030c08040b03160c241401 62
    0x5118000d1549544000031811405120303401a524141c0074040039040120311441103400d4454022003034410414080c010450283d0400080c044000003850401c13003410074031010760b1801c171500010300420410088102c000e80d000c0d40421128061480215034495580d80d1609a80c0d4080041c4180179180c0040001140760380c1c02201d1040100902514a9102030754000c80e40a5450210f41c10324403400340c9100010341200d40f0300004801c0800255200c1c0f80c2041c01190300c80c6241c02c01440f607410041803000c00d541105201d0305403503004480e0301200440200c05c0303c02001c2648000e143d0340c00c0c44410004003070542d1001355030200c8544140451421005600c55811043d50300030300150b1a80300150110100c4202c0681151103850808581043c40d15244483c0d081604441c03c629000414401c2288403020490041074003810704000b0300400d84c03691143c0703540c03058144c0c125503607070302c03c1c01c445403000d522a60901104800c01d4041e0f584420300d10004d02028561864050711410200341154 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 665231663 1250 665230413 665230421
    0x5010206150a0b070c1a030916080a14150a0209010e061201051c150b090702060f0f07020309090a1407300f0903030b010906090608040b2205030913 65
    0x400c0581000d00b41031502c680010164440b0f50305545984a042c8086104880c03412820701606801e1019030701d07418400347d420b040c10103c20b25840c1e801d114100421102c00007240343c820650b0400d0010300a04e00074020070b81804003240e9600480481139040001c1c0503404c0e0302825408400780c1c0c5403180302c0f0300c00701070158038403c0602805001d05135000401182c5031070051440221101010640848200d40e14031040358030054101c0c607540d403920710f001e03c44c1c10040c2c44c175030340600a40f0042450b41848800c094800901a040c421516102c40006024030300800032101150800b0344102d00d2450305130340800082200310410880381c4200c5000c10142880b40c440140d401718040281d01a080c0c02c0000d160603403c21070321144100da02c58505002001c86841084421802910b000c45d0882c031004c00140030b9040380e0002d000f4010105818000a0345c0540001d901c0b0fa0f00c00c400f041030f51079070204a2203515070f032074510b801240c0c290b519a080040100150555a43c02c0c2c60203c4074038030444000c426a = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 665232913 1250 665231663 665231701
    0x6090607170a05070215011811040506070318050a0b04151416020301141f05061602090406112101060912081e0c071d060f150d0507030605010206 64
    0x41e00552002c01c00e06405036100700e4110f20140121081301c810701480f1880300030700b40d116441c5c03c01a88070071001c09986001e90ba031500a007004c198505818100003a40034000d600e001f5080109550f40705001e101a04200409030a000b031400009559a410201d1907500070302a82039803c040422340c8294500aa0058514441d0000e90078181100d0003003920f00c820180209917410364a4020030900500c88650303240c05650a1810054044850745d00c148200b8180c0d441140244401c00c002c0c1c0c03140c10029405c082d9254102c0b101c0045441d2401c01c48041c01c3d10400e03800e0350310000120500034040d910114080e002410a90070096aa1464151809421407003407030b4507880c084140f003000909200c000c1040d49240b01c500c00100951005200c542e42016803c03440550211109101e0340a074401c2c1c1400c0c40541d0703034520010b881c00340081003421402c41d101901620260740c003c9151251102640c0d80004655810011450000340050240510f8401c450160103540d001c9010030018181d00d1210b = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 665234163 1250 665232913 665232947
    0x170a020a03030f050708030112020f01020c1302072d02180f0112150e100e071a0306210a0204050c28031806090204150311150903010c0206090607 64
    0x30861071514180d41042d0800042d0003007040c02c1040c0000916040c01644c00b03081080810f4400b070541d44144030f29030100c0d1842c1c0341550300c148010000c40d542c9001d0f51a140d540840096242d040f245042802c1d240c80c128241240c3d4103103015040c0e50901151800601d07070085401400b880c00c02e500000c01c60005641003002151b03080d0041c840b04800c2c0e0743c070b8542d4510030b0500c05d101c2c41061718801d0407503400c40c048803ca0b4011183d4107011200c03600961100803250030207440594901464040810840a0022004800800052842d560b035841d101180703000c04100700c010307000035001c5a850301c84026040f480346182001040c0303101100801d40f84004207014901c1c0c00341c452100d00310441f400d408204010541c4401c034000150740300760202e1403002e2044001090051252041000741d84042101100075446440d0030008207800061001580609a0721101c40300000c0100b6030040c42808142a019824000110401c9600044c1d00744035128181c1a00ea0603192520708030b49100060b01c4120b4 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 665235413 1250 665234163 665234179
    0x901140d2003252601060908011a190e011e060e09180c0607060218040b100302070f06110a020d03230907260c04020f0412060b04050c04170a02 63
    0x2010b001900081d090301030644c100401c2840c145200d440c41071065480341801403d100b0b004010460b0010400d0000e446000028084030900c4c00c2014858407803030000f54414255105c0750000041070b002d01601600c5403948041c1d0540e1144020107400c00c0064091500700d80307043d40010b0030b61085200c2004107000411003440c40d100c004c03520301403020084001034540505051031300d541c2c1c8c2d06030060441364810703440545c807449005101503031041c130000f449000e2400c1c01c5140c0c4e140c0d079a04c1e800da20b64005c0d03400e0068a030915410417040180700120024611450803100c0860403c0c240090890752400307600322182850300c2c0008a0a07610100924522258503c42c041c1404007603954003540951280704032840c003035446000030134001258007052403c0f601d03981c00b0f21500400f4000d4074050201034609501d0012140200070223403103180300b00d0605207500303106d030002c001160700301c030714078503001001400380b0b0900046108541e03129100c0c011096141d4080070140d001d0100b038003003416030001c00c150 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 665236663 1250 665235413 665235451
    0x509070503010611011413030908070b09010c062715060b040902090103110a0908150c0706050603101a01030b0405040b04030305041509060605120303100b0901140d2003 74
    0x340314000c140052842c55502c6d5407410380306a044450f05441030f2440e481b10990800642400340c41e040032030304140b070950040304041c08a11148011a00301c82001e1800d12030002c0300c0c0c20102c8c001c0a5031a000c25018040360f040e40d101408a400b058019130040f202242c1c4a481200b142c412500b0610500c0035148042c8800c00800c0780700d0740502081c11040c1030204030104210b02e060425030040c20102e000c5849042c05025094040007030078101c40c070841907102c440c00e0410b901901401070000c010000ca0b00d480006406480c00e224a6441c8a00c000040c02145842d01c20950210028043d050000707180c100b01482918107402001d001e16045080030541e615540c8003280507110050098865110340c1012054280b001c0c420060f180f03000d9a030025616040208210118405884040c00382d0b00a00600c1050725000344a038084030030740c9101d596910080c50042e81c02011082e40160300707a001192002550030142c018141ca800050300c0b0011140e24001c0b0034005000a40c3c01a0050b840f10302c8207 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 665237913 1250 665236663 665236667
    0xf0c080402060d11040b040f060c051c03110a02010e16061d240d06062d02100e06060307080a050d0f090906090b0306150d0b0c0c01060b0a0905090705030106 69
    0xd04160f11680300104000301d80d07508041503079000d6405101d107000c001070100000e002502601e005403a681c40c0074100a0016101c4e96944d10001e076104010f080d1407003807050018000e510903075200205030001922011007101c064020030742038000c07141a0103955011098401c00c502030324161589619544100e0b184403010310344026068101c2500b011026008881c0c503280403e140401d20130700d00f080c42d51128819001e50640b15143c0c054001d1140520329005442125000e008240360090031011344000c03404000c92a100c10100342c00e4200b40b07451014a600d0b50b000c44c01902c2840251b080b1307002d01ea91010060703515051010041c2c0103400224541d01c0061140101041c1515180350800c840358070b40fa0110102c440c2544130342e945950300c0d800303600701e801c050200952003030583d1020242c00d51004081001a8014580103111041050005607480509010744664024503402001030702c0d110b4150b00e40300d5002240a04c0450301d001000580381c44c0c0f03404a14442d500d25603035541075902c0e01e002 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 665239163 1250 665237913 665237917
    0x90516120608071503060603140604020309070302060f04060305012c0c0d1a010f08041112011803020607020f0102031501111c020c0a050405010e01450f0c08040206 72
    0x12401840d01d407500060304450411a240c05400d0700f0318540d802460003034029080301d8040e4072800a05081c4801d9102900b590110f03568083e500340e0f80035981c2d5a40c1460301e420640c0a80009610110204200300503604420180040e2411034034104620790300e5920b03001c071b03c1e00642140d200400c8550a0a000b081c01c41d000d4a07003120000c000c10f030625a1036010032065402210401514900c011342c400303519039100d8044490b4192038140f500031030400b81c03600c1ca045098507a20034040c02c0c00f2402c001c1f11600035070081c201c00d000d001c0504184d03611443c0094076044207580440c01446064500400c495040c4202d0340502994034410002d24400e200544003200d03a804c81220358012801210101070182c003900e082210180d001e040c40035440c40421042080c150051405185010014004015010312807810b49040b13218171040302102c081151b1040d401404c0c00301c40d4031034500c01c518000000400c150040d00e00d40700c0500919a501d100d5a048442039803650001501c1c01c004500503080c0100 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 665240413 1250 665239163 665239187
    0x810050f1c02180408071101030c02070b03070c0b1905061e150702030f0d03110a0c0f11131e0902091512030f030103060e010905030a1d09010303050d06090516 70
    0x1d03c26080c0310340742c0e6100c0c00b400300300c0302910740000020740803007040385803452030200000900b01004a0310034590000d5894181340219222000008042015280150071048099a0002411a440c5004c050341d44c5a900c09000708c0c0c1e41142454003144492800c40045075904060b007030780014465220042051510344082c0700c00720a9001c00c0b002016880900c03448c103c40d409880180525090003c0050854229017108035891a00340303c0650038551003040c1c0c42c0340340e400800c08144c030555405c4c002030100c2112180382e030095004001540e01c0400ea04600764003446111480810388081381c01310160391084400075407018030040010f0011247c6d2880c0c0d1103000317001c1d003403558007000310380454510342c00888442a003440100040080103807a001d201421607004000740b0890402d9070b01c141c1d40c1d001d2000c06c241404030380c020311000c4107003810301e20700e454600501c602c14550703681c01c2c0035250740d1290800b0801c0e0360400b030001c030b0b0b040c09502845000e4903c0522181d42882c640d001120300b100506 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 665241663 1250 665240413 665240419
    0xf1014130804030230301306110622030f1806020f2a10030207051609140910020a0509030109031806020c090112020d060501060810050f1c02 62
    0xb21021016880d00040c02c2d80c40f4410300440c2200d0303102d48403165440c01e81c5c0040329040b0b034003090741141055204c0b20102540030300344480508400d400c0c903508416024800c18603020351510308002519036030082c2c440c020000380340242d4402c1e0321030303031042141c40074000c510181e440041d111520000e4400e0350480f0441c41146081c0440f0a03081c480201810002c1d4480030050b80510b0303c8038039048003031003004200e00c1d841280d10f03134540810f0240103840d20041802446072500c4850200d42a0080c0c04503402d05034860b0940300800c000d8400c058040c006401211070300c91410440700c21407101d44a03480d0007407400e40f000380384496900701c20002079032015080104110f402e122000c203a0700c00f40101821544a034a5800200c030350702106114514460b0302050440d4000c0150420a4071015103903410345010662441d0104864000300d03555201c401e6000b080e81d403615000007000c40d0300820b00e90044860600c2d10b02c0c5142e4541c100480030349050101075211400010f00c0040000000c00f0400c0700c0d2000d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 665242913 1250 665241663 665241667
    0x27030a050a0318050c01020d020c03070603240e0a05070509010c02060a11070902041a1e0304021f09060e0612011205010b12010f0f0603080714011d0f10141308 70
    0xe8202c60003a103458001c2115907911041c171444180d80c05002a5650f14581e200900401e0340c001c0000b0342d619010301c541810715544101a0000d240311010010003200c1c6481031501d9940e036801c01c1010f82000301ca00b107213001d10b003402040070713544a00b0480b8132880050b51400310b29003c64080041a40c0144220f9040c071441c6600d04003a524184801c0300105134447c001612985004140043c00500000b00c1603450020003010425100c0e89030242015516180029100e544600c0480e40f0034101071420074204042e031900d07503050340c2d0004964046e15002c7e81d508a600242105004007406400c1c5000a0042d0480060225082c0080200481409040082400120800441e40540c8800d0321b60807070b40d46030f5074505414003c80c02611800030040a0402001e891030704c4440907030290110042980503000e0b000210103400350000101038004d10301104200080b500c503640d0741c1d02001c0a0819602440c00106040788007446507116074030801040140e0741d500c10691101030010369404071005102 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 665244163 1250 665242913 665242931
    0x609141e03072606010609080304150509060c0d020c1e0d05010209150301031b150807090e101706090a02060a03150b121312031517030327030a050a03 66
    0x4154840801da001150320103a0f0000c2c840d00300a0160804818048000004c10a084001044904076890200207588071201660200c4840c801c80c00303038a42c40000801d0a169180020412015206054085401104e07008060001d900c01d458900c10492603000304006135801c01c961081806881078000500d480c4450000501443c8000d1802100e03103004130040c010003044010141000e08410244040360707217400c034040c100e035106056403400c0010f00320105006d039019110a8000d001d500010088074900483d00003c10300f01445090079440724009901900400400d00a0040380b148000e06090302190302800f416030300c086801400c05580f210b9480c1510310209540025041c2040074660303c400010320784000c61000b8111890522800032000e00048200c01265106409401c0100d0000e4404540300c440c2e201a901103030894a6001504000c0203010005502ca24240030100544014080150800c60440200745100768401c000d00700f0b0441c010805030181046a15000c654a60 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 665245413 1250 665244163 665244179
    0xb181605040317032d01050d030c02090702060603100504050c010e0307030c08010c120b0a03060f0f05090a05150f0c070c080313081015260d02070609141e0307 70
    0x200c07280c0f2002400101005214003900c61042649803801d10348291007214030500c0f4116000c580601c0317424407545040e4445000c150003610706d4045507400800c104e031145070070752000c0d4a41d10304942d024840e002d5094074003150f001603c45e55005940110042c03a410701054015103200d00c084c04c9041c1e26100d560800030015a264020740c0191840c44c00120712180b240e5000f038076141480300311450b21420100c61204948a5034148011640c020070041401640d5514803001032004031000021941000c0401070200e200007500300340da921403011145801080d24401d24542e4051325000c170035840d114046104503551001400fa010700540b2000481680c0340c000e585980e202d0491003072a0440079004202e004e4044c0300c0850810001001401007281040b40c0e40380c80c010601540c00a131a903102c100340108120804038000c4c00c0c1d10001c0781c1c0240c910a8000c1c1d664111480f5440021b81d50340c038042482103c00c3c894000c54880900015000308820b25161a610800c0240301e805215428000401305 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 665246663 1250 665245413 665245433
    0x3111905040f2901170c0d1e0f0204030b0c030105100302030a0212070c03080106021216110a0e0f0105010f0509040504140607180503062715011403010b1816050403 72
    0xd010100780301c0c50310050002408050188900c940c1d000020406c00401060003405c40700d600d00c43c0000081c500340b90140e60022440015088051289441d01c24440890190300403c103413402442c0c540d04071b9960008408042c4401d000300c07034203c018200080441402a0091a00031034840c0303000d410140001e0710942045400c580010014100030119400d041d00101c03064090a2244043d01c89070800c00002e42030380c41240007020441f00040c209a00748070340501003001c0c80c4001494000c507156610b204111101c4144c0c2c112580e115018000200c640c002c510b00106400319440c2d180c200740c20003007007100a28000b04195507040341c1d000e108182d5001800214030540a54990640703904c003000c690403000e411a04490f02070f900240034840c60080241c0c5921020060400c21210440c24620143c2072440385603410f209a44414004108005208a40d15091764142d000b00240d13444001000007000c014040c09141e405000c0c003150f5112180c01c17211004100904010b07103010798907601c002100d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 665247913 1250 665246663 665246711
    0x1c080405130b010807170114010c060203010b1b0c0a0b160203010504081c060e18100501061e020c0f0f12030319051032040f0603111905040f 62
    0x2982c96150942543c1c01106a81c1c001c122131504442c20990026484400c401c180a200160036480c3c02c201324583c0306441000c06a0343c80f000564603965035003140704803500181c0c2001800030311081d1050203060005040540074000810b0904114600b545140c0640c5c400407101c03a807940d04032100e50142e2000d000307640c046e0344034000c001d65690f40380951080790192a0f81034800b041c1048410040d0a40314030300250400a4140c94410184a4410303c2e03240550200d0346031455828900000b400701e40212070b07101c010040c03640c2501500b00b0850201d0b00d45401300006a441048841541030900305280d8898523450080c100880e252160820980346800072200c1142c03201200002001000c1140511030f00b000c40c03d458100c0c601d050010b03420065003201c030000b00194403c20101e1258000034011144010b014100700241e01800c002d00000e46030902007980c141500024010f00303810406011318855030181c080c030034003504000c100301c007070540d0711070807502c083d198007420f202d03140503030888540 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 665249163 1250 665247913 665247949
    0x7210c05150a0f0204030206040e07020109020a120209070503071b03020304181a030601150302220305030309010e0d2a0803090d08130c030209041416050406141c080405 74
    0xe260001d0002c040c0c071402100b503407005005001c10801a144c2c2d80a5400791900034003480010741c1c818204a00405c0d500c1c4002e9800341c0d8480d80010300c00729280c1d00c1c0103040c1c020341e210000ea955803201510688015610400003030301c2035541c2d81003094500b44000a0034400c1c4141d074501561110309003501c42e1000c1440d046141c1d24802124800d81131b0108840c0d0781019000387c062985012400d858440c48820080117264001448034200d0359500c01c0744071504400007a102e01306880341041359032074204881d440c3c09903103017078182e0390741c950f000403a0070141c80240e607401c080200d4032502d07a04c00f8100700014000c0204005c40c00c2c0018098201451080c40c180c0c004016103084124000d240120142007202c40060005520001c41c2e40b8001c20001d0300e80503660440240c40b10314000039410214141006140a004500010b00280302940d0702107610845c1c0c1804100d4942d11003410070300205015561001d4240c0c3d810b1103002080c1207200c0c010340100d2a8a040690752030118803403000001c08422 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 665250413 1250 665249163 665249203
    0x200a0b0a020a26060d0f050a0f030f020a02130903050c01020304050a02090a060b07121e0e0307080c06041707240306061b0620070c05031207210c05 65
    0x3845500003203d0004010640b00c01c41c1c1c180702c105120010501c090300840c050504413001d501030096044c2c07000505070348041180c041c00313560305001440744001202240010040b100c1070800610004600071a613800412021100242880c840c000f4081102d04a040c00f2081c4101d0003108020b2010314031480c016005012046094410062007004c011320640d80c26140010500600340ea01c1c060b1540980d22144090140c042210196212400d0205405800b0540c2101700304482c2c1c4407a4010702500d0640840300303115100e80402c4e443e24054403d068000506000402c122a40e108055a8100003801507801d041d46075450110040000c100042c1041c078126030580d49154140b06500040000f498038034110702c1041c0c0c01c986510007030341001e007880340c0702d111284c0c03070815461007101c2d5081c42c070070b505075140114a84110f00d0000703032013001e2082c041c0500c1000c0c401c0000d001c984490394801044200d44448440514030354a0300107040c02081100351175003002881c20000c0c43c0d0400200c941c012 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 665251663 1250 665250413 665250427
    0xf011401090302090c0921030301061b0f110405090a2a050603070f020c1c020d0201140408060901110a082a040b0309010b040c1d06070b010b030406110406200a0b0a02 73
    0x72110071144050761f80f0009228248555007540031065074199407007440c100d130038031309884d507009800d40e030002c006000103c08983c580d08000900c2c4004210200c1550140034598070780080070b80710a03150360301a00794075401c5c010a82850b82040e6002c00c4954071000b640700d01e901e034000b00700640c200f15102004101500140403503203404000e40380b42e141048490f607011043c200c260b00042400003400a00602d5510004000c5a0040b003051107040d040c10b4526480c1e0f40c0c1c030740c038995a030402596080c101e03501e40071071003140da1003000448001c240d550311192000c1d11340c4403d4080b901141003d098003410203a00c4440d1880402e07004100510300030303040c1c5803a030900300c100700d0849511245a40c401c502c0c1c0100510015082403006800000d004005643c2d504501d021621910030500d00400c40c2400600200e040703180d490140d801580034203c100030300d224010800140784518002c05010521030545107c000480301802d12840c0904d07015074005c80c007039031b455188051003030301d000c522030741c000c01c540d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 665252913 1250 665251663 665251669
    0x210f071106070c061d010e01141b04030b040c05040c0e0f0139050d1110050411131803020c0f04150b16080a030c0908060f011401090302090c09 63
    0x2150800c1400005095141891180980400303442c000060400c0c2c1c5582d0082e00405201010503500c3c030726980248020300c101c51105000303200f600189144a00b0460202c2c007500300180c130403080302c241003548610746415512144c110030b0000704125540041d940c0007146d02d03211402011002c403c075455001c4c0c4440b595040003500c0d000a12910704201c00007502106c45508011500c08003a0b0f180551504038494203403c0c07540c215240000317071151140619046840c3d07440040c08800303600d01d0007551001000d02800c582500e2047e01c0c05000c944038102409590310b04130926210951140c1d0300007644040ba0304450245142c820025405604180040d00c894205201c03500d0004034112000c000c4110360703000e0911101042d002c1d013400c0c103002143c14401c208070858000e0203150000c502d1070f102c20500c0b0004019040d1079440c2d600099000d800060520b50000f20980144010000440d0740ea007410b401d000c50111100156041007825400040543c403411601f41c05089041030709640c40e42c0349030034 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 665254163 1250 665252913 665252927
    0xd090609140a02030606122b030506031605100c1410050705131505040b030a151409130206040f0e04060b030a03020619090c0b090a0501020105060a0605210f07 70
    0x909030741c0c0007681c00c040183e50104000d54004000c0b50b91380c0c0c10000d0360000500e800115080c242e0941038142064101806041014803100e2240c0d80c144055501c00c024036442c1c1c02030064214603e10149030500071858004c14641465050340b81c60100d204080d124113102c44000d001c44252500081030072807a10301e076801880e0f480b00751800c3c0030f45400400300c800220381d011445500a500c00d2002e80d0741c2403503c00d00403100103040d500851038903828080c0750310004012600380030040d1070b8010310008500e4504d05c14440840e400404074551690398401446944490b540226440ba42c20000030801581255600020b002d01c108020958503191034000221b540000965100398054040140000d900080c440d9000c06000d5010000b41031030a050005045090350050282d01c40400c0421a510310101624000d00101c44129900e5a00d100580c200c80f020340b080e980190610038140b20840c00384008004111246405a50170348060114081303031501902c039040c40500d10000d2060095102c0e03c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 665255413 1250 665254163 665254193
    0x90212011a07170c0609150114060406030203060f100509011211030402060a02010f050406050601080610090b16050f030703110d05040e1f0e090d032705030d090609 72
    0x10000002081d2400329800750040400042c1051688004034003055109000d4070aa000050200ca4060600c1004a52143d20301c0942582d480b1030040005045188050b801d0818034025010382d28150030b2040803030107948001d000c945c20081ca100c26281d1619070355400262001c00d5640c864803100817100061640d0382d403805005500d41042c0403c0800c2e20304800b10380e003080d070480350301e0344e500c10007442a40507104600b6100341d01032804041009000007a0401441182c0176a50643e45580307050030850300404444204000900d0544140000000c0c0c00082940ca00b004c2e401c00c0003400c0721341c0ca0710300d0400b800405c90f802c2c1c1c102107080030804d41c00c8800000d42c606040d01606130317941c4404000b00b80380214480c000d807590400c0081140c20089610070b400028a400b808041151503100c04403660b01c082d80c2845807482542c800300d140c58443d20420300c054044100030340040c4080e2021820060303084d01d060382c244c0020442c4540b40c890038441d194005100c0d04003c200400c4904142620400c000 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 665256663 1250 665255413 665255429
    0x60b12060c03400314070b0117061006030b1804111903080a0305100b07030c05061006091202031c091401081621091104051005030601031410050109021201 68
    0x65908200d201c0e00716000b4003410881c03c8181c1c1500040c00c0440310100c0360301090325010740004600b010710007808809416a41a50440d00c0c40320308000000c1d03a05c12044402a5101d0506d01b800c0c0300d414400e400070744103400f004080066003c41030f0020803003150f05540c115403501c000381c0310344010b0800c0c0c1d103072040d60403840c1100c440880c65500c400b2854402c48107a00201030b070b28000103190514000003000900005070f4810744074011840d014143c255625820388551003100d001030300541d405060102990041d81d10300078607500e0b24800c81c103210812041241e043c0103510251803407078180c82c681840e85d401d640d1401e010910788110344070200b100040040c1042503443c02c00000d2028140700000f5414070349030a030400040c1462810700301000714550000d490810740760350300740041c07605959100c180c115010005a220b1108000d8194034512505030150024001040410344642c2c2c0250070384807403c00d88420340900d118510490714260481c0702c03469404201c1000b418141004940500000 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 665257913 1250 665256663 665256721
    0x2030306061b190f0b0a2c0f0609070303080703090b060108090724083718030c1a10140609060301062001050f04060b12060c03 56
    0x4030101c0c0d160300c621a840b805650300210038880030042080100003802c80304165080b00c00140c6001020004a081c0c1036a00b041e040010071054291481080c503800a585086942d804182010038100740a1031844d590740d008141140602040512034144950704c6c010242034078030304500d000b6106034006011081018505522000024124100350740c00c0102400d000505507280e8100314a0103400d6004240941c1401d0a100d08085040c120740d021010303141c0f610805647c07031608200f2411900c0403004c00394640046001090ec030050390146811a40c10f10100e002801d140361002403c0700b1060450008038190041e0341409800048006607101120094295081c1003c9039142c2c03603080c0c014102199429001c808482e81c80200321a06608040c2441d600d075070b912800036050768487c00c0e180003120010810f2000e0580184203a81c85510b5070302e00204c035502d50f1f4941d440103205503603101d40c120000401c58941d162033002803522a864800c0c5542c0d4924110264041d54500d0319080d040242c00 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 665259163 1250 665257913 665257921
    0x210c1d010f0914151207060e13090206030c07030c0b011212050a0f05030703060e0910200a120b0306040b0702070510080f10050a0603060f0b0403020927010e160501020303 75
    0xb801c03e2031a000b04161810703500c07180008001404410400759840400d00c2001c00016641c0d03040703025030042200440e00d507002d1103100c08566060b2122000029844041000017035020100440a8080079020703161aa03007804c1e403503554448900080c0c204625050800f80c5000c100640500d00942d5403443c2d00e0064184407020802820803c1c0c0441d1078424003c0202c0000c000910951040e0014000641f031002e060a141c0c108648501d0385c40d1007041418103000c0040001c003c00c3c5644c94240d50b40d00c0c050782c81d00900801c1142d5803004440541e0040792200e4844125580c02c101682c046c6024105491040c2801076000e850030207254031660040140e07480f0603613140e4004404a6004c07104001c144c455548072034182c007044900360000b0794040114440490341700d030325500040680307820815104105868516004290166100003544403010030b0000300721145407403a030a5084a040007150301500420201429180c0386101d54903141c0c0038028011214a000814500501082c00550300d1428 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 665260413 1250 665259163 665259191
    0x603020910030b040f0c0801140a0b040e06030106121104060510020a02120c040608060a0e061005120c0406060c060f050c0a05031510030207050c0307210c1d010f09 72
    0xe401001074003450707603030039155880c3d442d5508400c1e0384954802c01002110380d0b442c4003400c481028055403120340d59200000e512401c040340e0280685031445280c2c0d080a10308000c44003403110080c600d541654036980e00196500036020740805aa2241d50041d400c112640b003030000301c440b1075000920504009655014184d00411140803491b0180c0340c14191640d8183c1c0d561500c980703000c0c0d86400c01d00c1c0200c00240d0100101d9802e0280c8400d44051180c0801e00781c5080d5520000e880324090300ba00b0f62400c11007450003036a060030200403803055a400000c2800005d0864480d503109a01081000d48007004103c124072a0a0002c1a00c1804000714100280c4100c61400392a00080510400002007040c1c100a403034003851125008101504540721044024007030f402c8207904075080c0c45862241811490040390b44404d541c0c510704405085100c21002c06d80e4503141041c15680c0c07a2000f840441e17000307440e500e41280f4810712142c40c2c01c103501d01404840242201e5110840051a041c0b58004040d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 665261663 1250 665260413 665260429
    0x905060418200a050d020403080c1c02010501061b0302012a03150b04030206210c0d1407020c100302090306130201080601091a09150307090f05030f070b0309030403050a030e0a06030209 81
    0xc0300f1490304948030300110b03070b900d0000e03ca5a00094145074000c944502541c0d4001000c0d075038190760302d071202d000780d50824099090350400e000b02030109403001c0a42c0c005400510014081c035009100108d10200c00c0b01d522070020b100070a4402c1d603041c0001c1c3c00161240c040c0513490441402b002100129403800c81c1150050055001c000d105500010b0f03000148420f0506000321920040c100d22214100140e00090a601c468444c115560410f07407651141c0c2c07548244103214802607009880103203400020050848001e210520134960709000f28096600c0400c1120b110b16010302d5000600e12003400054201e0718004c00325410095007000034852a002440c0d8290781c004403e24054903140e0360400141c515611843c3c060b4062404410059880e03489050340782220f4141e0386c448203040d2203100745521100b020244410f583d00c011410083c4040c543c0007544e101c3c6012066a084c162071f41c0e500360801510050a80c00111b81c0c881c00c0b21341c0e10308030203114010b00382400e08505c3d0070a23000100d2400 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 665262913 1250 665261663 665261677
    0x61e0604050a02090a08060f01140303030708220302150a06051c0201020c1c02130614010e03011d070608070203070f020f030c120109061a010207030210090506041820 73
    0x116219004962520780b141c0683e501200010540440d1079100c404c115929142141c2460513003200800000b500e540c884200c00710a1006000307149143d07079400b4141e8840c1d030081c080c0040140d0165882c450342610352030820300544203030702420740d24400701d92051803803401801d40e5024619205042109a03220284101e01e103480111520401a6500040c2d003000b0702c001440c0d8005500703811a800d071000c111082c0e81d03210310886d01110b00c1d404d4002c00d00b040ba03032140a240a60f203294800200c2c03960007401100c6020200600208407850004c0c8852240b80d64a8080e65103580590014408280c1105001d070340411070344029800d02c265a15950048003d07004040d001ea080c070106c080450b101840004038020340545a039102e8041400214001c15507550300792500c1c0c1c94040c042c1c2e400c18003c8003003501070703c05074010401203041d03400b0488040006481c440a1081030000061036481d0301018000404e4100baa11468680800d88a03080e40c0700f4140e1b40428583c009011514a15407409035440 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 665264163 1250 665262913 665262919
    0x727050a061206080d0903030f030507090506070203100c05030603070e09070501050a1215080c030312040b090a050105040c0317070b0a0b030c1201060f1d01050405220b040203061e06 80
    0x10074102c90b03005078010401d582151110340113040740c82c0901d03900442090205c911a603500108500010811012a24241c80ca840050441c0c14104244c0c40c000002d030000314001001d84080d41d0301d4501c40e40c2201e141141800100b4408801c0141a280620444006203a4110744119618020607410b07190441406003c1c1804004181c00264920030005000f0380d1103800010440480d100c800d6000d0006540708501c200c0c8a04500e10b11700303007008800d50300c48000c01d841440701510f8170354808000c00301c0144005540d20401e82140040361003405964000e500598107401c0460171814945007480a40c0c0440313161000403c440303030024101280d103a5102c80100b000040081c02013001908150102c503031181d000000d09000c8034821419405501111214540740075900e940340352070b00146a1445480c80101031603001000300303003015009654010000b5203400038500003901c00316140c1c1142d410544c2c0d540480f80810045090402016801155050120313010151203030192200100052030280 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 665265413 1250 665264163 665264177
    0x501050d0f060c0e0d03110f01111e0f0a0e150a0c14070b07200a050607030309060f020c0105070221090f030a0b04050609070f0f05040c11060727050a06 67
    0x4000780f0820304c040c103115000345030340c096481c075090061086020009400d6035005c0e0b00e140d200b890005115040c0e05ca41c000340f60b83d007003c604c0c031909659080603200500e410041001020808003000c4003c1c44610203544030b042c03940a181c81407000c907040c5004440e083e520b08011419100d40c01001880c0720300d600003038101d0740c19910b0b0307030540c00c1c03802030341c080408502d0100b000340401994008010200400c804200c1c00c000c060020013400400710301c201a04881c01300148000700e0700c03d401100c400c1d17029440202c0c00b030b45a494000101d80c041101e9a150385d654009129140b54107200100b000a801205800490382049808155105808145120300c07100f88540300c40b500d05026aa501f550008040a107614084c1000d9454140440c0c010483d0301070058003048071860010100c040d0380028240251050401007400000c0a070881c0c2682030006180340440c188404200041c416000b6076204900d10040c150400e008a00b003002c0c01000040250080c025626040d071244d0031200545004a = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 665266663 1250 665265413 665265431
    0x10e03030901060b2718070e040e0a0c0501110c0907110f0a022b0807060c091e030308060d0c0b0d0b0f18070c080c0c010809011b0e01121e0501050d0f06 67
    0x6e445000c0c480d81d280c02c0640704908100d02c1d1500059002d58008090b05c0c180455010a030015440e440c0c1010000c115160303081c0d0a002651003131039619208100e020850310101880e0b070000d10841421542035001403a00801c4203001380c01804640794051002c002030405100550008901c560b24828507142038807540b521400e007480c10341c0038680c0a600400c006968038454140700016103204800c01020550b140c5000407405403200465040000140d00d0b42c180d28152b071f0b0708880c0110b0281c040d0f0b600106007281e920103c0c0c00e0458003001441c90450351582e5691f03100e103a078155412016224401c2c0011401e0154603160040000c0030446143e501580d40d90b14030703005807001e895004021302801c101141c95600410001010061720400342c81e88035030f50b0b603000000b6007039540c52444507509401c1c0d00c0e004050316000d03104c1403100010505001500000345030442080b140c00700d0310b60300000111800c00f08001480c2c82414007410b0207a402c04a907454580b5050320140780303000010b0800380d80d10000 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 665267913 1250 665266663 665266669
    0x601051023130f0f14030f0d03020313081b070801090c0b07020316090608070506032a2709090316030f0c06050106051209030306150706020c010e03030901060b27 71
    0x103a0054035a24454a0307005440351920503001c3c607140200340c0c01e0006150140500d00d400a1f48895542280f8001c1003c601d000804270041e4001403c0b203495004480d00460008021070007078142c449500040398203200c40c001c0f0316131910b1010740c0001d07400e91400607408003003540400020300386e514584a990b982d103958408281b4080d881407003542c02188480000c01c072003a0799045002102d20301812503101503241d000b0800d152100360fa4003161004035042070b48080300400c6807080382001d58018181040c0c054500906002a41903031081c003032114501e0401c06113499555180c2042c003140c0214101400400100707801c244c1c0314809800d006402c010b030301495200f804c1d40e07400d00354802c1c8280519659070f0000740c4603030880c14550300d24001d05000500c0c20440001075a1040e04000c00d0b03008000324030701220b03440750700809058640c55000c01c84603055600902030104681c000c4c100a40e030700d1510011140c03c4900c0341d0880a0b00440030003d0842004100708200403115039502009000340e019000 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 665269163 1250 665267913 665267947
    0x4031b0b0304080c10050c07021e060313030311030f1f0302030102070f031d0f040e010914060105011101050c0307030f0e1005010f05060f03070305040203100e0601051023 75
    0x800c95481500004001c20010f10720050b010b1405200110f034107000080c5003003010350350212580c41c0d5000090000d00c0141c9041d500680240a1118500790341c00700150100318a54000c440382c51240201d40848401c040c0d0500c10010410600d003032080c21410030b10340000008201804943c1f50090b800079200c0044845904180150f0f4001e0003155221000d2808108400f010b850540100e25024080b0900d00b560807542410960002c04004280754440304000042001b0301110850350340e100642c500049895542c8886840b1460090160390326080005141911007081d014890341003000344000409000141c0c0d4100d0b0143c00c02140815500404a00401030f92410a44603ca000041c000c0070042e540800d041ea41030303042c1d00300543d031101c05025491086403800100d9500030000518114825804190070074030040644907070070100d1032900203451034506010150f42010004008502c3c18003141410141f580c100700184110850700c10010f045940b02c02088035070b000451400404800e04 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 665270413 1250 665269163 665269169
    0x114210304030c062d0809100509010911030a080a0c1e031e03090302060a0f020708030709080c09061f11070807090b010806150d02090d05031903050c04031b 69
    0x20460351581c0e40c0e414414054034041c4541c1d004600175840d0380482c2405541c08101883d0f940d0703101700303c1d40c13400101154915402404a06240294140344048c0d413014000c281c05455140004510950642810160201c0010416100b0b901c0705100d60001001641139841100b50790030a00c10103641030519001c5010702c0c1061881c0440701d84035403030805420824040c1a0305203281c0102c900400301c0401d500710307255044040c01503400200060160031b2160001d101e400030038000542040341eaaa0341000d07942042d9500b201003044103005003d848410080003100304011910031b6064208240411407a00c1030703140e603415104aa041c100100390040080c00c109160b000111036074155075030241a1030790310500540c00c540b030510340c1041056106901c1c01380a2400117118507447e12410726400802d40c88540e0b0303400ba0a13002c0c0300b00d0369113540300e0950102c00c80c0204041c40d61009100f08140348140340c0e51910701418076000170701043d22004020745007a20380c03060000c40740e140280a80308221300c0790340c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 665271663 1250 665270413 665270479
    0x16051c0c0e0705030901150f09021803030a050403060506060f1b1203010f03020a09230403090b03010905040327050103090c05120a021005041a0a120603030809150114 73
    0x4800c2c03102031584100114450504d110080103c0700031120740c40c0603070310180b08000304241021400e0081d100c40b640140348840c3c21341080342d061260300011a045401c4004250003007807001c54104140402401a2030b0300050071681c003458050610508c02e200d000310764a030310300e650301c14001c20001c0104004550b4032401d042070013501c940e035903841071450160a00089000711441100040c3c481c0c03640c001c0341c80c0c28005008400e001d5203161030401020b000280140d082020304800014044508402540a841400c001080c42d01d07150a001d01a0f08021400c02050390b01241204950030504840a003625400d1034082214038517402c00300680c20700f5812450f4454a0540e071a880b00d41c000445070700d5984240c900c200c0d040030b0480140c4440c0118801c105030541340982c100d03011460400140124000350074030400d40114044550101c6846030000c42c042810b003010b1164011040048440c400c04221603101e1a605000104440c44c01c0d05882d14024101c41c035680310304d214481074440d007000d040 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 665272913 1250 665271663 665271689
    0x31a0c07020a08010b13050903070f031b082a060408030c0708030c0910050406081609091a030c1507080c030f030c03150405010e1b0c0706020f16051c0c 67
    0x504543d600804007085050f02c035440c150b0307038500941c01e0303805580d1240d10b10402550402c400c1e41c81d805800683d1030400c070100220010202640780b5541000115540520003141d00c4d0740c140d041010078400c0820011450181c02d034211000d00b00700051302507005500c203601d2030326502d43c0c0a8404060080300b20007404000040700b00103c817003940c40030307051a0b40304480385400c3c81c446c0c4600741c6480c4240d019082c0010b00030400600800d041c41100b840048492130960100c6a6501c0301c44100d41c1c41c02c034640107501c10142202c1c2c032403908001042c0344580441c0c001c00c05002c0308684600c5c5126a08004107521030100307000c1c10384101032050320101048007005c240c0da8503225a81c0b6a25504c11103504030041850500340405051510459041e42d490f2201c0700320a03100c5800c1c28000c01d200c034002241c0341c3e8041094408808041c07101d4801002c26800800c030788107400640c0c0c0c0c2040c04d052558500750307205030703010031040e55003000300b640784409000503850b58070f0f4078188519404004e4006512175004 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 665274163 1250 665272913 665272919
    0xc1216060e030f1c0614090a05060f0a060201090c051009051203091512100b04030b04150606210b0f060a020a1205120601031b0e0102070810050f0c04031a0c07020a 72
    0x344d4010b003d030f5550040108203081d00c804440495003036060240342c10040700800992641d0107680125005000142429544031250f00000c42041c0b40c0c1c4c202070010307511940d10004000c0c0b005041d43c05443c044490400c0c003812000004c0001d00c1911030079102d118501d400c030000360b4040c003c41e60203040243ca4201c6000f9406414101350780510072440813601c0e0b250024203811182e00d08182070354680321285190502e191107004040d0000b030001e8440d082d07500c0d80380e42450711500c5104000d045948615075904405050400c1d0034049180941c803580c10040f000d0156503499040d40d140c40421a0709984401c591582285048003414004103e000908042480160010301400c00a440c002410803075a480700011001e8801005003220300d5800d0b800b06404a6015041102c201001841120b41059441c8605403038502100411101591f50350f040c000984203d070750703190b40310b801c0039840f41c43c080c5580e07903c410a003154800b0400f40b46a42006c079120f520400304441550350000c140d2401261 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 665275413 1250 665274163 665274187
    0x606031b060e040c2a050f160f030b010302040b1201090b0a140f0f0c0c0607030f0c02010c020a0b150307030b040c240305190911100323060609060f0c1216060e030f 72
    0x908c1d446440d950007003400006003c2403849580b9094035880521068540d1842e0f0030301c40501099100700e90b021691413800e4141280074802d400c10a40204411500d6080450580701102d21561138008201450300412200480103001241c1103d07111416070b14a136103200140109000fa180c0b41011801003500740640d032035254000ba8124460314078104a0f55031126010380c00c85e0922500680560000f00406000c503d00d8410941d002c0000001c0b03c0380301011600280c10803419410440c1c44244c01018442400754001218000c0d02400c12443c08101c0d81c0c9410b13021601890242c0004c06441d000080c60005008041180c0949503030002c2c040380c41c60f4607010401e01103089041d0b01500303c60000c810174a11900901b064207006241840707406d52141e201851101000700f4041e08030100300030071111500c65000404600b10b4032042651100c0282440c2c1d41880400715940611010500c41500c000081c880304030111a03214000207800350010b040a0300f03600031021840107010004c40c91200700301b = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 665276663 1250 665275413 665275423
    0x19020f06120f010609181a0303070302031c02030708010b0325050306010807050319020f13061d0102030a05090d0f0210020304090e01020a0c0b040606031b060e040c2a050f 75
    0x480005520030b0141c1c0c07500004c0300c208105103d81d0800e50b0180380c1c0c074900e0460580c40f030104042030790540c030500c14441005c41c0c6580d0003854101d0041e44000744c1c0b41151b100d40b20444480d601d000500354958248054001c00604041c0965000120b0010110f1050440e90461320b0441c401044074480d80c0600e0900a8070542080b201d25001c69403280014050034030990449204480305140701090740103c00c8660020b42140710f0000c0d44040c20441e4054441c040c0c0380381c0d401425950ba40c441d612000ca407031981c003c0c2801c1d2045040d0350050201040c41c1d07421005a407500326003034500c04240e6000b4102501c0303500c07001202941056030030140c840b8150b80440100b098445502c0240880f00e900d215581c02c0b8494840d40e0000104d28140250019160003025900315004180108981b5100c1c0c80340e144841450b541540b18000c001c81c1005400e0300f10b200c001c41050103ca08210450840d580600354a1144442294507410100d14400850810b0480c43c03085410070210380380400b100d50b1240c0c3d60 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 665277913 1250 665276663 665276671
    0xf030e010f06051c031b0501020f03010b0702011101060e0406050402031e030c160e060d052e110304030e0609040216111219081308010e0114150319020f0612 69
    0x2500291484d8135401649a220444003036241e179035046a80003a094140c22403900e5001255295001c100c0309801c80c20311005036002e08004010507586507580e01c005130240070070a03001c0c210759062101c20000701c100c5150707565000c2c2d0040000b1545550f1403000074209081c008004044c50fa01000c104601040080584203e500700400c440c40c510344281c00105800c81441002450045000090503c0c00d25604616149100340101ca0005d80503045200600821001c840030081c80031000b189080c0450181c0b91171010101c80492035810240c90041643c1c0081541c140102c02c0003030000420307140e0741e04490706000034006d400780d070510710314201030b282e0228600c15104034082415148506000700d150b10b204d00c49468496014a555903d541d26508004102e560f200d2016900107001032082c01040054120280006000e28401101044041c0040c0003110303d1090749480e07055540780020518295103c411090641959510006003007044002504e03401c61070106003001307100c041c2200c40e401 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 665279163 1250 665277913 665277919
    0x2190b070513052220160c0e011701051531140114041b0c020d15020703022b0503100b160507090522020d0204061716080a030f030e010f0605 62
    0x81c1865821500001d2050017115150302804102e580c42101000716600d20480c407581001c001c169440303a4418084509070f0008500c80e090100c03c4010b91070a215503648168212203084040310040c0204e0506148039502c1c400034080111403440400d4020498040c51988840601810101328201403002a0a1062619006d03000c0d07a81c916a01e07040c0600160512080382554500394841c00407140f108101e03a00342c4e000440c80c13280c50302242100c11803050000c00c41e03c001da41d034074076071600070318000742601a8102207003003041c40703402c045c110301c0c40580103410f0b4a40107031244c8410035403090620083d0b201c0c500f4142c0005080d40c181d14121901d12070b07140620169000580d44241355002d0340c104640c820941a16103103001e0a0940c040d0b091300382e060001e0400d0603034a00a5001c01d0449506401c02c0710450501c1401d00c44104040060300c01050706003440d01c01c81460000c4031565003003c4400101409018103150040d54481c0c0c1c48400132141c02c00080c80064110704404000307140718000c90340 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 665280413 1250 665279163 665279171
    0x302012f0a030608070618080c0102060619120b0f06010309030e06070c0b0301080c0a081203010e07020f010e0102030a0b0d0510020a050d1a010f0503100b03150d0c050102190b0705130522 82
    0x7408c40021403411700c0e023501a009400641c0e00c0504100806050128090380ca41510740042110f003026a13203030181921030701aa9140703040c12840705030341540c010180340c1054144144080007981c40543d240d540c0300162220ba81b10320b082d16101c0d000d400b09800c81590311741b0200000070f0580d8009000551030005487c140105a112038800e40c8410100c4240b1102102c00c00c0100015a0810f038201d511501610648500030301c0d11a641d400d44607126621030580e0740110901c00380440501c07507000b1407003044030450072200d003980ea40e43c0c0b50520048450784090380800c02050b942d02520071101003181740c000401103041c000115100c0504207010481c0020002140754404a0051044074003070f0b44a40d0807003181c249002031070001a07100805185208103140400c0801c2d807030303a84050140038454804c40c21514100f000081c40e142c070310720108419140420602d800f01341d0408055410010b03030b00d421a80c1c0d811040841860405035400543c105505004021035401038204850100e444880248 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 665281663 1250 665280413 665280419
    0x20109170406090e0912070206090603071701330c0807030206070905040203071704020307090f05150108040317071b11032505130b120a0302012f0a030608070618 71
    0x18a8085040b00c404a1781d5010b200d42852035458032003d041d940b84006c0a9030325191402c0e000c135580e034105a90240100d082c29907072088119000030031380e0141c48030392580000e82002c8030668001d1000d51144d18111407401e1045584648030300b540c1c5441c940c0010f500c0d030b030300c1a051038000c2d9102003c07646030000401444020400e8502402203a001d20165030300c42501d041450344c9250400d00262003203030b0511034a040050522450300a8151710502544001000d113804100e0010341203030365100a0402040c0c10401000030b030400c00d90ba5960944232542112075488502c00d86122070480003200903815400d0642e030800120340200301c400e84049d0159020890710540b42e00c603c201c00c030b04285810324491030a01013414070000c0c0207800e03069003501190311901c0304007103445205039030102031464000841c04001c0c5502401f4500900c0c900030203480c9100701b18040c2400002c01d0b014002c0d400c0d00300064102c8054401c2c0c010304040c0a808007510ba4a9030b80d820040c04842c0340f030300110f230308000e2600c0c00 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 665282913 1250 665281663 665281679
    0x318010507080c09100e13020414040902150c150a021b0606011d04111308150f01050409050c030714010908031903180b0403030902120609071502010917040609 70
    0xb0900a00d80400c2060a100001e420402205800c03100b04081003905041c581403595003110f4080350004844006075101c0c18940440203020040c9041c034003560134803651000603250200c40b41d00c1110303403030500c0b0380b1580000709107030811401c0304009409480d0354003801806026580181919141d0810941c44e02c1d4010a0310360303c070780c1e040384e12902003200c1107400142100c00e000040e079071010013400002d0524800c1d050300340c56000849600c0d41105609014071180900700040ba03080502811a442c10789482d03030b2a048001e0701400380314000c0d6103508000c01049401c0245a42c41c1d0402015034170312503114144020190a232100e6180004c002c02e00c00200808040105c0f0b1195001201c1103020314907441c0705401500364880da80321849000d02e1500c010034150703c6040d000d184a03680c0801d6602060040001051440f400b06c034098000505000220b10700107018000c4a0422001003048040000107a006102e007a402401e25142001c1020303d80d180000100186c40440c0c0761090500d4440c040 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 665284163 1250 665282913 665282927
    0x3030516110d030c110f070e090708070306020d090f11031b030604020f030c0d0303051f0e04031d0301020a050903120703080415020d020406030203060a0501031505060d0e01020318010507 82
    0x1080c1050b0001c5007a00050351294010f1444902d00d420060810500385950300e140000608118505400c030b40000d100340300d0030b62401ca4001c0054002450307014289402c442c1c6821242c80000d01840c1d0002e012240710101d90005045c03180c0051500c441a10181003160b90f1001c1040d84520030f0040c1c400344020303c000380c2007041c8040c1c00a03000b031402c2c0e6503a1f030034002c0d0b030b50012030170541c14400d0701813540c80d943e12521341c891032a211790b0f008900c0742800f09c035039040d070701d0240c40f80c0d048902151018041c220034140ca9540c007030303014540004100341244007443c0340030400c1c5159805500000340c07000701540080080c1118030054003241c015031800100b00e8014020800020001103827031001c14046550880e104841000380c8100600d0070840112440c101d80c0f0640c44800400e0300402084224a4001c0500d001000207003802d01c068200401f00e52500801c9001e82da1041ea40030482c08146d001c40c2e441400035031081802190740e8184050312445510380c03040c603141c5541c04c000c000b64606100b805 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 665285413 1250 665284163 665284187
    0x1020c090717060a271103041a1503030c03040e15030a030f050c1507121a12010e15040c08070f051e040615030e030301080303011e03080703030516 65
    0x1e0345400014001216031002d031809403515601070401c10000c00e10010b001207a01d002c1d03015240d84084c5501c8042c1d504291140c08401ea840408203104100116080030640f1b00100e04075103a800303040e514007034410000c4248a13061a0944030100b0300201048001009100750360380105000f145a640b08000300e0602c003011f8516825030080481038000034020408001101034a003000d034108442004410300e0040043c090154820003901806102ea820011000a1454403e8140700441014000000702c1d91004201c501499100c0f52058401c1c10a50181d500c810824060f2101517008001c0ca1004080648080c0c54165088000080b1140c001415004035500703603042c10300b0b01d0b00d0710b02040038030a50a213411030a03c001803511400e42c0d0396813150001031b02038024036041294403100010201d500c038800b040310b07551080005001c41c80c400010b480c1107a10343c80800c529143c8020b1002c0403204035074030041c01e0000200340c0b4010103403d0782066100b440d078100440380c2c2520380d041c102c03030b0b19201003 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 665286663 1250 665285413 665285417
    0xc07170309090c041a1209010902011707051e04171f090c08060709031101020a030c0215070b070305012112030f15060507050705010201381201090201020c0907 70
    0x12000d105410304a00c60b03070340404030030801c900b002e82d5030303c4070300c290074905c112000291000214031000780c0340300c0d103641c0d00510104020007138400d40c1c0c0d0001c0d150541b40302521000c0301d40c07440003400b5135100d06c04682021548415441c1700b401c48200202c11a04540504001a0700094550040b00000182e5034a00103039454524031500c01c00010000a00041c0400d44105401080108101204110890003120706564007c001442c6050001c40000b0f02c0410f241190003101d101030203c0c0e0300600000f085c0d0b40446e0951082040c02800100b180701312500181040e401e8000c1240254159004904a030100c2101d48090740b0251002507600c408044010104e50361800242c000c64403036409209100c1c1c0500c000110541800300d401900b40305a885580022000500c880c10000c00740300d440001d080c01c0c0000c0c0b016414501c864141045588010410008010001c07600c0080086008680c4130000c0c4c0000d1301c1c0000090715a001c1c009030a0168054810301941c601ca80c140340700003d11509441d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 665287769 1106 665286663 665286667
    0x60b0406110c01090f060806030a051c020d02010504080a050a0c0507090b0a1527050910170d020c130e0d03050f01080105040f08090d0c09020c071703 66
    0x100c1107190401442c44c1040117042444900c1000307990b041d00301401180d5586010a26040d940350002c1c10905c40c9109288031408402c02e400681400b030340c25140c2450b69194142d09840c0b042d940144851020060300700c1031480395001d0180c00d03d00d49850032000740345494042c60000207030014441c2d565960409403c03460a000340c44001d00c0c2c40c0c84088030613425071030080c11062454441001204616a02c3c0d40c654a00700002c60242c2030003030200c1150700b4a000d25403401c2c6c9845c003032101d40030200e02050181860024079400d13a43c8860303005004c1c8001d03881c1800100c00c3d001c2c1c40b4402050b25610350000d001d01c00d1000c0d8986201d5503500050518140103c0600070b00103a00c064542e924200510010607125061903040701c2c2c000701403565904146011402000d2590005000040c06d80d2011414a141d278000b0f0064540c81e4085540d00b80e01c0b200607440f143c403ea9400143d542c03003 = true := by decide +kernel

theorem cover : BRFrame.Cov 665107913 665287769 := by
  have h0 := BRFrame.cov_init 665107913
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665107913 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665107913 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665107913 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665107913 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665107913 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665107913 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665107913 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665107913 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665107913 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665107913 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665107913 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665107913 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665107913 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665107913 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665107913 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665107913 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665107913 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665107913 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665107913 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665107913 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665107913 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665107913 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665107913 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665107913 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665107913 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665107913 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665107913 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665107913 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665107913 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665107913 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665107913 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665107913 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665107913 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665107913 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665107913 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665107913 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665107913 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665107913 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665107913 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665107913 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665107913 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665107913 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665107913 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665107913 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665107913 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665107913 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665107913 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665107913 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665107913 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665107913 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665107913 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665107913 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665107913 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665107913 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665107913 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665107913 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665107913 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665107913 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665107913 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665107913 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665107913 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665107913 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665107913 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665107913 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665107913 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665107913 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665107913 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665107913 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665107913 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665107913 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665107913 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665107913 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665107913 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665107913 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665107913 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665107913 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665107913 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665107913 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665107913 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665107913 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665107913 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665107913 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665107913 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665107913 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665107913 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665107913 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665107913 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665107913 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665107913 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665107913 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665107913 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665107913 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665107913 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665107913 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665107913 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665107913 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665107913 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665107913 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665107913 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665107913 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665107913 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665107913 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665107913 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665107913 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665107913 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665107913 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665107913 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665107913 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665107913 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665107913 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665107913 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665107913 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665107913 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665107913 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665107913 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665107913 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665107913 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665107913 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665107913 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665107913 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665107913 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665107913 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665107913 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665107913 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665107913 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665107913 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665107913 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665107913 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665107913 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665107913 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665107913 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665107913 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665107913 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665107913 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665107913 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665107913 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665107913 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665107913 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665107913 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665107913 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665107913 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665107913 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665107913 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665107913 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 665107913 ≤ n) (h2 : n < 665287769) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
