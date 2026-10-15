-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3999
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:17:34.229522+00:00
-- url     : https://prove2.me/submissions/60c929de-6734-467a-8f7f-1d73bbe33475

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 719064748 ≤ n < 719244604 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 719065998 1250 719064748 719064763
    0x50907030e0d120e0706181d15030f0304090606030f02032401022103041b0f0b0d09120c020301181e0303090212030a02070b04242303040b09 62
    0x15002c2c0c1107a00840c1c4a01c0c0140054031108820190103d85480315800c4281054819401600403d0710340f4801c402034000d40f11030002503c074110003c2100822460140041c0308010715181c80c0c101d115429007850381e8200b0034038040d000c00c182280e544513211940300b4003074000384c4101d0010038244452070f4115000d030b0094910869001030312010303103a00500e42d59500b401c00600181580110a6644102c10141203420890440b000c0700681d42c2c1864a00084000030010300d000b510400075005200d0713010004009803c440312103101c281c0f50090100340c10010211710100502c1c05c66134510000000d6005102c59a900e07008074001c000040c0300201c1d071a0000c03085180103010050800d01003443c3c1300c6217900d481ea050700074940080d920f0300030360200ba009110403500e207040780d00101c1c101e81241d504201d000042c1c0300800031103050a203000d0b001d10035a8500c82c03025011041c0c4100c1c1c4002c4d5446030a6801440052030340d0740c1d41c0c804003840426041e6000703540a0752000030f680c000688041000440c60f = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 719067248 1250 719065998 719066021
    0x2090105070215090303040801061502030a09030f03200c040b0a0b09041d190b091f0e0c040f02090108091207020625060f15180c0912030905090703 65
    0x40d45085201d608220307244400a0546a03026020b1015070a41d8508102400c0a062402c1c0000740322410081600c800c0e00c0703000c200604560003040803a0360325501c0f88110045980c030003e44c40c8403070010f14003640c2d1076503014030820181903a014a10703a40740001859084152041d10100400440c0c0790612842c0170141c01400ba040504000d80021030030142d2207084516100c280990680e07040c00101070824600e4009560714120384801003003440200d580b20703a04545024014000c000c6804101e1085000002c0d000e00b120380e44040344e041480d400e101040089100800c20070078011015401002508110855030015100e04002217901d05c0c00901c294500d802101a5400d00000e5404c101c0301e50310468001c1e0079100442d190031910513444031351341c403403e11a050128881560600350320440d45022180303a140f51020340d04201903051480c1c1034194110400c4c0210302114400003c1d100112a0b5110703100700c6400d4040c480a06070302031001010703610704881c0b035046522641c40440580d009402d58 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 719068498 1250 719067248 719067257
    0x1020315130c081602010b0303040807061e1e050c010617010e0105130233040510020a110405060109030524010e011505030604110d0b1002190209061c060b03010609020901 75
    0x314003495130380b00400f44480c02c81d01c00407603a44004004030f82940c01661003409640c0c070004007030000c1d03500b103030450010340c1c0510f100000f0102001340046c50302e84c1c1180c0540c2d6040d6113544c403190881c410b2084544107054a0002d000c540e503103282012100300c8002c0c2c0c5a1441d440c1100803940d1800c10f01070a4014000000c90503055500c41d000c0100c4040190810031031018508140c0c0006450342d03408884080e1468000c5448602d000c0511410031824120302045402c00044000090303a5084548401c0c0020f46001801d0368070f041c0181d03207a0505800242c03180c031414450942028049801c640c01c03907840307101201e850342c1e5050740e040718110030701401071602c2080072042007042c0318070050b5500107401803000c140b580360000c00c0500c1d81d200f440003012041d00d60000300070509115036003c030312451510091100c121243c02800010b6200032000307200d10b10000107d040cd0380c500c00825841c2c43c0c030303003104007282d006460803030010480090040e00035407c00000082c00c4030b851003a0b846184044c2c44 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 719069748 1250 719068498 719068501
    0x609060c04140f03010e0708010506010f09121112030705010203040210080906040b0405070902030106020c0102060f10124b0b0411150f0a0909090c120807020301020315130c08 77
    0x30401c0b844603180545415645c1c0d041d03602c6070070b4007c024007070013003c84c40300000f0241880707000102440301d00d0b20700030b0a01100000401108c03444d001205e001d59005010400b02070500c5000828410f0094116030841c84080350700c40034070a040d4000c40c0564800c5815000090a0781400c3d076821804942034107083e04403100140c0401e0042c0891381c2c5c890b103c0cbd000d5800c4140c5481544089801c20381000b001a40a08144002035804000d610740004104079049290b00d0b180b0341e1011031a000e8047e2640c2080458150030420428450041c1071001d003000108200050b1112030010420081c80e81111203228600f80039015040504001e601d030b0006100c0107035035120746078408907448000000b6003040c14040c040c4030a10452004c0e294404644950503074070148010024101c03541e80d04481501ea00d80905c9900003501100c84c4021120a41c0c195a40788080d410700d161907028449002e0b40550000040184507a002042c04500702c20844030600008440c6400d1700442d0781c501c10081c0403801140 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 719070998 1250 719069748 719069789
    0x10b1c020307030312020702031903030c081005040c12021b2806240e0a0b040501150e1504030b010e090f10050c0706090c0501030506180601141b0609060c04 69
    0x1d109012051170700c2d0000d89091b000703501081c50b041c16200d40c031351020030780300c0318604141c0e040c0203011117248a031034260418280641002e51315582481240c1c4a160307640c0c0c0b03180c1c0315405074030424001c0548000c1107445242d24090080001c01c101040301c854020b03091150114080303140d42048084900d01044035031911541d506004014011220a440054010303100002c0c001d03120100180580d8014209641022104042924240c2d0303011481607081c01c0c0180940358000200b205030b41c006241610100c4101800300b040d136014800c6c0c3c41501e5000050110521285100080c103d55a1441031002c0e0341d66190403a49601031582c950200b40c0050a0007030240e4982d170840c81d04034000c06000d40c40c0c04070580d10b4400b1203805401c111203503d180b0303030704206560301849125804902a5406104034050151440764000b00500c0d02d414001d009800c851400c1e101c100762000e00801164502c4002c20412403140d640a04440000380d91059030009000117488005440844500d0215003000c0366946 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 719072248 1250 719070998 719071007
    0x30c17010506130e04050f060a09050c04090602040b041508010902040e18102301050102030f04090c050412030e1306080c0103020913090311070803120f070e0909010b1c0203070303 79
    0x3c00304107a80c407020f1040455203000d102013440c0501c0c481d60042a5104000c400b550502e00020300c0715900f5840c20f010b01012680c00f150101e08010100c3c0c0008080c2d1151914a0080c01290006680e030180460046607107241c25045111400c003a44640c0c159a0383d8680040aa107d11b002c0c0c1c03011000220007080183c00106400c0b0b450113000b5080d17941144420608104960168014017603605484030071041542e905044e41d03024001c207101031454142c0c080d240140c00d12440c4a51180d041c0d4a03044880c51b5882802a100500b10708401c041c0c80054a0400a00d420f0405e41c42c20b00c250200301d1480001580c52140c002280c1c0d1110143c140d4016000c0190002c0d0046800da9404c00c1603821100310300d040b244941890244030780c80743c42407076408882c11454080c0e00e42012000b58420001400c00006000041c0e600413000c1800c0c40069950348400ca070030300b0400e4030f001d800084000c20301084a9064001e41d0844e001910b4108281607003000c0d10646020303800000e90150451a01403000ca40308 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 719073498 1250 719072248 719072257
    0x5100e010b2107050405071805040b090403081015050703020c09010f150320120c07020109030f050a02090f061c0c0e10082a0f010207051011060c0703030c17010506 72
    0x1030b50644030b040da0343d440820151030084036a800040c00b285060a00c00700c5594800c40500700a51702080320704800008240041c0b000740c409010710507401c000a40c03a40381f40e02040098554104000700342c0007440c0d80601103070411481100540601c1030340205504007241d1041c121611000c0c0203800d5490180030804140030b041c1d2003c1050b84490084e8440c1c1075001c094114a041d00960780d17030700c2c02c1200c040c1405003406482c032900a881008030002603a07004031590107590b00140e60040000303040c544246840f0846500a4218042c41c04020040e03e82003100ca2181005072502040240c580d841e40708800441d103001418040c507940c00380184490600d403140d0107c00b0114556406031141810380c40d0490828103248400d5001e010780002c0c206d00c1c10703104c2c5c00703040a585600301244003c00203501c811090040c14094207000c1031003503c1e41c1c854407400c4055000e032000d80e4014240400f5242050307200d100240c0200f42000200089d06220707418002c42d000c910031007061581d080070100409a4030 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 719074748 1250 719073498 719073559
    0x14030a030f03060e10151409130605090f0405010b15041403010e2a0607050d03050a020d0e06011a040303170a060504020f070b100605041a04030f05100e010b 69
    0x5590002240c1070203804d003164003a810030f145544c0028504154194941480c0c0f513010100101400d091280041290680302241e6040b02c50300c0d20040026001c034014000750348001d43c842c03d00700034810203040c0300c69018040c601070002071003004007210503c0892548001d0400001e84100020072240d2114020010076070b038024008200d68405c00361243c608035414800191420911109421104078000446240c400607100c1a040c80099141c0395159185580c0705c1003415140c000140001c5001c0d17044406580c0c46000400c0b03c058180c0310960340c0c040900582d0040060b140d80b00d48428007035130564080340e41c16a54040d6000619104492000000e0704983e0b86903212074000c112541c40d40064025922045156509c0354110305203218204005000c4100440400701d0900000c0c2e8000708139010f5406001e55601c0084c08106420800d00c80d83e84090a14070803898030b10100000440d18580c8045018014040d0300c218031b007500c0c01c9444403c10994407a0304451600036204d0000e15081c4900d0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 719075998 1250 719074748 719074751
    0x203040803090402072604090c03060f09020c0709060b090a0801090f02311406040e0303150d15020415020601150c080d0c0e01110c0609040236090114030a030f03 71
    0x80e5101d070f2086030001c050100c01c6e00620202c1c090060301d0240c402d41120310380c103203820300c1900d141084a0601865074003407500500d400150301c92490504003e07c17401440900002c111066a60100e40b519801890040f8802d0908c0100007801c417105001d0588696040301000d99050710725401c000e00076021001d110000303046894845d4088010740a400e403c100e0b4400041000301700540d524003071140017411f0b584980c0c41c6c240b4100000900000750303030744242040034420300b84d0303806130018404130030b005002458107072005220740e82081260090012260030350100ca8100c040000280e072101d10901805860303901284110102c18803c003206080c90780183c0c1003030b01c0c0c400c8500d1110709440f440c211880100d403c1442030041940d11510b5003800b880c039030002d0007502c11844005419442070312803da01c516000326240c042c0f0004115581c521070f4a4280c3c2500f00307469084c99500380700040e003c240c41502180000107941015869480d84c200000f40901401e80301c940c0d080e00e03007048608041c0c0405 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 719077248 1250 719075998 719076023
    0x1a0c0703060e0a03030b0d0c18090c0b0c010623060a05190c02010806190e0408160f06060e1603090302071203050c060703020a021915050c0316020304080309040207 72
    0x104907104910540502d40c01419151903281000f4003681c03c1d83d10540c0c020b001c0d4040800c041929504400c040d1450401116004464603e6200c058903071501e0103000a241c94200280070030440c0300400100e650702e00248145c2d0b0391011304d444203803080301904824403420701c152209403525900522140883e42086400d202e5014420000c04d00c400b0140310104640c45282e000390341e0045806070348104111003c0080c011040074212030000503109881c0590300c5040442c003007000c0300040e07998440302146000d800d45107034205050352a20100c4243c486034944180400c0c14000b80d841d46110300040000101405c40c0400102d008000182084d011809085000700d405410320074617020761406a5119512466950441801c00e900902075000703040c070400c0408081340e00402d0401000300754020007616041c66040c41e402c4110254046d0088510702420440300300c103054003031405086480300c5202d50401c0c0d4082070741d40b0711890040d1007065006018500f41480d15070002c0c84842e01c1102605000c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 719078498 1250 719077248 719077253
    0xd0e01050708030405010c020c040e0d1d10170606070c0510031b0905040506040504170703090e01150e030c01020717150a091a010b0403060e0f160603060605041a0c0703 74
    0x883d00240c84c1141c081e5120141810070560402c1145c0203008121800c02041140313280043c2d54501e0030071003005106111118100001100114001180c4084e10044044c00d10140080a11006102c141004002c07100421098100b003c20303501903581c0304003202d55150030002000010411800e8840c03c043c1c0742c2d6440c4001e80010701205030001105c0d2280c0035514144000c10064480c01400795015500c0c0000300004140d19141141c0c4201591640640d00c41d554101114034041c0c035008102c20720324180001a210015059545841c4003d5a95076000b49030203042688481030810200c1c0143d1104030103008102c00d011b03040820380042c00854103990110071201d5454102280c0e809a0380355075065a800b84400070100f002000d05101406242c5c1d0f0507c0980c0c4d46078000c902000d894a40d07206d042e208800c0d010003001c02007188880440302c01500f0030201c3c0d0b816125034000e00c000282441c01c005030b2140a10243e03015940d03910018926541050a50381d03a41e001441084401d12035131000001 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 719079748 1250 719078498 719078513
    0x5060a050d0b04113a0b011b051c020d080a05090f0106031121032a0a0506160e0d0f0c030b0a0f0c09030f020409050708030d0203040b060906030d0e010507 68
    0x3000031402100740d0329211001441640c09074580100541100c08003407500d480c0b00c01109482520500036400200c06c4110f10048807108511a2031410100c1286020420700030000b941d010103402d1802804900b006a660480c0c41d02c14002e00d00c2d002c9044580460a24516504000d9110f4103a108813074206155020103820740382241e0098440322a01850701105040550382d229a4190032082450002080000c49a4034403506604103400b2421418100164040d00c0b400720081000008541e489607050504c60340740c0c502a106e0f0001050700301000042d00380a00c03803191030b42c94000c1140300b000150b0340700c1e190080303101d400403a03ca0320220703001b200040b403031645640185030301000000c0f0b095404940340115000403130f0700418400350080030000941a42e00009480d603050fa0082030008051400d80d10b801c1c042c0c0c0100005000c04506845000d00030f5020703610481c000d00c240400d649030242800034407030090b2070301500b603000030b80754400312030107011044021503043c5051460b028440c2c41d00b00 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 719080998 1250 719079748 719079761
    0xa110904110d0509030a0c0b131a0601020d0f0906050c2415061e0c010609020c010e07090b2d060a030f140c030118020c0105100509010f05060a050d0b04 67
    0xc6001051015500141d40f103225480201c5400851400c8555080a445684200c070010203810300400003842c45502c1500382e4020991100922144051040b445840b4481c1106e1144c010310900501e501c441d442200210f91142203512140c15460404004860b103030700c2403580740d2540c07040e035134642003a0a0301405c41000540600d6080c441c1d00301000015040f100d039418075440385a003401031115882e0285c40c282e000382e0310413400b20342d00c014040640d80505015484041400d10114007600603040640045070913a01e506d040c1c2d0905606d620b80d075821241140340c078a0b08000e08242d43e100340001c10107104252520703d14195100074841000420a5100000200000f900c0d6000c82c0100c101c2400f400514041c203071410300d29881c0510240305940014440c407044068855240d0650f14890750480e92a580044020301a600c0c00440b091380001c031a1240394092440c402c00015526280c0b0700240c1941d200804c040c0c9006640322045600c3c0d006164811740c0b030b6070354004410503940c5038800c03003 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 719082248 1250 719080998 719081021
    0x510050c060a05040c23130e0a060b040f0e0d050f04030b16090806090a02041104080a1b170a0b04061103040309060305160e13020f03010e01050a050f090a110904 71
    0x8503507132400d803509030001c43d410f521010f51502d900c0c1407050048035192203000c0010043d81c010702220300807440740025007003c511604060003290580001d010f42c58100c030005240c00d41d03050008201245803c400c9808403501d03010290860b07113000e003920f403003403009240c8a0903a448140c1480d450f82c941120400081d10308003508940341c42803c18a582210408008013402d1000d007450f843d14a2380551600c8001400900c105e13a00d40c070058101c2c0d40181554080e220070001c8554270340305407502501c4440e40381c0c1d2161300c0c02c0c03100800068080e4202d10642411034560054802e0b60126035440100351006081159901d44401450300001c50410140d880346000760b50384414240707401c0020f4112a0050411544521140a1400700642150072000b14101c00d031514194480803000716002030003122607640c0803a03000000080d2012003140c20b981038074000c4502024803503441e010040310690425156800c00b4038900065079540d02680a1341c0003455410200d450507503400005030440f080035020 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 719083498 1250 719082248 719082251
    0x50f0409140d1e080403080402210a110405010b07062307050711040e12032a0a08010f0e060f030f0303090d170702060c0c030d0c0c05010b0a0f0510050c060a 69
    0x842c1c0749070b40311041404030500086003412140380e200b0000c03c00080100082c0600c4201d00c045400c644505c011182d044911081ca90035400301d441d2001d481e50448407040d15402d9201d03400c03440ca45058410745040b146000c0e4614681681c079035480d009800c41e544401c022420104000e0401d4202988440c4555a00d0392030a6407401d0515003c40c10804d00d0700001d00480c0f918145800c0c0440000b240b42e800e0700f12000300c9480340d0b01e01c0807a44440c81d034407041801c0802c0e408008110000450090801407985490305601c980e20344006e80e240361040c2c4501c10303030101c0d19400b143c0682030646a0b0842c01c100901910510550728400360701d55402500c11001e03030b13031141e1114801682e100036109168060b18643d48260304055000075551107014103500302400b0006020041e0b034600700100d4400b0381806005010b540c20609000d408040c401c1d0054805508040303c01e0000e00d0720800030b0382a00ca2041c0b84445503400d00c0e042c0202009018510b009003e010042c625034400c04100584c03040070310900 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 719084748 1250 719083498 719083513
    0x60302041e06080c0711030a030c05150c030a1113060809010b01030b06031f15021005090c2404090f0204150c08030f101203031b0e0a050f040914 64
    0x64102441019a00d1540c89560224007800345550140c0110b030001d0200b0748045d1246031900b0701c501d0014101c1d144a516105e8070a42c3c4040581203405601410b01902c2940c0101010040c4510b22a208643e42902d44400f0000556818000d501040c003204060043e1810100c07407954141807042c0c02d40105010507040300400410038000d00130702039400000e280a0002d080554081103141c040078090315058400030640c080e0801c40380f8142d200030201c41e450040c88090301c1da8080e40390500b6400246426040c14005440341000080320015920003074642c90780708002894014002412541c041e00f0040c2c100b100141d9501c85004000d424409080010303078803842c007401041c40400d00d0003140c0a0090500107940899086419240e02400d1038641914540c6d81078118161330880b0b4001c0c40851500003200001d160b07169110f001814400500c0c01c4804d61440b0007a698510710383e440e01d502c81520541403055040644d02c0c00c1080c0303400b400100300341d07a0951312641041d849942280c2258460507 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 719085998 1250 719084748 719084759
    0x30411190b131e0506030a050a09080316030c090503031e0405130b031b01090e10031a0a05060616060f090828091a03190606031a03032104060902090106030204 70
    0x40850402c010b520f111841d0780303243c01c0204100e404020018246103648000003a07812441350030140c1125441060503030380340780c01e142c041149500e290076100000d246c0600302841c20701620002042e148003d000f541400c243c1010b40c2040903280c0c0d07000e003400c1d5081c00b00003159210080000345d142e20307640700030840550b40b0701071601e0144034904001085e2408803022000d40d82220030f030030580744030141c104030b9903072200d01c0fa00041c40d20740d00080062040a130207050700c2c5440d00d0200d0007140c0b1000d090000c0d888010804c1205d01406c010110340428070780c14500002c81640c003210705400002d00229515245c0d0f1208012600440e0034200c08644c103041f50f0740007520b00c2c100e84a508006003000e0300060f04181d00d588840c5103251500745451b20001c081044c03100240840e81c0d482e00a04018010143c9424000f4003030500f410300d4409c002110104689240350210a44014440038000300c1c100b00d028605400e29050302030009d0740c081e41d0300e0034180c000d0303190b68175814044e0041351400750381c492a0a = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 719087248 1250 719085998 719086019
    0x3170402030a060e0a200a050d0303090b074113050a060206041a2a120a02130602060402090f1009020310050a0902070f080901050405030102040305010f050c030411190b13 75
    0x426950018803120820129030347da0320506801c0d107c06469080d641030080c603040e802056030a601524140300d000070000143e5001e00052005034141d0300c40f0614071071484e40c071866501800145000c2e1078945035031640504100d40a4000c000225005020071507588010841103c140c2e0440e00060b04441f0810050002803660b8008071000b1620a55142c40d2400340b40c540b00024010101d811115441d4000b20319140c8000c1d00c00400140e01c4038035003410320740307650307002540440c0706520010030301007000176041d00126046104640140c00c0b421243c2d62072403034103031840c00141b01544900c00207402107010800791001d544201110240b0803c8223003800e0810a09100310360115001d540104240400158134650407201654401c94051f1100d41510069422340500e41085030950720102300081403003015000144000e005500c10042525040b000b0341043c40700300c4020700002026515416181000030b040600c0c00f1900c1442600a0f03116106124a50f0010300c1a045001c20500188420100d6 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 719088498 1250 719087248 719087273
    0x6060d050c0d0b09011202060a050d020a030906050a0216120c080a020a0317160e01050405150405040f2d140403081902130b090d0503191205010303170402030a060e0a 73
    0x4413140c041d15850294a0040c850201600038000e1201080b090f0302c0300c0c010350541d501c510003281e0654454802001c02001000704000554940c0e041c107021400101091003146c0007201911801c1d00c01618588495440703004296108081005503c40ba10200300c0010141c4512489a4080c01c070800050500501148280c000001d20203110020701c4800f0f10500004404044c042c1849008030004500503102401543e000700d802440c0e03491003051280016005000b5030f00100c03001c10254000801040849030741d17100440703030900c40f04109001c4004105c45008800e850001c0440e10403031109803001000400d0300c4c1180850109011711086c81b041046000251403507131011400e0030350410304001034101c40c0c444c00e01b0190340080e45508070b4071420208405540c0000c100c0c0c6e52401111003605038640701109031000900c107081d651031500e100f4024541200c0d01640c4105402041070700b000c5001d14050001ca9052040c842d4201c00203c040c0204503461501c103001d001d0700200703030800c017040080 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 719089748 1250 719088498 719088521
    0x501020303010501080412180909061113230d0605010e13080a0315030c060e0a1d0103060b041b02010509011d1b060c1204030c06030216060506060d050c0d 68
    0xc140010300859078080c10590340a0f8115035131501c415020403003500c40f12a0b05402580901c566000490060f00300d40250001070301c0761004000c0c03134a024589200d1800742c8940f0301e20760014400100040001d043d1250117961640c502041007040c04000500d45030031418003112100e45500042040141d030410a940c0000c110295030340c2c884865554842512039000782e0418182ea58005981e0714942d822680080c41c0c0c0081100e00d113540b0b440300648507a4030b1491040c07080705607030400300328250324090850400c2e02c062240005039085943c0c200192880c0300035a0341169a07182003800700741345400100c518290030307000040d407801c1402c0c1c00d40c00c1d43c05200b804a13a00b40c041040292030388000464a122a01003000403c400000600150b002d100e58940c40d4175621401c0d00345500912624000c1049074401c045142d60555545c000f641640103264106550400481c03a60020640c6a00a1584080010010303440c012601c0d40910171540141c1c2d50642140020900340c0181400b4480c40e04800c0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 719090998 1250 719089748 719089753
    0x1406010c03080f0a09080309060609181c030e0d03060503190b0c0d0b1f09091a190914010311030c060a03020a0309060903021f0e030702010e030f060c040f050102 71
    0x40351501d02421049000c0c1225020766100d000082c009031580d1300200381035520201c0e04e07507a810158925540c6040135150540f0030b40d08400031590329099030180744403403044072002d42520781340d0040380c1407082800c150764410300d034450b030210111550a00040c0a0100e05031000600181000305141c60b0448032103480c1d00b0692100610300c049031180a0887d4005452100c00d41e40e420708042050207040c00c454800c1d00211101441e075800038030003110340700e0300c00c451350ba10791216541d000b194280c1c0e40e449030600c2c146440b110a00e0319800d0811806807a41c040482c80b011051740e81c20f612044400101248060110070401441002550304508440e030701c0440c000c00d00d0400090020300144944200da405042d80042c100120a009410180c030813500180104101807590074003075240c1803d0540038410481d8050140300d03001e0148202c811a07491400110b0034030a40783c5c015500000c40d9601168188074207828460002000c00101d07200f9003480710b046403601e14000a040540d142a007010717044d0f4 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 719092248 1250 719090998 719091017
    0x9011b1b1706060f03030d05100e04081207170106030b1503090f120f09010c03260702010b0307060806060f04260d0c0f0204090219031209050f240c10140601 69
    0x5941c0081551f0900c02d910a0000d51519001e50f030b292128565031040103180b10b50410001403100180c041e00c1b046041d40c0c00a24540d80c0c3d40000c070740c00b00c49400400c9040002c0070041c820130744280d0090501c004080c08100300711521400c2d507042d540043b1000700e000d9010711105503405170180058100c80650440003420003900300d00a05aa00030303011080e04004040d00c4040070302d8072807002000c0117500089800c180030440102844000c000b120b1040c055828032000126505000881400700c4130a03540d11505501e4050400009510800c6004ea03041030510002c1016048140c181c001742d14030002041c9200001402c40e414022400c0d13258060101204466000c2102004400f800f654101d03400140801c0900c00590b21800c425081c0c000d00394802804030411120a0352101c004203a0b85402c1a502c1d80d030300c100002c45203440c1078290020404c00004d40002e89010011501d19200c0d0710490400b149042803500e000d00011400b034481c0d0310303000e180f0a645031251045400041c01e21348501c10 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 719093498 1250 719092248 719092279
    0x603060315090a06020d05060a12051c0302070507080a0b06010c0507090c1e0f031104030203070b07020a081603060c0311031512100b090c09011b1b170606 68
    0x1c480181d103440c1c510007203001c00200310b0201030000f52030641d848a4110b440f0080005078000600c1c00300c030040e0190010f0320000c101c0626840c00d254846500000030b100d4641842c00e082000000384140d40103042e000e00844002540c03e102c1e80d40030300f4a040040100e000e482c18000044500079203c0c50601600c0340b203c0e0045400842c45400340c8008a00204913508996411140f55005229aa040c0010382c0c50a80384950300c0032115030741c1071040c1d03001d0243d1005000d55800d03034840c5100007503041d800541e08012455581c070190050600042c821101c00b41c0e2403506506082c003002c100d6000a034101c4007841003120501c10902c03000011300d820402d8150461000b14140b0002e41141a866007400980340d90390758203100700d041441e041c4180c51021116a2004002e0012824400c0c4602c05810008111161002c01c2d5146402c0503551f48c144900010003001c0f42041c0035500741c40072100803030700320045141584c0b0f000c003d00010350310b4600240140c000d20704003a8040c002c144039000340000b0214 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 719094748 1250 719093498 719093503
    0xb15070b0601120f0c090501030e0a0f0204061a0309010c0921050106030602181e010531030f06050f04022404080a03030207030f08010302010504260105041103070506030603 76
    0x9255110040ea241511a4001a9815009083c0f440769680c01c1090301401c401450f08180d4983c0c0301d90322144d10041c0c0303410040d01640c0c1d08100e20707107480e40002414404500213415042c0121300140000980c030303886802065030440d01d0b0342a540d40350f00c000184481643d00740300f440402d84035482c2c0105440e00703098224034030486079040503644605090885060060030b5000000070740d440001150b40d890510941044082650f120a10408140380300c00000040b240507803110307003016075480d0b1405007425501a1600c4a031110142d234141e021400f4200c1c00000303000e60000d180105603d2000e18201d281c500305803000101041114400b80c0d040c080181c4844d49001c020150390407902042000d01e840745411406103a1020820f441560507400c14143c0560040c907a044c02680e0707803d012204683c0655144070284402030015204000801c103414a203040050311314088149901d01a1140b210a42599000e07502074594081610f403152684c60100f00180c0100f8041d5070942c114904000081d8 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 719095998 1250 719094748 719094757
    0x30507090902120a09020102030d0911030c0a0807060f0210140604051f03172101050307080303010e0c1b1b030d09033903061b090506091320030a0b15 66
    0x6000703441700c40217021a8028030070341d072600d14a00c90820503c441c80c10304010328841e108610780280a802803140203814400541819101c01d880200300b683c0c50b0407408c07500b514a042c0100214003c0c0c10354942c24140500a00c2601c0c40c035411000281c0c24507404100440350082c1042c5100499074030080360002400400004590704040940e02825822034040d03420b1280c1c00c05005804440030408409000f12048541a548164101c1c1c2c0090344070400c05580c0d201c2070141c001ca03222044006003c1110000041c010f42e150165020701a0050900c21441c18841c0c3d00042c8110f9403082c1c0900040c1010088200320000e586000c0c1c103410300e9030703e46142080380c0001b940304400607030300e00d0004803250604211001c1061280030041559074186032004140c001c80e410b840804404503124500e1041400c80c09691005180600e40802541001100d4191000e00484142c440c1103030b40040b6100c0b00050500311002c000a90f0300c1c5404194401100c022610075481401e55411181c04e140008c005d94 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 719097248 1250 719095998 719096011
    0x71b02090622020a09170d0c0809030a06060e151e120f06011502010606021507031d010e010b190b091e04050a090201030e0c0303190903050a0303050709090212 70
    0x9500400224562100b0b4034854829a14020b00010705144c5165000413100200d80c030681c005c100c1c0d14082c0900c1c071b8407a01c040d010701c40000c6824541d440880c140c44024000c0010007001c542046003203540d0382061302d085034002035102c04054100030100080b000c1e1082402000ca5a00424441d043e00c0440c0004100c1d442c1c40c060186c14208908002d02040010708604044084030010340c1e450010141f6561445003000041d428102c1c0050924000245500c3c0061042c150700c1d00c1d540d0744c06080340101500d0b01c21901c0005da101c100c1c6007a0b0000c0c82803010b414000b000101b0141020740c00d00c118807a818145d4460440f0b40c1104010080205c0c0c00e403050b880c400c07500400c180e078100700d00b541a010342a035a035502a00d0031050050b030f0748403070b80120701c0b25100782c038240030314039211901c6034450b40d003410342d190036810410080d00803404100d20301e0180809403d0a0b4420794594031000e1030103281440890109503208240880190000bc4070002049400310540c0ba005056200300302108028200 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 719098498 1250 719097248 719097259
    0x270c07080f03131a16021515060f120118090b060f24041d060a05190305031c0c0305060f12251e030c030f021c0b0406060501030b011710031a071b020906 67
    0x41c64459a1500110760303107042d40400c003d2f101d00341310b0714500ca07071503082c480d41c004801c4941d1040780a020030b0103040c50345074001c51124042c3e901e203070920514000700100b03141c1c0b140f00d05101165480900c3e800d05c0c8500440003601c1e071101d04004958007400035104c40a5070740c0c005c03a0200406541c07a0b00704581a940c09899000003000805295013041c0995000248a800040341140c0d2210b4903c4101b48000c000320003c0c01003881e10b40c0f00358100c480c10f40b2a50b030000160003403044503081c284429021101c000e01141c95401c08100e092107180e803400e488946610b18014108007072121509008800c01d0044404000240f40d5511351020500921000740b101d0a404845001d542e180d4214044815680090003107212491600c0801b46108441c11a43c00703140203000310300b552092003900040070068442e08054480c503461043c0c680e00050260610001c101c0010000521810019008401c0501030126905203620050000711001400e00031014107000c0c0200503a41e42441c00342c009900b540c1 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 719099748 1250 719098498 719098531
    0xc130b15090628030c140d0b0a08011d07090509030a1d040c0c030201050c04051818030a0512010b03040c090515270c07080f03131a160215 61
    0xb04102e4012111042000603040316008420884649582c00c00700d81603804101d401d48102c000e40d40804113103440007000c031003400008451403d0f54442520844020441c0d003185039642031050070358000c607000c408070761184006880c0c0d0031401c0283c5005000644810301180c40c01c01c000c29900c1c014048030100700800c449800a110800c1c2e20004500000980300784444007640d080607201c0b4205000c105d00541ca00300c001030503203030100300b90b409aa80c01001120b82d500025808442080058803060882ca140041c0b0150760301c041005243c4e150090322801e480b410003007000c0140b40c4050384184801981082000700144a4044410a03124400000103041d203800004414550078141196085043c0c04552104140b010300c800c01d081c080044101202d650f400c060010b2402007840c028920f00c4184070b06411031180c9006140d0000c4240496035100e1038039151012050040207048030080946014406040e40074240c20007400300e940010a1000100e842855803688000c090035008620b079030 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 719100998 1250 719099748 719099767
    0xa0215070c050106030b0106020d18050103090804090510030506010b0406080c03040f050601180b04020f1912020d020307030e010b0a05010e120a080d05100305030706020a090302120c130b15 83
    0x901c0800075400c07400030040240c07070703140142c55a1001c0c01040054411580d505400c00c0c891000802c030398081d000c00d107141601e0702006601030801d6590807214000140004a120f03681482114800c095068694803140c1c51414414205041030b0070090b5401c4c020401803209680140c003aa42002035041500e0b560354550402d0f6410300041c01d4018000d01440d0000070310801c2080404215600c01c0c501045038031001c0b000c0008078881c203024168200800d00c54802120761811b080c4680d0740c40760603c925030388135080082c02207912100e01602d240350b002c0f0520010351750510030104c82060581c001c0080e40080400510780140368400e03241000301e820790313000305521a60b0342510b41c202140200c035003401891500e8101038015100c03140c281442c040001d409491309280c0441220b4010024514007501c944408020390b00079907948050006003a000401a1103031146200c008240c4c0c00640300080c04081002100d202d908529064141020101c00155030340380c0240c03150018080e00650340709041d4 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 719102248 1250 719100998 719101007
    0xe06070b071b20030f0c13020d1b0908010b01030911040c1407050106080606090f010e060a0314030c010f020c03040e040611121603061a0702130c020a0b0603030a021507 74
    0x811000744440452000c00a038200f480c2c1c0d01448020048094130759680c2c0501c03640b0383e5028050380d4290b010a51309203068564009078000d220248100c900400c0004222940ca0120101c0c0c00c2e043d40001d11032442000407210030310545480b01e409103010720000070301d40c42d50110781a040c10503a10499940b08014003c6028805c00e18120190926013030320f41c0030505186008114a1143c4040e40c0142e1001480b00e10384038074994030480301d24048440d541d00700100c040045e40018811600000008404008180c40c030311000d50b00c580c0d070b000a583d1070020740c4d98a400d40c0e800054802c11140144140c00c294440071080d03d05540c41158503001c00d83d0b560030179001a100002c44034840d6003002500b131200f02e5203060454840c5d11002c9410001290039a2704804441e000c0c82407a80d81071a0301041100d1424010003011b00d140018994080c4101c1c040c0000d0031906011034500140c1e104420220400455104980d8001e0b8124003440c00d00003115806526400400d1049101500110010f492607009 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 719103498 1250 719102248 719102297
    0x91603150b0c06010b120708090705220f05040302101109060d0b1f050702010f0e03070b1e09030a02040902011106010b0301090e06040f0809040f0f0204060e06070b07 73
    0x2000c01082416030300c15012507107a001800d10740140c00f4220000c5000d00e914021204803003c0490700b09805d80d200345080700d410202402c00035250040300000140c507645e201c50010703049202c000710080e5410001070700048888180c40302c95464100300800c008a600400e00f209404010390340031418070040d01030381c0124400d501c0855486540072407101d6031701c0e040d58440080000183e8422101018030380200035006043d11003000000d404210340001548101c0d0070360151840c4d41003c644180900e400a420401e00350440701c82080003290b940b002d10500c003900454800d82811071441c003400000482d1700c40c0300203000a030107542c0324070304a011a4400c0807540c00704401d681c107440b29075849441004080d4800c1c0308034002c0c1424150403030303c906808602580110b6008081401610705603488040d40d0b0804011954819900d20301038150180764051114071ba00039050041ea51424000c0103852049030328841c600440061001c08005500d07500b80541001a03802d007a1401d07406202c84a020026 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 719104748 1250 719103498 719103521
    0x711010501090905060108070e150f060c0f0c0a080618030906210c180409031107030b040c0602010504080412050c130507090b090303041a0c0118030201050c09091603 73
    0x18103000020030750007550000c003030300c3d100d81c060350620303665070041d0b90340c0350307018001e200c14603401c0070100d10a400f148008107042c520181940080d114018000b51480d04011480355080c0c2014000056800040c00071201040b0b00f160030990281c24080110b40da003500402c0406540d824888889030010100300f82e5001c84001004590790b041c4a078200600310940031454083d81507228085034150040606030780e41140c0c2e240700a00c1c0c2c854200108805046110015410300c5110502e1490300030080c0b01480c040e501500e00580d0a08192501d910031003651b40c004021649800b042c04000740254007210115801d051020340c41e9840782c00d095040040010f1040c0c1e1048980014045031486600118496101512207141d9030f0342e03039486460310b48103000c0c92070380c150004c000a001550401841c01015040341c1029030600320903102040c21104400850701040102c00c020038201503090246a92225090350280d0401040c0300100b0707041d4401418103280203020030a500d80c910320990150401d00c5 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 719105998 1250 719104748 719104751
    0xc0714011503032003160602030402130e0114060f060405011409060a08010503010e010c020c131805030301031b080607050304030216060810050909120913020c0d1b020906010503071101 81
    0x150b40e403401030320f80039022104200825050701d090101070004000c2e1080d0100c00301d40601c88240341d5442e40029480140100c0c0c3c8540c444941050013145440f034004c1c0120b404000080c01c04a0900000c0c400d840113201c0c9100b14000c4030340d011030f91240310580c0c003101c500b030918000b468a0000b1f0b40032280100001150001340103d19600325640c0003040b5412110160000c10403410160760050a8840b5400c00c00050303404050341140d1420110000111502e08480005074509001d00da001c05076020041a0303060707030001c401031051282c0c2204100d031443c0508072816039030349000c041d6500d580004014005000002c8002800d00d8024091800d0031603204041e4600d403501c440028110520540d04c6040c144c03820800422182050381c401030290807140000d00031507040340c0071982140c2c8949100c68000d4400c0340b070903000f45101c0c0060081043c4a102030140314001160007070104941c007001e0000c81341041074010243c0c856100c26a0064803c0c030b0250350b2590742000075120842c00307010302c07031031507 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 719107248 1250 719105998 719106041
    0x21094608040b1c06081603150209061306030621120c05060403110607020f03090402160503161a160806010315060806040e0d021b031002070605060405010e0c071401 72
    0x150948000f0701e440030241e44080004580307070184290394400102c0d40f1440304c00c1203141400802e00ca182054070381c0710803440140c03601d503034600424525044059801c4104000d8641448907a4050040c02e000d85240e1001606013110340501000603450600050500300301d400d208110948150503a0b1541d9400c442226450f08191600038a00d4050140302c5095020300d2020039886031000c50a1800741910350000c6052008a4007000020340c070401031205000c0b4001c0740c06000500500141503148103002d025603d02116081040e2051075000705583e165078185c1c10010148000c182d03802600703d40b07280c42c01440c0d4403280160004c1c042c14200750090f1b020361000003606540185460312600050b00d0038045a03140a10066607860302195480c09600004280c2c00c0c005038407404c1031201c09004007100ca0075054524644100d07403203d103040d1030454484082050504180c0a014010040345660780d0552520716030701042400350040c024001002c01d020010442c2c001d41245640244100a18411 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 719108498 1250 719107248 719107267
    0x607171b031c020f1b160315050c0f0d0f0621020102011560020708030a110c0901080a030f021605040221094608040b 52
    0xd03a08116001e142c0304089601e4244600c8150090302d194048408405041640f0748406122848104d5010102d5100d0744040c003890720001e03400b10f40118003801c0c0036080d004407009050196039001b00324103a101e40030850340ea200c1a510046410f001006000010414000001b1002425042e42f10b03002010410320240701103041096881400c5200340c00812440340725170725079141040a403049911136294440300781c800b140783e5440b500c0152000d100310003406d00d185002d00d40459124159100380c0382c00c0e102e80f0481c01207003141c2d0f03608141d66000501c0094900b03801c03240d580c8284c105450030815180c103114a035400402c480058000c00900d80c10706580c44140d41540c4030903400d42540020407a4007402d984034000300d90040c0001c44d00c1c442400c401e0030078003840040d42c000b080c0f000401811800181d81701c034806205501500000000d85031a81003100c00c0040048100700c0100343e29880062500031a07491440d00c03245038488140e1070b0010711641001d10050040e0350000040641c0001c40040 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 719109748 1250 719108498 719108503
    0xb0105070510060603200f0a12060f03020f0108090d0f09031401020304110a06080a050c0d0c0e0108010807060801090b0415140a060e030a200312040f0e04020607171b 73
    0x90b98001e6508001c2a0419006c90f40004a11302c102ca108840030859030180c0c40da0382c1c2c001d224000007428190346000d00001d25108580a80c4e1080001201c040010f10071454000010000400c0034601929a070400c1040c003074950f800e0101c48804d000030401c8100c90140284c0843d8011900207803004c80c4099849a4a4040d50046804a8000520346402000761038500010416686599503010295582400740e9005020103013150641031411b11800000c41c020b405030412480250740c1c0e0341000405680007409000c010313007010701290080f02040c00599400341d206411210074407400316000644001140007850000b8040441c0200b2107400304145a1244e2144520fa509603800d55440e07640b00f0f41143c400800141c00340e4180c100c1c0384410f0105031402c803016000034402c4452215076050a002915084200a603030802e18800f0500700802c45080090740000c1c0310740c000c6260149840d0340003400601c200c0d1002001440121b0720010864100d0007075500c46810802502407004060301c00c0e03075 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 719110998 1250 719109748 719109761
    0x5061512030a1d041b03050c0712030902040c050301050312031806180c040615121409010b011101090b070809030408190b070e011e0e0d1109090c0d03030b0105070510 73
    0x502c00194030310055090519200b0040c5c5c14012054440e0000c0900b10118094000030303020040b0102305000032000f10b5640c08000001c000e1075200044d030560030b44188030640340015407407000c0c0101271004016a07140804c10185031001c01014594a41e280d00705082d441071a50000b02d2280f1904080007028140403800c01800404201202c1d030240b521130400082e1041ca0107440103006200e82c080c10700a02942481c640311031010008180100005640b030310b0300b801148c007211640e446805440b402d50300f1000c04024008920024020703105503032a170403075890029041e030040100c414001041c100b818400d035405800090b05862081085010343c45843d450b000055072000406004141058003407080308454001c103031240601c0e42d0384109203242c0700050300008001d010000380f581c000755035507122400c600c034401c0c0401c441c90642c2400340813080070010401201d41d40241000c1d0300301d54503400142105a81894080307907032108840101c81c2401200b000610b01d1194401c1d442442101d0f82220 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 719112248 1250 719110998 719111027
    0x3020d0f0221180c06030421020c0a120b040f050a17090108090d091a0702130905010b0d031e14072001032702061e180d05061512030a 59
    0x50290f884014294102d41c08140c2d4a0384198045a01c0301c0d15401e000000d0759126004184078101192660880b418410410b86400010782264040e4825854046044009001580708480c2038031850303621103808032070181000d40240d12135204101005820080354041c40d0b40509031400d00d40c40056125041e07000781500038003041000000540449000440d40214004e83e80c82c10034442c0790003252440b0702103030300a00942c0f5804001900c0541c549a1030740814030b03500940000c0704a62428802d003100c8071200c1030351280429440d0140420340c0300740740100d2a83c4141c0040100441e185069a20b40800c1c0e6882030f5480e40403d241d010f0098030f80700380070000300e5003020794090440e030001101200c0b0200a0006100360341401c17600c0301d141d0905440ca02610240820f840d2500020841c0308074050121030b080740d40c800250300c040001b101c102d0045054015145003106403c0c075500c2588494000309008801807a2010807001c0d42d64403480a21f21030600c4081e6690b405081030300409050403580c90 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 719113498 1250 719112248 719112307
    0x10050a1401020127020f120f0a17070201230d09080306010f03181b05040603211706060c0106031704090624050a09080709290f0103020d0f02 62
    0x35407000e600c100a1114400e0800c0c0e4010050340250b00f01b1500610030000d080c0c201d002032921200a00703082048207001200c420040a0741901e03460f210502400140c803446120381c040c402100140d03007019590481c0c4641089031000306200b0480702c0d019000364180c1c0c4081506007400902401400da00441c055907081c1d8030382c00e421030040c6007074064031201c2070141d400844000040c40420441000c003022060100e4008840d290b640000605a80a44d0002e80e801040160414602d000840810340e46504509203d65520b60b0489183d0707011070000c0c0903134064400002d00040c9400700f9406140659808648440c0c01d04403c0410181a0414050103421a14001001c071702040e56412111070307080c020000061000e501d8504441c02c1e00424144014851400c2010903d46000c0c05035002030201b4100000c1e0040c4200e640707109015803035401f140d0ba50000c4420aa00c5d803070b41e00c8034031110002824090703a60000c03220f00ca401401c800c05441810f0b403001c22441c0f4108450023039648020140810b = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 719114748 1250 719113498 719113511
    0xc03121003030318050303060d14120c1501050603071b060c050c070f0e060f0109031520030603100b01140d0b18070203090108040213020a091505040f0e10050a14010201 74
    0x4425000b007030040174009038003e000060017890504034224909101300814800b4234060b945440c070346901545003101c10343e0007042c140012a01040407031160410080166407652501000c15100d103c00b42c80c500c100448203441e0000140d980d28041040c50f0b01101c10001000922401000341d000000040c0c440e000f40c09c0b000410052800c3c2c40c0040d1503244200c0755041e100c00d400c0040782498280c03070310f0510080140c0000440c016074166061406c0c185408680c03001143c0ba000124414201e21084005042c000d01c509510006441c04846626010018009141c840103840000304100600c0c5201390000b004116150a81c0000090780019901070f803090441000c043c0c2c1c1131000322840001a41306001110f2950b118460182c1c1050001e00381070003903a09215010141da0001920b800030803082441001141c0c0b01e42c0c09080b03804800d00c0d105042078240701d1403c182030761510a1680003100310020860001280d16544000c040040461412580d00e548a81c9d610384031104a0380954680034 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 719115998 1250 719114748 719114771
    0x20307081b040504050106051c0507050a0e0f0712110c0f03071703061f03021e0f070818060a210203010b0301050d050c1e0a0b0c120c031210030303 65
    0xd02011080696000107440c210748406000080c41c000307100752125034941c00002019155000c1ca504a0099202c0607411040503040840c60304010f648528022030600408009820350444042d81000074910407141d5034a8100c01111554514030442003901c0c60085117095503403032000280511a404029144200d1056152646901070948041c15160211b103943c4030b01a001001540d1110009040221a480c1540f41c01c00e4000c509000302c010a5000840809880842056404084131051503a18060080034915114003402100500030040070030307410f10180034500410000320020389500e4071031640c050001d020302004210900804604d64000312540518001c40741610b01c44031106140d6483d040c00c1c000301c0050000e058500e03003d008000c040a42d5101c00612200b000002c55914481c2c0c04002c110700702c289a840440d803a03008000318606198041070700c0f00907801c2503080725103464040f00c0305411407142c0708c414000d01c0718010422410302d5400f419030081ea402594100641c076006c0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 719117248 1250 719115998 719116003
    0xf1104050405011e0302120f0106060c050c540709090209010f0509041e0204080d08160f0203070506010602010c1427061318050915010308211302030708 67
    0x2601140b03843c60702032820b00c094144203512981240041d0126034804442344c40640c00c41380e0613003002d400601c4101844062010801c9a1116401c08071041c1c021200d071102e44003801e03540001070f9030641070302d5200021030080900d51032590300032242c01c451215500e1400e440014500b12901d20126182a10100e41f078000c61081d580c2461041e100d003050903140c00c030b081d9066046214143d6004c1d4861801400038844218209a580d12100c005030307d580c2421489810310941030012020454143c080120401081e94807401650540c241075000c400b5609080b420342c8150540581a807090000004200da4158030101d43c04149550301114110034245d0340c0c016110341040401c010003a040c64401070240c40e000d080e0360700c3c001002c161400304210551029064603a00049001000185c1800802d203a805015070040140c4090144402c6c2c44c041100d01a03011300014005d400c0204441503039181c18007203003261400e5601043c00500c2c14a00d4038140950402080b4024000c001c000122401c00 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 719118498 1250 719117248 719117279
    0x3042c0103170f090d11040501081b100201110307020304031b0302030a030305090c04290d02060d0b042a0906020f030f0f09190f0b1e03040201030f110405040501 71
    0x854000c040c41c01c81484642e5107900801e1040b00607800800051001e80d440d05540c14103d8814030181001240c04030800c000c841e0140d1025202e40c01180f552030207210b4075280024440c07001c031030008440139000f4007280140144a070507107250b48000240103940d03400002400c2100d224a0712401220130f850b06607003c108491000a4040c2d1100000c0030009000350031165200c8030400072034403450b00c0d200000301a9000080d20030140580030a2411b00400703078500400a43c9000e840160041104c1d90125125100d0002034101c45591808100d00c03c4d6241c2d08070014a04603841c03100030940c284602c41c204264007110200108100f040d00192042c004a404040860540040d40c14800c001084c1102540040ca18400d8550704105020031039a80720410010011014036a01455040c6401a40082c01d19000104900303003e00c4400410191150300150701d032811142c154a03911184010780141110540c0b0640040c2804051840302e001d244c0500129001140c0c1481241d13a5210400c409801 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 719119748 1250 719118498 719118503
    0x180501121205160507090207030801050406060e150403150225050303150d021512130b01060e120106060305070f0804020306010b03070c1202060403030b03010e0705090a0207020303042c0103 83
    0xa0005803101c85038041c0303000d0007070941e280c0c2031014101a6030341e8440c01e286041e0802014568003286050078103500c0030816000d090144c070100207440c00d040b0060801e00c0440e000c1c9116580d03001c01e2120460320003041d07400450b8024805a40e940c6201815000794004040120081b80e1400c4005160b0021400d07040307034030350800c01a61844c0c6420b4032966500f40c00000e140c2c2c11641c2d0040b8040144c4030809800d04082c110300741c0580b244607094003040d01c8007019001c1c0c034221221403561004201c18006a40c112409418401102c01044000c5216034102c540110459480e00c0000110705400d0f400c8103219801031760307030303a01e88813007140055035208401e840c069090b5122000521000c0ba981e8000c40d0000400d00f00640250069994801d8580c555110100140c111000740001c16405018011070440c044000740480072110300c5042e03440b010b501c502803185651a01181203000f0365070440b182144c0160640303075115268903030309041c10400b40440000c0700c2e00d032078142d003103820740119103060300d9 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 719120998 1250 719119748 719119763
    0x81b1b01080609042006091306090c02030406140a11011d011113030602030405030c101509020304030e222d050408040b0f04170c030d030522081318050112 68
    0x1050354043c403c140081c21038a40e0046020481078a00307a2344c95280d03806010002c000492024200110b59058462000c001c03015584144010700100390420442140c0690021071280c46400103541215407e09515101120b9441d10300324503e82401422541c41ca54500802400b504a55403220300b428450640855600c010701c140c24000240700b44c000316003241c000c400300d9040c0107202a4441c206814215050b902c00c0c1d82e05d0072801010603543c910001080044000c5080d49000c0d01c003d0464a58640c8080c803031000d01002180900601d404451035000f84442042180100301642c401c030381e0182003240d04820464040b00200285016007442240d020b04800d08091600c60b074000c154000a580b11207540090002003000b041c0ca8a01e01c01e01031825009015208202080c941060748160f017050405041101708900d240c40c100f643c040d014010b0b0600c8030008140e0034150b540b401800e14803400b1002d607140002d940350040c51403000b110b1880004001c1a40e903400c10b03003110000b50780c0042224 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 719122248 1250 719120998 719121023
    0x1020c01060e2205010f050c0301290909070903290603010b0616030c15020403031701150c080c0d02031b16030605190c030e07050a0e04081b1b0108060904 68
    0x14143c001004039564030030000400d07000300301c80b92882030f01c1007103480c007000038008001040200150b00c181d01d0046081516943d8080140e4410700309807003219191800360000001061100b44a0311078240110b401c1000225454040c6024a405102c00c003140240c0307000d4140490f2080c5810301c03840c800001c000706083d251050040d0107020050103030806809200c89001240c01180c00207a0075185461000300c01a0394030700b1841c3c050700d81601d1078418900091482c0041c00007140c2807400307601c010751900f4451150020f0340740c012101d220b03c0d095590540201e11405050710340020103015600c010540b40301007030801e001e00c182d444048516049920380f412408001250f010b6200903048502c604031400220754902c6008107039045030300000700082d40d5009180c05800148a00c4024007001c5441d20111881c03c000d04a00b2040688060300044000801d104e05100810707241c00d000d280d440030742c1c1ca6207007c00034070008a500c1c100c182d40840d05100c0000c404d4076080b140144030b41da0140c0e080012 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 719123498 1250 719122248 719122291
    0x10b090f04060b031009030203070312020c0709050903070516030c08150a1a1008060910030201080402040213050d240b100f1416020a090c08130201090e010801020c01060e 75
    0x240403d140616058096180000c07906281402459500d500a0700216516009480c00030982941d125410b54180d1050105108101011400b50100e0304003040101d0603881c3d02c2d10040c00c42c46030410040c03c1d4855440b6041c21490040704040172a80030765040d640941d514042151116075514242c000d01c1e22030800181009010f40c011600361b150700b0700181e0b48004942c086210b0450341c840107804290b40800304420742c50300f0941160300170180c0b100d4426091940d80040c03c0b41e00c025100a00c81d580114581c0c0b8442036644441e0020400141040100a1181410042500244e28000e00000c07000301a84104032140035000752040b0291026955071512181180d54092070b4444808200000600c080304003006406000045910011030307a1a800d14810041140b40a0740024411810900c080c0703a101c0e0440f002c07075400290320080d80403404075440101c600da5030ba900482110080180082212001540580035400601c0d000308005515030000c1c03000010b044403034441030b04c0c4205440b0300 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 719124748 1250 719123498 719123501
    0x7080a05070c0803040605060f030c010909110903120406030f0c0f20060a0606031802030712060f090308042907050c070b070f020a06050a141b0109050f010b090f0406 73
    0x81c000070a01c1c010015104070340d03c49030b555005076030641d00281c9400921040745040784001d18038100032001041d23402c52100010707041c10a54881c24280c66039131086285c16401e1203040b00e0000d500101640d0b68200d00da40d1359422a0081c0c0039080000f0b02e40420f100440c3c41c00e1240950071a400d0320b075030441c00c0c0c0d80300c421250020104080c0c120303518078480c0442c1001040003454040c2900036800b064003401d000002301215001c5030030001d541c214407554809a01d010506000707540c280c01c00c58200d4009814600c000c5e210219482c0715092400e042001495407141c41c0a00862048020800e010f0800d08030300c035602442540c030a144d01c0014049400b1174080c40080000f4032140302500c074680d54500401c0d540342c010010680c5ca520380c3c207403400e045181812242d009032055083c20717810072008880003000c034080741441607030798070001911003282c03180c8512000d1b0040c3c25000a02014800b4944035440790f410940c40c4409608080b508500b900d800d41c1d0151142c0d082450303c4100d0b03911038a5407070 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 719125998 1250 719124748 719124751
    0xe030a0c0c09020f0969101e1706030a0203060a0e0a0506160311040e0a0b150d090b07030209280e0709060207050609061c0213081609020307080a05 65
    0x581514003142110f0000d80a510320b0419004443d00050081d62039204101401c3c04803000c01400e1307001c1c01e03180b904a01e242240c0800f55009580320407540f247c03c039096030101440322011921150360500e01d001141c0c0210129407210f106101213400c2d48034070050654902116000952642001001880202490340a0400d0316100011907003000c0160f1140b81c1402c2c81a501c0c0505941004540301c00f0940502601c40000101c0180340d02c0c0030300c1c0800503000030102815034000d60361a00d4481d02155500f0405100b0381c0c00200002d0741e00c010380140f000050445941c06c50b074500c080d0001400e694024800d139003003820040c01003050036250480e5031710182c0c5030896405d90324200d800701248011014025510a4800f61521341a090a00c0806461719006520241c4203150404c04400f06460b10701c00e40b002c4400c4a55003402845442030b401c40a8080c0307081c40d12108c0c5030003a0000b4210030024072080c07241c13813900940d0080d54840c10300400340c1c4400c80d0b41c040456045004212038081e55071041d03 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 719127248 1250 719125998 719126029
    0x311090c0d0c030e0c01021504030c0203150108010504030905060f070320070e041103121914031e13021f09030204050a05180f1f0e030a0c0c09020f09 66
    0x103514200c030700c4000d4022208410444800240d6500d807081d000b4000300140d4a20130340900040c0688032800350304141080000f00020204481c8141d582c086403010460545061600c5420711340c01d68480d5601402070100b2101500000d80700203001903541020401c403083c0e820103448031480d2402c1500c1c00d5400c4500d0009006003080713030100d1144041824407100d000350085101c045254145070400c60102d14030221102c0c401d400080300480001250400c50301c0c154441e064080e42e4480c06242651811a41c42c0c0721301980000008100e0303201000c140300a000c1c0841d0003c0d0405481c4d00900d0801e5290302680250408840000e000c00d4800f410001c11071f800303491410011003038580e4041815107905441002200b501c4000707000d090740c0104180c090400b071106c010030800d9150940a0b0f80c0755203010b6821400500c2c59405240001d003900070031080c2c81010b0031280e8440e6840710040010200e11000c0c1e460180da100d02007200180781c001c03126905c000c7c000940c2448001004c000d002030004518 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 719128498 1250 719127248 719127271
    0x307302d081605160f050a170a060c1709210f040506070c0b0d050f01060309020f01030509010605180103060606093b04150612030801120215270109031109 68
    0x582a000c81c091180000d0100c5c1007041c605540342000344260807600342c00c2034808442c45401d049000390001610441240c1242d00464134018000382555018100140542c00c40009001c10980b1a800500303607503c00c141007008180c0907060070029120b401140300724525440708000410091a050018100e040e020344010700503585d030348030070010541c0074070780b481c60841d203c40030420111032141402d40140601e0a06000c1400c85074000340302c8000829596041c55920004202e003607509611080207001c002c1c04c40d142c1410142054941c082e42444102e0b2014144040498620311551130b20049504008842e2910902c40c51442240b014103650ba9107024450f2018141c1d00d03122001450107940036401d0b007860707000c103042000183c62084e00440c50242c1b91214080000307030b0003005141100d5040f81a4210300b050342c40081e00c004c409200b000b51410001c10b00d4500206a00c2d0848505901b0b44048030780341d1400b900540d400c032000d10016007a032440496005490070710f001090750002c4040d80c0c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 719129748 1250 719128498 719128513
    0xa0b13020103060b0d1a0904020913110a0e0916050616030e060307180504060b1c11030f0717010b0d0e0c0301020c030406090e060307302d081605 64
    0xe581400c1d004900e0303107903179240c54288080c00d0f03442d0350b00102520007080d038a18000c0d2400e40c0220300c071201c0c050401c8aa816203055101d06100710034120100b4004014900326445a540704107000c0389400369000390305070145414404070f22148034031800c01c0792405410710341015103800000342c110010360b10982c28440070f0361403000e00703548010055108045544801e5a41c4507441000c6c0c0c0e09101c0354103c5400b581c45d15006004102c83c0405440c07841032070409a1a150703040d0300115018000d05030b04500022004412301c0440d200045002c3d1042c01a0703070b80c60303403803548401204840c0310080c420003408220400600104d58040d0b080308550080c07800840303000384030b1000442d0883c1c0c01000320584039003011900341b0816a000c85401d0040c440c600c14101281408400217845036603510a10841191246000c2c4001403004858059040d00d03035120840603000341880b50f4048003c60804c1c0030040355110044151101000003d101c3e81c00030b204906003240a080320400406002065455104150 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 719130998 1250 719129748 719129759
    0xb0901050a030b04063b010e071707080a030e030607030917090d02090a0f1a030c0103020307090b1201051008070207170c0a091407052b0209030d02010506010807020a0b1302010306 79
    0x2c007108264490721a0940c045c0f11111b000300c00d603042400710301c110303414002d4414038401c2c00a452001c0d110a010b06842103156041401d10f0200d00c1d500455050282400c2c04003810703004802141e07860001d40aa0380a070351400811021500084c07402001002091081150340301858042c0400441c0601080483c001a4001030144801101c1404000307403201980b070a400c001d030107000c200b25254141c80c4140240800026242e000c0030070386c681019408800140700391310402040001307202860000f5503c0e05080c81c0845009002d00650b801810035229160754076100c0c00b0005e1142503298058618981080e01c00c440b800c00078082c0405620030a490f412003560360705190402400d9406001031040e50101c034a14000340024466410320406004001e0301111503c801c2c00384045861000e4100400b070b98545000f03003e8541c00d01d425210b0501900702c0726405502c050b00400003600e13501c0560344e4180080380d50700e02c5001d000f0412581342011581301100080036116540c07050601007909502c80 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 719132248 1250 719130998 719131031
    0x1e0c0102070f140a081e040b130e1e0f04030e1c0203010507021507081f0e062803031202090904120f0203030103030e0d051203010f090b0901050a030b0406 68
    0x7603002d6911026507038440b0104403c04485500559142e0003418042c011900c68072154020b22800c0e066007840b0003641c1101409041c21280038001c170355100d50312185048000a400b216034040c006104040d80c004c2501c0603c0020b0486c0036010303c0682d03580316502e5480c0038801c0d5038050300840a005400d086007030207903103010000f0586c4020340640b40e10341105004042c03e4680260441c010f5400c028005040f858040401540c40300d801c0c10248099260207109900d030502c48028104411030200c00404e031521040c200c40e00032902102d000c030605049c1c85545d12415100100031400c041c0b05542040041d004000442902805000041c01c00d24a840800c2d0030000031a022110b158010500200c4c2e15004106000c65050074401035007190304594000e0040c0389441c01c614455004500306104100c410007020240c640c002e8101c948a50b07581152141c964104d001d006601410104801110300301403c01a0480341d00404049a45155071580c1d071804101a100390340003920f6061405194244 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 719133498 1250 719132248 719132257
    0x3010603020912100f0f0b0105030c030403110303131a060a050d0303020d060b1e0f12150409081803031c09080706020403081e07171c0e01050109201e0c0102 69
    0xca004c04070b45540d244290004484074000d801140d1481c1421810959910070181c036441103804c0d0f2016034070b480300d08007992030110300240e019040c4000001c0001985884080d055003612548080f99424449041110520300484096410034440042084246084050088c12a0190800503c0d08084030381400a45515400c112010b03040042d20301c0301451100305181009104448490400200214030061032050545e449215841640824003c0716040d4026040c81b000500c1044038144074505800c06030004000a00300008202c0c100d03146080120849180c1810303401030041c4010440101c030010510f0850a40d9500c0f000c0c4969400210325100a1000d94042d401d52515110319081d041c3c20840b031703c0710202d440141802a800002d00d9a2100620b44441421041d00c4203100d09a1402900303605021454950030900480340050066100328161801c0320418800e040854101144465409561200d40300f0100941d8030703e6101400c078400c0f80d141352088586090031000c0f445003079810 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 719134748 1250 719133498 719133523
    0x60429010f0501020c03070f12080d1a040507020d0507080a091203021c09080a0308150a03030e0f060403031706010309140105060f1c02040b061207020a0501060e0c03010603020912 79
    0xc1c071480a208540e01049050185a000c500804455041242d58038131441036204c0c011820703080d041c13071004002c00c0e0003c7c0c0b03107101181f06080021007003001d103031902d050500a206000c0e0745010080703052a072002c5001107031000a51140c0c3e00d02580b55030341d00c109074444d83c0c00e0b004200103d0400b00c6d0501d0020388002c6a2406540141150000007400b20100200da2214400340140003c08000c003a0010a0b0300d0302864250a01100542d200045403520f00c3d016001180d103d403d803100401050f8020310050090b00d0103030313009411034256030240401442a404054007160b2108058160700041c504015801801031401260f104c0c00340d80ea40c0c89113100007205240d41e075124410030446050981c4152000c080c1107c603c007080195401a9070203004050019000b00e443c4c00f5007003000d864030030803070380d00c6144511901d2003880c14140094807445100d404a8031542441000a000e0354803d080501034440070201030b107075900e4508150000c1d030120000681000180141e02001c01c03003030003403801c402c0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 719135998 1250 719134748 719134769
    0x6160f080406020610080c0109120201020a151401380c01060308180a06050f1b03030403020109121701050616150b030120070f02061b24060306042901 66
    0x8100011817002c07941c075080171000d80d02920024046130f0348029a94116810962810401485800100d040201080014041800501c00041c1c0540244d0080101910b600c00490050b40c88010b640719203410140714030800c400e05502d40504101e0008440880901101024078140c00c0303541e42c0342034034250340c0b0603100c0347d8004c501040100d019017400030402004841d02d80505084c8007002d000c0e4000c481082001500200d4500a030320040031141d105c420106044a0701c03850507280c002d0284c588243c2c1207070143c0b9409a505169806150420303000e01482281a80580c201028003000c0d410107486990320780170f09043c010100c1e400d00d80701c41c096203560002241e20b40e40030062500b51000308088060402c981d0624480824250007500c60b001e0f403100c4494101c0300640006902d0f0702039440c20f02141207044101020100d0001044801e094081c1c0018044003c45502c0d0312044800f190066096005000000c0008040c640c440c440b42c54218100100d0032015510b001180c82c00341c00000000 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 719137248 1250 719135998 719136001
    0x7050604091509090305270102070b03070207030501111e1e03040609060906051803040f05040b0a081203060f040c02060f070927050a0c05160501140f060a080c06160f0804060206 78
    0x318001c5881e004182c041c240100d003520400001b036038ac94191058003650344010000c80d01d0316100303000000080d50000020b0041c13040098142c807280e0700283d08002c0461f2104400b08080107040d060b1359040c04990894800782d015404a0aa82e0740700070406c461055940ca039510000300300e841006000340c06a1000222031401c1208026150f10784c03900c0000d40d0780144070402040d6200ca203800e003078403010355020a0219414010840d0404590081241030041d440d807a105082d4400107180304030021101003c03081007400c14002128071220300c540050700004005240d2610042c41c0c40c3d0021450300c0d18109007962680d155034091486024040c420f07109800c030303100c2600e043c000c0c41d0300419004000c00403c80190b03005040740c441d100c146140d0585590815051113401e620031800340494030b19000151500c0701c4d030302803102d204458962181c0c005203000700317003030a0004105158441c040c101506d410201e180301d00c1640c5080c0b404130707400a9120b0480000944420103807004160a40040125 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 719138498 1250 719137248 719137267
    0x3010b040e01091a090d0c111f1803080909040318080f160f0302010809070f17010c0c0b0a15120308071b1101050d0f0e1e07050604091509090305 64
    0xf03e10b8091220135041601003440035244020402d40c0145c9101e040c206021082c500d403c0d03011034051240700c0d90000000341120b12250222a0100542041d5a00c280b0b69422101c02551a05001d00015005100038008454039080664130700b41c200e40070781828410341c950b0707100808540d91070340c11407007507a00200303e411366100081040403005e2110300230b802c0c41c20381401c940c005088001d02c00a410040c04e580451403c600030b1100d1400344c250103000094a50700c40c208524804510b22081c0c84640ca03050091044030f00ca84541c00710581d021003507010076242c9289010150044021040031000c1d4039400103400010baa0f000001640b1a4968005914060401900d02c0d501034000c10140d40751032401c100084c0c05006181c510010074200241c46a12080d8140001c02d400c0605540a034030f0040602e00d01100024180602c0e82041c0101c10380120a41500e0384580c2e4522805030091004e10050211202c990810002c0824103101c100b2041d66034046003003a01e41d80b0310207074040754000408040 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 719139748 1250 719138498 719138513
    0x72007050406060519030b010507120f09050301020a0905150d02030907050a0e01030c03060216051914010b0108010311010e0604120204180f12090807060302121305070608040203010b040e0109 84
    0xd110f1130038094140002070480c00c1c2081c2e100d18805c401c0642d120444000303030f801101600c0c24280c125180c016081024900504a0f41d02c0100c601e000ca050140009404d1805008072410740b0f03580e40d581c28440e8a4982485919481b401840790040824000c40200208904c091071096019100034280300d4506024000c05904a800c44849604248014800b084280003550112640702c07000590f40e4030860f02181d404c401154004085000d8001e040c84901c00c030728000190280143e82580310322a00c803d170300f4201d868100030766010071304010041000c5a103091142c035500b10103040000040c0c44090000d80e0390b40c0160011004801260800d000794141813003406550010f800704560164200d460f41c4000e9040c007030004011184560f800b9001034443e0000400404c0c0c14421100303140d171070710000380294104c0a402c101005c1c000001600803e120035514001325000780180507110f040c0801101d5000c030044c0207a030950340b01c180071358458540e0304c24000100c10f1a800090105a545003070031 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 719140998 1250 719139748 719139761
    0x121c0212070308010e073b0a061e0503070f0c0c080102040b0a03180b04080315220e2e110a0309030201180b1f1205250b070b0720070504 60
    0x10104804000743c20000c0e10950811400b822024903180c81c00120400b864a03d0f0301d00710101500f08c0208000003850927080b80609038140506000306821034900c2a084815000c2112070a00207800c2d80d50f0807503078a01036001308881c58055100c0d82041600d419020b07003664041d03444000512000070b5880300f029030600c03d0240d080e18400348210100b64580300c103800d24401800140102e100080850705c15010001c641ea444100545900e0f440f080c1c48401500c1203007081d441802942c1010084a074000000c122900c64160b0b090178503c19481258000300c0e01103034142c21080007a0307a01007140c12038040c10081c010440c03842d0b030081503552142c0790090039103401264840401400151080003c1c03c00750f1010781c0841d58405440015111101c44042042203a002e224104400c2c1202004d10002180390300d04030410740000002070060111170f030110140c6124104203a0401e000c11030001d4182403005821094034a45000b000703010300d02d603400481043e441c1c0301c40b5a03c501810095400d09000343da = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 719142248 1250 719140998 719141011
    0x60f060909062301020c0d08180d051b01120905240601140d0f02070b1b030103030503040206090117090f0c1005071b030b09030a02010b121c0212070308010e 69
    0x3844040e1400f00c0c80e0030305003240c2c000d007001c4071407480b0390001c541d00c00c101d03000d01110002c10019284125041c80c0340305034002180d40032441d503418a42052401d1120304e440f0074680c001c00030030320405070f4820402100000f003505070401c1080703494501f00c508140241002e0380c0c0654003802c54041c0205959041c002c444e0503e1503100707a448100006680c008101d035084001c0b2403040c2c2e550700030303080d503000040c0200d000540e152071012030302109004203158014811007841002c8075504150b65800b1181e40424031000b00000d0080000070010304208018040414041c10121b00d200d5040900182106044600c084268099641c0c024803420800084905c101c040d54085181103944000030810310580d24050641d140b00c40d81c0ca0003200f040101c2c0c100858202150b01c203107003024005c0c680c0f07179809a100c0034019030a001d401000c07072070184071100000f29504010142c02c000d035104800603000300719150040d03005080b203044121200b10014807409200b540d81c01915814015014604203000c4c041c0d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 719143498 1250 719142248 719142251
    0x50a05010518060109081207020a0602070506030c0f120a020d06060e1311090303160b060105090a030f0c0308031009141b13080304061e0c080901110a06060f060909 72
    0x10040c030380720907250320505102d0b011580c100e50740d040010b0311145842d602421640c818031112110305d001040241c48103620850340c400300d40d0b03517842c0203e95a0080e809140d61003007041021a4404e1007550040480c4541e40440a051a05000643c15580b4040724000c10180c1c00061a000f1100755100d202e015260504200340411041400305041c07000d0401074070f105569488078420280e0300300c42035851081c3e0080490380d0b650114a1002041c80c00c440e000c54240500c400801c07410f6010380240c594014016040c0320760300d8950745901c02e40780b44402c000c3d5441c00e0801d001102040c2d48034025841241d145888400300762a0081904c2165511455022000d901a047c0a072a00d450184600d84003402041507850702035007a240030b030070b100c00da00030a500e00c0000b80004015800205c503214006254221002010104070705580c50002c0480062500f101007260161560252090080c032002650494800910f15980c0307400b200d007260402e014100f0500c10810034298000c00c808050144040c0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 719144748 1250 719143498 719143501
    0x504032a0c030309090b032d150711070807060206070c1406010905090c2b020315250206090c01050307031e09060e0d02060105040b1302121902040b0d0507110d0210050a05 75
    0x850f00c03100d0a001410910305000310306840341d1080269890a09d039911341d071701e2141422400030b07110800c1104807024a004a40000404502c0429104103da24680103006995a0000100c8130038031012003c465507000c180707005010610030481a8043c0110240016250400010091510081410b060700ca042e414070038041d44060142c1401c20b6150140c20f101c8070710602c0c40001d04005000c40c80d001000c56000030041201204407080003d01c2c0019103400c42e40c001918100d851f00d004481d005d0580c0d12100b50303d0101d5204800840d84032009180016000c402401031504002c5a15810741c0043d44992501e41031020f1881410440e030b80c84070003803115034111f107800384d10781c0720510a403485142d50b10b0500320144c94441400915400c5030404643d40c446c54248120100400d136400441c0700d02c0351800e4440c2113264800c9070140c070580c1d00030b03504290980c000c3c0c0340036103001410202040400000e8059540041003681d2022401c1d030045c5c0b0784110034a80310b03c01c4417002007071034142c5800d000 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 719145998 1250 719144748 719144773
    0x601080f120909090102041203081609080d2304060306080705030613080306010201021b0307030233060301180c03110103090f020607030c1e0b09010504032a0c030309090b03 76
    0x412140c442c901550500c103207507606002613009015940c0204403041d06200b400042560001d01c0f00d00c00e0300000c4041d60041900034003121030755240d0043c031919034014050015031a010320f004540702114200346654046851801100d16082a0705c0384000c80d448080510141c0b4042c07110070081e000a500420712450300b507614000000f00309901609170341c030000c0410220f034403c0d0112407603802c1401d10051403d141c44021941e1364801d05044d00180244440d044035204943c0c3c2c1d11118060011160b0700c140c0750540324520880e40a061103a042d9654007401e8070102134440c2c242c07840c0c1e0280110096039071841c2421031900b5040545a41014604814140042d0103000701e07960054041c0c03000d42d210822443e003039070840003042018100742d02002509400406450070005040e201da21030f4001c64a841040ba400e0314000c0d01e0007400316900d440c00d02c0219040901d9040c081c1c0006001c1c43d02c0c03a0755602c900300c043d0b902d070300140d001440c0050140012000c40c01040c418542c250020f012080510 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 719147248 1250 719145998 719146033
    0x140a05030f0d3e03070501050411090703090b070f02010902130c090b070c030305221811070b01030311032107030522030e13020c0102120c0a1b1703090601080f 70
    0xa00307004120300140f5021110000300107440c85540e00c40002c104a0800c0c0c14004034203145a54120b1003a0403d00c0000c1c2c0c50f900c640500814aa409050050340c1c1d211944c09584c803454440d03d44c411596102c100704c0243c0c1d6090fa40c21640d066841c4000354910284800030050b8180b9005026001810403240c00014088448002120b81510b8003603102c03c85c1212107001c51522240341018086c080c1c1004c1560784400614142080d00144100111140e1403051041e500880b1030180c0b46610b02c000400100e40601d182c0c20107101780105517490710721003203030321b110014085892031003000e41c40040142c03841e01842599005003410070b82d00840c076100540000f4884404800800308034000308012956240e456041000c03002e600c2c410754a40701d5101016000b504072510058095100b44041a0000440e908440c03010b1080e0303494640145a01c40c000b0043d02100c0341c2144d030301d50b80300446865241100e002e1405003800201500d00b652402402520b0411003d000d1100750b04042c0800c0078144e00c8 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 719148498 1250 719147248 719147327
    0x40b0406051b07060b010207050411040902130b0a0206040b13150b010923091f12050a0206121f080c010e0f10050a031b0504140a05030f0d 61
    0x20110200300d5035079030440c2864403802c5000380649030001041c1241040061740101c5076080c1c080e802c881801d43d80742d01b00400d03641400d9200c1c3d01004200418090040e107900100b11200d401c1c580300101641d1842c3d00c0c10154094541c03400140c00c10342c01c0c04100400d2840700d0b0b800085450351100000780c00c1c0c0b0703101c42c1100300e82c0300b0540c138903620005070f10f1a0740505d6041006040700ca086002209041405040c112000361080380b1a1079840000b4861290703a03032403001d10295214490034001e042841041c881443d008065400c0d11440c2080d170300503901c0c2c000034030028902c08c05075007044c10701315480181602e4001c0c1e03050307421103407040c148284000013a41200100c424a803614040200c007000c505040001c03a8466003020010038803c85240d0000c0040025420a95081145c038042d8081119000e030900c68010014804100c100104240b0508094000c10010407451000d65242c1c002032810002400310641c0b41c02c101680a111a0425610007124080800f541c0101e0b50380e0a041450004 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 719149748 1250 719148498 719148503
    0x9030901120c090329061906050a02030d02040929031b22020306030618070306020306011803030e030114041e050a05010f0b0406060f0905010305090312151206040b04 73
    0x1a41d07281c54002d0307449150b000c0b00031a08145160045543c40d240351144101d02c042e4032020302c040f44042178450810301513403240c5004110406020b02d00701042224a81d21035050b02c0c0440c4410700280810381030520041c002042070740c0c0001120740190012507000c03900c0e90410360006556010181290300c020400c209821000080641001d10390000210f07481240d41c49111400030001c040d44510000e036005501901e0218100c0e015541c801111001c81482c1d48986c048940000804100003035868000d0b5400c214141400c00c03281000c3d40710410803010076807065001906412103c60710342020f1207040d040c0da0400c00702105e14036040c2c03200040071802541c60700700c1c803449402e420140141031007034070f01c21584580240020150900000d001d00796003c8881d105a1a0403400078580d07010706003034a00e806568964000c01072030940150000d180003040580d4501080040c13a540c41c04400f001c1e482a540044e0500491190303509003ca8405882c0c0f00c40c0103981301c03800348000300c1c59119070a075000d903 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 719150998 1250 719149748 719149751
    0x50901090b270a0605070905091009020d0e1b01030b0402071e030203071b0302010e0d050d0c030203041a1812030316050d0c11010c02070b040b130506030414060903090112 75
    0x10500088030b00c50340300740e03801420a016940b01d0700c0400400740c00c035a0051305c0075a55641c0071510740007008a4200181c56100300e80e4002c071307020042051950043c20510015490004800704824020350510329051004000e50000d400300c45802e41e00341c4150015068181d80071800c00b4141e50700c02c8040100d002030040c280da02005588201442001250303032042c0e010b01205000c002d040c440380c2110100c1d0008901080034955040c07014100448992151038000c40107000045030000203580100381401c064046020400011407890040f00a24485415004226590382107161031015002010b400c05d80c450107503104112951840007007580d4200311180c082801c040916402070703d482c41032002a2848a007030151404102c0c1d08450319075020410603000f40441c03190341c02c040b42c4581d0240510340724003100b480103002c40703180000a0070055401e04203481c9440c2e1103500050080d041101c0480d90314100d21031500c0030b0380e001c2c06800d07000131000004608000000b40040c100ca801c00b03540000c0f0a = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 719152248 1250 719150998 719151031
    0x1090e030414130e0d022104140a0f06050912070305120a030e01050a051603090201080c070204091509051b010903030503130f120f020703080901200105011503050901090b 75
    0x2607681440b883e21501040604104420508420644801402c03201d00054020340ca4603240d00503881483e030301c0d0701c1d45113410107151500701400c2c101800d40780011590800c0401002003210701e425a40500a072140e03131070f00f944404140b03081024981c030350520b080ca103400c078110800c0062000642e01042c00b10001440b511114401006c42c014604403502600c07542c24042071000090700c5500c001d005881d15182d00143c0e403c41003054007522181e0000134000b500d030400050f1584124405801d00c5440103101140d01030b116103403030003059030504c4201410fa40c1c03451180704002c1c1c1002000c08000d40004280b004000e6280041c0601c03c20b031001605002c0004001500c11071500340c06c21002d5800315000d990b60b034080c2000b007141d608a06510000c85c112000e11294203000194001c00c682c2d2100565160070840c00044881020f10100d030010740c580c0101e4403640c070701e00b03000380c1d800307000d001210000700e84803034100034140da10250400644d40d14200b150404113055504c0713603920001c0200f031038151 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 719153498 1250 719152248 719152289
    0x14012606010c05300910030209010c0510060509070c150902011202070b0f0a02071e060e120306031614010f050c011805060903030705070609020a0b040e0f01090e0304 73
    0x195036080703006005000760310202c1a40304c1d8100d42140440da000007050030002010413114880e11404045992200c040b21615040c684641c0042c9181601803400d14540c080d559102ca1500c80321152141c005d40d1141030078004d5050600b10203511a020b45040001c00d0b816488601c0003001c801c1504074001d880d040c0341c105690041c80702c0c00c440d221070740c000c640d16031079801c08540c019010b0700d104030300302e40420100310f508005000f0b864829420000780e00c1404007a021407a41003040040403a0347c1c8d900c45403040701c0114244440c401864a0024065585c0303401c00800d410082e105880c03040d8401e00308014007401810754280c808060007030a11140d81850040e06407160301500110715055030030000440078140c074800c01b4078480381c03144088404980710109045d80700e0100302c0b4544000b55060100501080c00c0d41c008034070301400a0292080e0a4a4014110456015030401210744200409202c4842101240640180740d8080c04010101c880105a52240300342d11039104d12250781c8a49449 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 719154748 1250 719153498 719153507
    0x50718122301050718081005250207061121070606030c0f0501030b040513150b030a080702090609010302030715030222081504031b060f05040b011401260601 69
    0x2151145440c10741001e03440039882030702910089903010b0010b8002c2a03c9003640c000300348420305486104014244040751450180c008140060030b040303181c2c030461b2a82c004a03c15415406000755558080c2000f06d007000c00c05040080c100c90360b41d40b16030101c25252194401580341203044c91403c01190341d83c07075241c2490800f404c3c0a80000d072032440c00710303000202803113899211000c1b40c40a032020310403401000200720440b0011038007010850455042000041e040004000550902c1c500015100800c040482d1400c200b80e03800b198000b030001031400552500d04038459224a0071a102c110944c155400b00351036501078481c141101120413508401e0502035019940f00c16141c540580c480d842e1100d1200707441800340300e58401401481c032007103009843c1000300c0703201e0b540603210640c2000404900c8108138625444c240da4142d5070b064894201d0426004040c0580e008040303031001541881c00340740c441c8800e50340711414020f072154043c88503001740c2c0603040d902e40400b0041c00705540d0500182e9 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 719155998 1250 719154748 719154773
    0xf0702060708400806010608090a050f0307021302130b0903070306140601080702120405060901050c01050403081006030c08040212010912030614060c0316020411180405071812 77
    0x11540400e140818201e0300b6620f180c2024074040c5202e0940c0c00c43c00000c500d001400c9030144640da42c12100c0140072540c06100c0d009d421400a104a800c8510a921028100600820561034076003002036004190724100d444800501e0460108621b003210001da280c070068014403d80030300280100e142c403080d65050181100031501310205106814019001507900f42d403c8030514003103403208010594051000402c0744041071032030311280c40c05040000f0850a5002450300d0760401030204642500300c4028009d950145110303856501d2a42000030f900704881036580c001004140c42c1101e50307500c03542e01c0000c0940058058903001092415004894054220b50034060b004014510042d482e03154154000302c01c441440c2e00f00f440315008003003041950300c1a501c0c07101d515070050041c4818100d40c40b0702003150130700c0148000341e01d8100d8a030422654100702d041d211903003800c2c0c201c007182d0b04003030196581c0700c01186403458403100c42c2c40303003e541142c250281c0d400c0f40c00c40c1d0f0500410440410f4004 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 719157248 1250 719155998 719156017
    0x16060c0201230c03040801050f0610121d100606020c0102070902030a0e0d0206070306150905310c020f0726030d142202090c1c0e0c0102070b0f0702060708 68
    0x598443d21914110303680e034494400c0c1d0000c0c0d031a000000700d40c460030111550180000030030001c00819080317402c03201246008141f105040d603035500c036520010415000341030891454041d0135141c24010f001d8044400584c4002c040d90003465003406141c0e800316400041c0e03004508016280d40303c400b240c1c2c1c000c00401c10158507620030210b1000d50580c0001d6094802e010a41c0c0030300480e0707141c07103044524600420f140790124200c0700060100f8648004130354140892507404225200c0d00f43c41020109404030b0304200f02ca0307950310204c07688943c1488000c1d0300042c0035005288161801c0301020035039801040c084c02513910004000d4114406204581c0c22a85121382480290b03410b50008910040c01c0e224811071481e12032a044444080500140b02e07260024420802d40d1344025100d00c140d8040301c0310080907074540e02c807243c0d00300462052a103201d00410080200d00c1d0004000b82c03511180d50001168079005210310b07078962040b0811200015410b45142e500d80d802ca01e041040c1d400b484899 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 719158498 1250 719157248 719157317
    0xb0a1a040e0c0301060605030f15031906090c0608060109080f0303011a04090213180c021e0a020a0f1a1e0f07210f050a050706180c0e0916060c0201 65
    0x14035554007d0156026090038a4400540d0310b414403028090303045019090303099084a6091042243d485204100c840c1c0556408285420b00365039501e071042e0540c0060001c54070980510645590221048003e4190759000789500c103840301516030769002c1403140d10554580c846e41403018142c80c00541e030017468051403e544411030481d904041c1000703405800b580c00c481d005007080540003070145030100d000c5a00506a5803641e200c1002c21000d040c44c0c030b5840c0303208150264005860f440c094800809010092034030b02c84c1064611000c4001400d11180c6002d0240700050044c202000c4081c101c0e0140e02055030389088404119640c0e0044050107400b03911281320846903d0b2078404020500413081d0b80b12802650031700740c01c0e80c1a00071038104c0c90000b1424003140000a100707611120940604442d1003000388240d607103d40d840d000300e401202c040b04002c1d09011078035004000c0c0088035030042048510b020300b04a402444840e01c1c24020b03041200d0321011806007200f404000d6400e456803100c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 719159748 1250 719158498 719158511
    0x30c150c031c1811010e06041208070204060509040b16120e24070e09060a0302060a0914010e0d0303050613060b04051320071a0f040b0a1a040e0c0301 66
    0x3802d0442d0b0001004505070070100107a8000060300c0818031010780c84109080b40e501001d00454002d001c0351011030b00100100004541c17083ca135410b090a0f2482881c9580c3c0c0c543e450301c1403006840300360707100d01d0050a100c03040c400016048981c5a07444a03007016421900741a000d0210b40311a500310410280c0c51421074101320540c804105c080ac01306582111007400011030351802c0403070000f15044c8000402c0f038503070340310300380751829006400c181c00801541040b500c030380015066510560700a07011a48241080194440d81c3c502860442d5003420300507545900c110116044c100070000c0141015603880c0002c0e0b00d075507011f103112094814400100483d68032500030052a40c03050065a118601c08003580c0c207001a00d0054034407078050074440e003500d66105801e52205400c090000c54050041100485003048451b022030f04c04c0e880203610fa5500e040c103080c806002980680a5140c4074200800500d04607801c03004050301d0703034065500080f90250148801e051944802d4015419420400c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 719160998 1250 719159748 719159767
    0x30f0201231608091902010c02060a1707020106030b18210c0c0405090706080606120a0903080a0218010e1503040c0806070f0f0c1e0b0a1a030c150c03 66
    0x41e1414440c1c910740c100310201071071403001541c030b4520403922409650301034140a81880340107558105003a1060411000c040c14a5000903582c0e0005a004000a8ae04480c41f50301e41c0c1302c0c00c4a484d042003040c0000c211160841c0c942070a0400c00800c07443c0c07001d0f658103800c0403821040001c0c3c03410380c4842c40110300d005042c0390100c10705c1d40004084419441003503244943c40c9424400c450060803580001c002c41e03442e1880a42e40e5600050059500c880d052054550740351341c4403d0144140f0450303c00140b605564074000d4100c0d20003504c0002114414042d51500c00c1e42d40480940707010007401d003c2040d07200c40b800146010340301088403803800408002e0000b0048d4251121060703814250549240703546444003140c1d580509103c020001d0074031502c45117081e000748100c20322a40643c1c441000f0520414009070b171800b00c00d40032100311102d02d0400c41144440e104120043c800fa100c030050b5404d483c40001d6640c1c00c40b400e22407261042a0280040c100e045040741e070341c5020501a291a40e20f501e = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 719162248 1250 719160998 719161061
    0x11100519050a1418070e150603010b0910030605010e1210020a030509061b0d180204021204060c05040b0f0c0313030c03050f070e0f0a060b0c07050f040c0903030f0201 73
    0xf041c1d40784002014801055a030607429490b2102043e040c40281401490a282207189820192404c0c258002c0700c1d401128071f0711148011070103491050340082c0c0c2c03441c40e0014001e16032481a42c145c1018504141441381d03a0b441036111a820004540800c26255a444003a090403044860300c1720240c40010141c6115400d40c021a00c2031100c2410341e20030303550751a4400200041402000c0ca00780e001c012829502c03074140d0118448403003000d4102c0b801c031102d50211b8100ea210140032092140304000304020491030703009801100c2031078038049042510742412010b450003100703011240b01401280e21905540104190303680580e043d41e1b12001283d0b45d0400201022040c00103072140d010304610f4550003c00001c40700d003180c13001c01c640301c920b5494800241045002a10324009d007030710313284002035055010014020891031312000c0d0113503e10344010003090200056860f8000c038145020300b00c000381c002040760704490301428145010769181c40101d0043c40013040d07518131149500001040d840342c4 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 719163498 1250 719162248 719162261
    0x90f05061305040629090f0904170a03060806060a050604170c040f020c060a02211503010c03020a1808030d020f16061a010507050705010e03030d02030a0e070611100519050a 76
    0x2200c0c0c40c811003110200100d83c00388110103011f900805504080704041c10310103140756200d0700400c511403100741c010003640380d65401440caa1000036224081885200828072204c0c0c1c000500310382a25030103242a0201c0c815006900c00c0500c00940d401c00400450030a00503207602c038130003d10401811410b9244400250440905d184540c031642002030810400c5108480d000c040c02000001c100c000307910300e042c580750f000b03180041c0f44081d44c500d02c049850034041e040c000102602c0250f100c00e00340e074000303000e00740d0040c0e0840c2218856004004451000c4125900206018030150741da16403800040154810a050180840b00304140301c4280300e019403142552a0400030b00c201c0ba84c3c0080c0044425014080c400381090700b14510070451580201c0d00802c3c640c0c40901a2404c005280300389004a80086420090b1941c4800600560000500c4680c01070005810410340340341c1c0d00e0444560f1001f44030324005030150b8131004928414071007820b40d030101c014000700348410310b031151000029021 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 719164748 1250 719163498 719163539
    0x204060f0903030801090f0608010c0f0f0f082a0c0105070305130203030a030c020115090e070e0c030c0307090f1d09010b030a02152206020706090f050613050406 71
    0x24000522046900c1030031000200c2c0e816582c0c8641903420a003d0f200140428461881801e03542c0400252200003070040700c0810600782c0780c544019042c204040c100c40445291802000740950a1202c0d50340c100d110141c00c0035a1186000b00300070080d040c0c0b407003090310002e559100c4030003281d6011500d2054003d40c1c440e40f000e40e000e01c0a03031030b1500d00d907a0b140c0d13521030020f6140d041070110302040c0e8071942c45200c800c2c41a10010441c070294030b0b40c5c00303041507050700070292036615840e0683d4001010462035005090391044100146840a40f404c00360001900b00780d105140000410451032240012101403e880f40781d880c002076482c03500e2101c030f0804840041c3c00351a810300042d80075006101c0c00c01c60f80005000740190302403540c2000041d441041e040c81c10300e80107001c0c40301d485010780344609091240c1c0c1d100c00c58041c20600c010f45402c85aa0003241000780144d000c2c480c801919280e801281ea003038a44644882000e5026086060baa80000d40c10520301480001c2500f001000d0009004 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 719165998 1250 719164748 719164757
    0x9010e03030103050307120305011d06041d0a1a070801030210121b082401200105040b07020f01061d0415050f060a0b03010506090111100204080a0b0f1506030c130801020406 76
    0x440080c06500b0b495007407080000101c140700c44200c24bc1001e5901e9540002d00400004030f09030f03000b072408020076440307400c0b040300e5200800b040200051350400b0228206074855400251521500c0181135100500000f40500704840005e509140640c8100d409aa0f01d54820f00032002c058a44d803402401110b40302000070708810220700803052291a59001c021310001c500c09048058005684044440640000301d408180d08c80c140b925082c410070380128424240c4012a0511000c02403a1a05042038045c459140540400c440050080280c2c0403510007080c4646a41ea6420101121001c00c00058880c40c1007000b0003800b4650306207618070401c01280c0b04407225455140281050000340141c036000390040052104d10340c028603031607201040c500200d810280ca16a10071042c0c1c1c0250380001d4040e4400d01c0c10804102c66540c02c554000643e55000321035145c842c090403d80b40c4240101c5010300c5d030010124a440000d18111071a1642031020381c8105035803103110364000c1d03000703118410014 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 719167248 1250 719165998 719166023
    0x102070b0601141c15050d150501064d16120308010e0a090f05030a12020f030609100504060e090f1c12021903090204050702031e0309010e03030103050307 68
    0x2003e6030066038003003154440760304104071509080034000e0080ca20012440c0c00111000200303641d440c80120103640c840e000c0c4c40c0344c5091750342a0100340d03081030b00700c0390501c0000000b0700c00c400c04510100b95804011805201d0701e40c460f00b6090108801d44060208048145200300258000043c0c03c610340080c50034410380c01035403400074403a0601c1190740100026424001080305207001c0a40740d030040c04410740002c0c1d0007003aa440620303444a0301e0b021203007a08040340d40c04006412070980e00c8400b456040551500140b1000b8420034400100b06600c992444030100c0d00060701c0c0b07641403001d481c0107403042155a40701c025032002c01c201100c881a01784030b94004451102e2010400341e04540c0f042307203e8104e0341f01c1c1500949000907000da60214803a0300f40246824007a150300300260f00251901c000400f54a28014481610320081061082d50b00030404181d25401c00007004801d940390007a41034480c0c0b0303081030741400b42c645601c445d101d13444084004411310402200511807144602040d480c0c8 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 719168498 1250 719167248 719167277
    0x4030804140f1c06050408090402041d150904060906060e0a0f0e0a03020a1e05030d06090c02010b210f01050c121501090b070812040320030f07080a09080102070b0601 73
    0x100511042400b00d03c105410140c000500c0b10b400c103e4016110742d01d81e40c1041e2800b07020404230307081a400002c6803e2011817945054201640300c0d600000310300c202d143d00f0915440420b401d0342e4050801004965a4004101030006030f0780039501500c94442d094005060522800001c0c20b510303020380400601e031000c180c103868000101012040c0c0d058001c0c00d0f4071441c90321070580c00c0340580c40507202d10000c040500000b039002e000a001c00103904000184803410000c2c0300c011910178000410a580c90700c070460312075a072030034030084c01030300c6101c0c0110221150300021800e046d4040085a280d42c00c00d030038840c040f0148009440c40703522003503003000c141c1d4072004002c010342100412180481d030486010310206070300c0c100400d4140c0c0541d424a00e8000401440d04410008890940014003061020348648403180e44418115410b80029130030051b07040c00700100c0d403041c10320040000f440011340300340b010b005007602c00040c00784400841d202c003260f0500441e202c5045814600213a00150030654 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 719169748 1250 719168498 719168509
    0x3110f0109080c01050a02190c0e060d0b06060f090402070b04170307091e271506080c0a031811030d0305070203070f020f0307240804121404030804140f 67
    0x2c07512024000c02003101c10300019102c540c0049505c40841c002d4000c601411400403119000b0144120400462980380150056a841000e4907040c49522404052000301e45490200c50300103d040761000c1e40d64551029050592150030f155a0b0070600104581042c05a1104440c2c032484c081c1283c2035010380c4848403140350b44000c441420100e94a0082800240017810b0912003000d80901c1d0340c252030340c403040100c04008070403003621100456040401c0c00d1207807501420101100c0700100d19040d03401e040024258480040580111480105540d0002442900120640c012602480e04100d0203400c2400c0c4545031070a07042c1c042c0c0724401e00312403d50f200e4491203110f00c17955070140d41003070034944d100030380c9980304141664070501420764060f80c0c1c1c2e02400f48038010700251501400c281181b6840b4084500c0d817041c034106200e00901048003042070075000000c4000b9900e001407024440c910120f05902961308050030a04001c280030898000c016103400080c80102c07400b01c2a006001c3c200710 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 719170998 1250 719169748 719169767
    0xb0901120c12080f040b0d0c03060609060809122d041a0d1e020a03150308030c030a20040e16140702010e03010f06030210090303050708180a03110f01 66
    0x2404042941d0040100c02d07900c5050050080c4500b60440c0b40500986a000300360304584c100304200c41e40059000c0c10302c10f9a10a008591105040c00d200b00b41c41d0540141c051107203880b81e10300b030000050014403660400e2000041c0400100c8400340c03181050141c107008004c0218108003610080066040b001e4500c1c001e903400c64189081500890700d1032108195560801201d01c1403094890171032541e0000998890076180130907690058840032400c2005055490b05041c1c1000c691500c3c1e41880440c903044101c0790311021114025690b40c90706260701c1e00030b0101ca01c0100d11520f101c95408083c503092402070003111405c00c2103552980b86c04808901d0380100c41c4100c000309400c03119503400c00070380c1d101805025005040040031260360710042070a60b02001c0030041d0302a5034070420710071072a000900392240c2c0e05d18a0010000d9056540c058414800d69101420344080420101c601c000c40120903104210b010b05903002c070f03075506e00c0c09a55003280a1800780c4504488000300803203511420010 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 719172248 1250 719170998 719171003
    0x71202060402210c011d0301060312090b0903060f060a09090b0709170706031a030102041d01060c050d0e0409050d080a06080c06090f01030207020909160b030c0307030b0a080a060b090112 82
    0x8100c4240100015225625044a91b04c4e00c0402c4407440095641c003031168400460180c01c0d5140c145125000007003d201941d044492041c0d414800e60310785440c00100c483d84031403860800c05954642c900060f8241c0b446074032001502c0d040c0700100c000c03c0f002c084010f00907442502c998840a4503000c0098114004030342c4099160322081040007094880c0d0060040c49a103003c1185440300304c003011909980c41a000046101e0b500a02d001b0010b9807040c0850050102d4505104204065a42c1a0b10780701840d0b04c80c4204003103082050700d155607507070203d10180e81c018111a81d2215a100140000308110b4082c40701620b88800080c14200200d1b0003000f54400901c440d140003036450400044015100c1420b0400d80d00340b044100507129280c070715009948240003407003d00010160190041074640007201c003210103200340811008007500752900b05106060100b035444091707000c540780410303e900c40a0740784030384c000e61401d2003120703807200c6960300c0280d404d41d046d80e032a004002000d00781a48c00 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 719173498 1250 719172248 719172253
    0x11010503090d1202190207140a0f0b091507050c03060106080702070e0c0f070302030d060614030a2f3016020f01090605070e090420010507120206040221 67
    0x120545144942e501e0200460003142c01170030b01ea08202006204529042050096807002c8028010562410b03035070800340700101c4400c0302160401000c1d50816202e8440e5641107071010800b00e0159480c1c200500007450355514844c1c885040b1308159946948038004280640503190000c54101c1c0303e80002c900c5226650018241c9501d400d10303100c40d00c080104240c1a103081030001d181200421001041d03600c1c02a8021621003511101320703003c07250a0350002080c42081400030b10342c408100d043c0c0340d01504000c0c0010b9001045024413688120940b640c0d10a001c1000c0c0f4401101a51b801604a410704480000d9070007240721564051a0111002c5149501420000414603049595414184c42d201d1059070040000c100f442070075074003030303c000710340e400c4d203034010460a5544103201d03202d22941140c05192600740340c1c03a03002c606100c1004450510020f0b0f01000d020344d014108035807699600040c3c1240d5640e000c44001e4454005403422880703000f9000b032240488009103402076890b09140c02 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 719174748 1250 719173498 719173513
    0x709180e060714070b130c080105061f0c06050f01150908031b070b0301030614160f050a03020909010b090319150b0a080a03090501020105070f0203030c07080c0f01091101050309 78
    0x2000c2c0d0704500f03018a180d14088040007100d002070a4640c0c2103000b000c81c1e44266038038442034070740410703d0140707500003100c1a80f601082040c0350b83c4072001401003000212100b52170600d5000d0072210348078508005000c480c01c10050140b038000c0c28850360704031804142d804d40006003601c421904e5038018400c505a541c800d0000b0b2410704a030b95407580d814031600c400c03100d1499451070501c0300364009034010307511180d50707807008044820303682e88c5264815001d101b03000c2060843c21000d400c001d81400594104080070882904040c005d82c11512220302c01000309188e5a5034580c503008540c40b003400386009024a01804100f42c4d4601c5050f003e9603031044c601d0400746070545d0450020705038440c40e0b80d404098050001521041030040c00c0302a4000e80c0c1d41c80d000c5080000190030748501034000c42c10032800c01e89058015a0103c142d9400803c0207000d1691442c050a0202c040d006868624030107006541696194000c158000741e14030384200c542d6003c29481d0001901d40d8082203c2d403d03426000b114 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 719175998 1250 719174748 719174761
    0x315010302040f020702030d030207060c0e180406180c090b0301110d020d06030b0f0a0b101d03030904020a0215060405010e0a180501020a1809090c0e1503060709180e06 74
    0x42050b22800310b000f40c01400c0c5500fa4000a10740a40329464801007640005d07004103024a078000c4507001c03c51400d0044c40c804081c00412145c00c011040d04021024410100b8100301d083e410045410800d030158130382d0106241004103000d4501c1c40381d01960761606d09800b4950806004a05880d50350031901d134100007036100007030042e41c800c03d85404442d42c1c0d41004000500f03018641c0340161404131040780c0525086900404503991041014400d031181c1c11242c0c075095016405441e140481c410b40500783d002c1c0130100380b842c02003803409540b150000c85c2e180c00742603001402041513415100714080e0382e110310003032004030703407081c001d1340c0b0009040800920200b060303801c00c4031401404003070f2101c400c1c542d890b03041c01ca030400d10002000079a4000c0380d081d803507891403000016025130502001003000607a648003205a0700e100d807401c00f88000c4006120700d05251401c2c4002c00010f003d90384a40741128005101d01541c0c000d8541d0b058401f01e80c0040c0b0403031803181100368400f404c01000b80d6120390 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 719177248 1250 719175998 719176001
    0x50901232a010908041811220b310b0d020a020a170c07051f030e16030615060f0207060e0a03060609020408060f091b041d100b031501030204 62
    0x5104405410030349000030001c124091051809040c00b584465032640d082c0301483c01d00b1012583c4125496052010002030034821108072403089801c0a00035404000e480d10300307021807030a644680ba183e4004a03611207001109913518555280c001046200d44c0058000c8074480001c0b030107000c140c2c203414000307040f10a04590040c2000710007401213484880c2e03d9554140c08040c405403c071100d46000c80d10940083c01001050081d10f03085031140942186260001c070020b900f102d000007010b032510141c0c103d00100f444004158441c48040303411070358503400d1a5001e0100320204415030301c20700c200099074501c030f91800b0041d07035080e902421940b4a4040c00711144c00c20362a00c1603008415690000015815221710700c0205551900580c8491500b00c6060a02c4c10041c41019000480010009044004128140d410302c03500c80140d08269003101090080c848070500c0410344652440340904518001180f502e000e041c2c40040c4990503004080c503842d00807034214200b013609014010300051905 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 719178498 1250 719177248 719177287
    0x152d0117011a0f13090507032003041e05060103380916060918200f12040f02101110090206070b040b0f10030312050a0905010c05090123 60
    0x14400039041c4900c01d0742a43c40350b8003403088000401508801001000c1e00e5004240e4409110304040003100c0403115054240d24180e1310340b152414000001070100090484c0210200c50100e48101c0310b1003207450140d0740c0e84028002690704810740701000d408010301d981c281a416480d5440820708041c8000c10319003c0c1c10103002c1403210700805490207015141e000c50f0500070140369568a000390b2800001d0800b5074011240c0d409003905005800030144001c85400952440d004010343da86ca6440800b20080c1c00f60300e800e41d1405065100b400103102142c2080401c0500071144d80d17030160281130702a150b100e0507007104540b0750000e000214090100340c0c0002e01c5a07001034074240c50f000040d600c14080c103104407411621110a04280501d8220548115900c00b00e9503903070710b4006055443c05030a075140000c911074265190400a8464225a0401d42030180d10400030b100002c02c500001c0c1045d08114089800580c254507005c40d40103603031110b910b00f0070b15408601d29244000308a50a500703a07 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 719179748 1250 719178498 719178539
    0xc1e0309121603090b0a0203161a01150314390a0f120c02030d050c1c0b010e03010605100e15120a0b06030f010509152d011701 56
    0x302041101c0c1c4190340c5008040b8031200c4101030303420149900d00504426082d030822003100c2c0b818441d4034003068000048076036065483c542806803134003500e0912801c0c02d0380c119501d9000000e0000042c091541c1e01400b50b18041e5880c18041c0da6241c0c03184151424040b5a0300004891840686114100e4980c110740c3d500d8182da80700c40755840741c0c1c00d5010140d100604081c00034440d1180c1204071940311800b130a400c003100006002031080d0b010020354078081d011004500590301ca000c1402c0c200f4a504507510340040030a00001008042c0303415009200100722180424403100000da07ca02d410f105207070540b90000d00404110b1008001100c4110304081c0c0c960b003101e089449145c1c5000003030301808002040c2410503e2519003035810205480441ca0018080c0b50107006001d46180781081c41c0f13042d03401c2510072003060390f10350684001d4001c1d58903803e600035200004014400c2c1951640c010440242884002038a1404004480d20400d214a030700c5e840c0c03401c0005010580d6000e118008002 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 719180998 1250 719179748 719179753
    0xd0e060a1e03020403140a050705100206040803060d061b1b0507090906090206030411031603150b0a090c0302120105030703020616030e1203030a060b0a05070204020f120f0901050c1e0309 82
    0x1600d95582e074a21b211000103454003030f80000094010000d003080f06201409041e0358610060780350304800f950701c0002400040c928040800010800d40b1220001c80759940c0001040c00308441d062004040b441c002c0e81044001542d00c1888840702c2401c641002e10304d94010028541e0781d00d403041c03600007008015012201c651f12040007001503a907420181d4080c0f4060440b0b0002001040205850400004150322080450342c0c810404038807050341c41840340c6003800d004504144d0085c0000c0054074650000548180f61620910b052a0b141d800380140c0a8081c80c43c48103030f40c0b21010160749100500c40254050410001030301482040d85c2d404d0b02c480e110303082501c0000c0d29000000e00c041c2807200c10310840c0c0e0000c0108606030560b07002d00d40041903841156860045c0240005000780b24101d0041c0c01990002189041b86c0030100443d14042000c1721403840c0c4d82090540c115840c070059440070f030650f007000c2c00300e050450290b007200c004080c0c2d48219030300050b40d90020507030b68000414455890 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 719182248 1250 719180998 719181007
    0x50319140709110301140d0b0402010c050c0a08010b03100216080d140106081905040c150909050a1d030310091a0a090b03010c02070f05010309170a020d0e060a1e0302 73
    0x60702c040c00f40c800c00400301d007003180d01e0358144254420003040c200d113910300c105c4004c0c000401040190105c1c070307040340c0c081c68080700300d2585003080fa00c1d00d607000a08541200074103000003518079040d80480038081003202941c0c400b450600f89a42030b40250120032f040f040041103114005000344005040600650309c0110780c5010041c0c0e00380400000340e0141010070a803204010901c1c0301a5028401c184800804000604190b1288011100a030103030001d03030302c008659802d480340105440070081c214a1014071013850703d20004406000d00ea80d00b2090b0761110388040e0300a04000c0240da01c2034190105403000d003032921203c0380c042d010301a24041500c44420b4000f4540d120f030ba003144082c142c5903401041c2003411405043c21111010717803010031034000d145c0a0141c5600404808115030f800d207030100708016131f4104007407032500c0304c1c058440310340e400220101c9d0103070007082540154141d61124105980c0038000d100381031182c551070300006241c0da030764404024030342030400d903600030329240040c02c0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 719183498 1250 719182248 719182259
    0x3040e130507030b061519120914010905120a0e0f04060b03040c050112111902010e0d020a031805030c0d0c08191209030203031902011b08100503191407 67
    0x309a85038106071070135480442080258103241110041c40030071000020700e451101041620b403280340590100c2000440b60b981750741545e01e50040ea41c51078005042079000002403558900812141600320f0b154043c0d10354410310b40310300d031003a51819241d83e00d940000620381300c10062807002d00f40b2000c0e4400d0b82d07281c0105900a0040207140302d01e00c03494482c001c990401002601c03010b410030100303000c1401d00d05e8031400324101c001511429500c0090260303400c0b08004e0168090400341c4e05058240c45440304100d5000d0340042c16001030b5001352202224141000f150030b15441141c02000d81540c80f6a400d83d045007411100780310998010303d400f041498a3b440302d85d052129180e05252201540d1030000148086060381c0e5030080410f0034201c520701d00c0c40e80880c1c4c807401400702d4508120501c1c1044201c0d14001e402036409403c8441d0544a04161031101038008130042d01c030600d00217800f4801040d1405c000802d40400c450072541245410020f0391485030f203203403950f001407a41c01011400a0b6 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 719184748 1250 719183498 719183503
    0x1005041e030206060f040218040f0b0d08030711030304170304021906091404090308191401060f0f030e060138090909061b03040206070203100203010801110c03040e1305 74
    0x1442032003980075222a0130010100004034001e01c40c00c2e0b200c0e5104018198804035620039443c41c540003628081400d4130700f58a8440140070300e021058100c450009000104a10b9000451041215031200e000c10707049a48020b540340404c42d030050500c040f03280701d0f8054190035000707154440e03c001c050001c0040c059000e4482015540d0085010580d02d51044c070844101e200d02e0060960151010004a80c5c2910020b1440001401010110b901d40d1451310b186042500880c091800055141d8059650784a004050341850004203000900c0100d010342034034840d000e1240143d2080000700002c1c0d0030b01050801c08030203e09507400214111f17800020b10400412407540e08400799030944d0311800d0860070701505480040100392150010810040707854103c5244ca041c2d803c180b1500c0d1345030784d03491000c101c0a2044504c069414850882d03040c003c190315400850507a08054000c3c800799031681044011409902d003c10303100c0d00203100a002d604070440300313503600030002010401c0782c0385103445407030 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 719185998 1250 719184748 719184803
    0x60c0b0402063117011104091805031809060603100902030a0e061003060c020613030e180a051501110312070e0916030b0d02010e040b0a0b16020a06020a05100504 71
    0x20300000107103010884c2420b0310150320300600304040207100c0880c80e80940c2d18544602e00a0380070b45550f5007404210321000a600c40d001c02d0b407110889942d00900c40e007606045800c1c0c0f0b5210b10640482000956506200c4e0a0b64000c0345c28240c80300c596410030002c0406500010a900566682c0d84d2045001090402606024450b03011400140707909500b1728206035002080c642080d54880c1d824040c40ca803400d0101d0f036080ba010f152002c07136010044c0020340d4245429601480000c09030703041c003949c4200796100b00d0217001c89070181e84000840c0d0006407118045411880b41d07903001440305200103440703400403640c06646ca1801c038103c2d420050000d0303241801540e0020300954190b00d0044465018481c1c5101e14404640b00c0054130ba040d1f000801c6503001c4400325000f240c442c17540b43c03050b131070b12401c41002d0314a0303000719034480f110101418441060701d00b00b42e100d80021000000c2090012803c01c00064101c80a003d03040e03462010000902000341080382e0181c2410b0320b800300c0e015000d5200303 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 719187248 1250 719185998 719186077
    0x1120209061602031e0d0507060f0507031d060709170a0204140a06081b0409170318100203010323030c19060b1002061b091f09060c0b040206 62
    0x40c02d900340c0750300500d40b600c1e80040d005c400d03d68030442000380d103490006001c0040701307076817034030940c1d038141031614101410f83c03440f5a000135418207061180080d09034001800142074034100d424039014080109a8444050b00e500e40440c1100005100f400c80c4c480d9400c40c0702540314111510950140e004c84d04a4404c4508081c00b1080182403190b40d440f0380c09442e00401c8140003d080c441c43c201d10b0681d00c40700441e0b180e031040d130f910301500c401c0008015070f802e000091944940d071286449940c4918804c08008292401e009814070200400442e109882c117894000f580b9200001c0c5000c034040030006180000d108600c0140041c3c80030210403c540c507045241181c032020228910b103400004c4d5285d6000c5a8407421041d90718100305940011402d500080c54a1401e682d4664000c9080c15441031702c0e41c0c25001a04458200e84052030001d03648400407803980c921031015650202128550710030800201013105080105026260200c042e05a0240300b07081c040300c0740c441c24184030303d00d0f481e07031103c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 719188498 1250 719187248 719187277
    0x70308180a0e07021504031e051201060c0b100806072d02070503070b0f0a050702060c10020702040606050307080a02030711060406050f0702120d1e02120702070506090619020a0510021206011d0112020906 89
    0x120b42c01c12041440d0107800400c4a098040c00c0307801c011885403560780060600081002c2e42d00324f0040640c4070300c59100e0440250316000d0341041c4245c0700030b4498116020701402886a07d1000401d1b0241c82c084410010144144e54140f00350b03178004880941c000d4a003680e00410901c101100c2c2132080c48041d0100781ca118005a603000244140401d1b1105a4415000e00205000f00302c041c98202200036401011904016503d56a000082c1e402e844529401e164038440c0034208010046a5440f83e400780e241c613521028240d030b481070100e98a000c01d60181c240c041043c070681e1503901154000700100c1c889a0070264444102d001e0a1040b0307086010b11010302c2075918148040d003601800510050901555024078006c00300c03000c00c0b524414800709030850001a440c01390070510030b10003500314960140642c0c01119074151440040e4010000400d280d05409011454940c01170307410403101c86603c4280203101945100548840f82408503131440d840e000c211803001681c50701d0082c41c880c0d001c51034 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 719189748 1250 719188498 719188517
    0x40e0106140414010c061b0305250f080702010609050a0c0f052104020f120d03050106081603050702070b19170603070308180a0e07021504031e05120106 67
    0x80180304106040000e071040400304801e100090550072265600c800030700304041d03043c0c01d519000300200403d00c29a111980359101d142005603041d04003030300801e80645145c500711180380c901038650040c80b140c100403800000724011254060502554002072600001030b0140e5100740103800e841c8c0440300d203101d40759680e4154558940102c5010000c1c165850580c2c1002c40c2101d500c60658001c80302c1d500d2000124001408559440c0051030582c1c901074424000d000716400074a5882c0f035000811000300741000d0020a005105102c45031281903a07030704a090912900074150000d10707014100c0d9003180039607000860900072190003030581080e1040b026400c900028001805500b5101c00740710340d070f100703c0c050040c00e0b40c0015440050380d40150010780d4038440b413203aa0307120700d014640403500f24000010000790700039040c071014030649154090310490100121610b20f1810103c6004020940524400046442c0c480f001010058181800351a2403094414505100403d0307203e4000942c4009 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 719190998 1250 719189748 719189759
    0xf08040501080a06050f0d1103030d061d091009140a0302210301031a0613061203080a05090a0605060f180a0b010903080306130609050906090c011b14070b040e01 71
    0x1038001e60f22511014042110a042c0000242c81d4044034003400c0c42070003a201c6074001d110401e00c03074a00210004040782c0d0f075000d02c0b45d6208007411a612428a550f039011718200036021101003018801c400740c03009410355908403c4068000e020003c1d003661103020301c480b0303118040000c10014115900a400400c107000c5403d2000d18444545203003081c000c00700b40b004000141441c0964801842c1054524446544210100d00807541070810580c00901784600040c01c65900501c14141a020b541c0768000c5a4400d5000400c0c0d60007a01e841d40035900c00402080487c0ac41da10440d001240200403d0500c0746120000d40e40e42c1c200e02050041409071000d01024115510494080b00710078200030030f0182c1380d502d42e40c41d2400003e20721402005444810301502e01c242d403114024060442d81000b0b00d051074850075a58802c00c4409100a104084503070030298060305c0b4080c54100e03490b005e01524642ea503504503816414625190083c0700d150401308112004a021304060881503190f040c1562415 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 719192248 1250 719190998 719191007
    0x30a0e100b01020a20030a080c0d1d0907031b030506090f0118050a020d0207080a021e03040512031204030c030e150d0b031501090902090a020c060105120102070f08040501 75
    0x24000c000d08103140c088584000c1c1d8003c18a402c00642008050f40300450500c6402c07110b031110b08866901d4001c4807940c0040280ea9000b40080241d40000c40b21149800502507400e2546948542c0d088440e2442000b80b0745008856a94007680c141760114244a103440030384850b00560740100c1c04030f0b4841c0d0030050740b0708000e02050340c040b010601c440b030325500d4a420f00c00c0806c40f901e21030034240c0e195030006120801e250110b622050f4142c0085540d080c0b6070074000d00b15000700310924018001c80c5408050302c0c07001034590300300343e10100c041c0d86094030700010421000322111151145000034170043c180b4030f0440c04000e20841c0030341c8501c8204406c920340100103c41e40c1109a109071015601402c400340b55405451400046400000e010840da01c0001c2c40d1484c82450508032103078400020810300c40e00d40004410602c01d070f80c0c1d11410745880c4102d10580c029641104520350002d401000303186045035541d607600a64400044c0381100c1e0b510b950004009030102510b030308100003410001540d10 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 719193498 1250 719192248 719192263
    0x60b0c060606030402010c02010f020c0d0804031401050118020c0109080d2a020601050d05100c09140607050a0204022203080a0f050307080f0a0621060c020f03070b1902030a0e 77
    0x110741203451880d1517030000c0e01705074140f039000c6e04000980300070700c0c46c45000f0040ca41c0760510050410114a159183c071340201e134450302046503841c55112003031000300c0d814020607041c0d0320180710041070b041008036040c1c02034010110101480d906c60400001081c0780e00001c0030451a0400302241480340007a04414058807000142600980d40e4984030405602240c1281515412070b1a5003840400e030618034500b102130500f24214903d000221b28000e5000021081203809030211241078400000c104100ca01030200c02078000d82292580c40014603065004000f5040c811102c0541c4c0800c4400c8200d0340c0407160401c903882200060140c2c901d540100c1d0190303440c061843d0041ca1464500001000a0780c0940651400303d08607000c24a500e259400c8000a07100107800003000081814900200038140c035002c0c0c501a1802801450192020940c01c82c412400320065151200031b54506084c00c0c8001d211440c401d503140703607000c01440c1364001036009081112021440841e9150307045d05001c3d4 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 719194748 1250 719193498 719193511
    0x1d15010b0a090902030c0c030a020a050610230105040b0a03020409060f03020d020f060d020705071820031005040c080609060406050a031106070f240c080a0c0c06060b0c06 75
    0x1e01c4556003141c1d00985420a0703c400070000b580729121101c8a00e16800b80d42000100303800701044041d1400e50002d07190a219001c0c03002c4982a444000c0a50441c01050040c41f121502200c0152007250303481d80640703010201032500d00e192130764500545033350b80c11282c2c1240001e60005010091000113000b000301418142c441c0c51011481c41c9d00050354908040002401200ca004240b15242d440f44103031006020525021356440880e49040d5444082d1030140c9200c3c82940c203805402002d141c8111085442d040300002d0302e9080020582c0c41c40d0300010504905c500d1049404501901ca0340035908030310402d41c85501d0242040020041007403c000c11030b50145180070410041651035030b40140880381c10244c800120070400012540b144140c4402510348040c3d0ba010b402001401c010a580801650468103080412125808190b4420501400025600030045012103440d030340203291080d0203040040800302c1690702d001c2a25601c0d40491211034003c2064800f00c80b0030302c01a40c0c04003 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 719195998 1250 719194748 719194769
    0x1d0f030604140111090f040b0a09020414010908160e090c0a0e090c030a0c060c020f0a0e060102060c0901080c030601030f1406011205040507060e06160f020f010e0901090f1d1501 78
    0x803400081071010700c0c80744805200b55290f4042d804103449d0000c00c00003400301074100b95a00c50b11401c8540115a030078002c6400130742e51150003e038001c404298440c1580c407000020004030b00c2c00302d240300c1d040000b4089042e140225007518000d43e40c7c800c002c070003c248142c0241e089140200322182000010388a4500940012001c000005e401407552030035503000b4180f40940304030500100301c80d180d003903402c00e400019141010682010300f14101c1e120703da00740e086032180d82d1949201140e80c0590b056a60225001c4008103100c40c1c00c220285a01c0241850000b8840350203540c44420360f080b03007404a0800ca050000c0c80125607011107064158060003100b444581401d9503160356444181c860030041140c02d1000000c45e956000c1141e030300705014443c28410303a1150502941b046a101001c902c00d070800c600c07051f42540038030525000d10b08004c10585d640c0e8a000d490030081d045140704400065640c90745c0c5050390103040382d41001111804000d029011560240100012068020a000340d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 719197248 1250 719195998 719196007
    0x26060118230a20091302130b070b090c01090803030a0507050d1514010302070503090411130e070305160206060409110d0c090606030b090103030e0105070c0b070b0c0a1d0f030604140111 81
    0x81e10b800499500c1641c6050006980321711f540d03000400341d440d5802c0000d0358500021942c2c18880003464580c003c8a039401610050300303801c0c0040d0f508811f00c4c425054140c00501c0007690007140e0703a000300c0c0d10007294141030b8501102c1c003001400321a00d200d0300100c801d50180c403d20951007400d810911440d02070908620385030054441a54070b01410712120720543d201c0070b2044100c40600d01340c0d40651580301c21a1030090701c5402211140f81d0494070080000d103008c002441a0342140925103071030b030b40342d000340495444940070700c07025050403407054400c0c403022000700300d558031703544d04860700e544c060f040e00c240103420201704106640c2c1c80e500c007204040c1003d821451681d44c0750b60290441703501d820441d14412342c02d40180c3d07050098110241c05503421002c002102804480182030b080c0c815054105503950303030602d0311421701882400f18000758021869a481c0032503d904141c207114000e001c002d001078140e001078a032080441c2c046071100051128070000d000709001d03420b00741001081c07641c02c1 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 719198498 1250 719197248 719197267
    0x1803090607060504080403060203240301140c090a0b040f0602102a03060b0310051f091701110c0d020f0f0c060307170126060118230a20 60
    0x190107401c0e0054026580ca02c04201004500000c640007194003002c00e5440f45444542d007440c400200c1e110990344241c079003044c28540703418440e92080300415004d5805940701c0010301c01440d04604500c50300081034003004a180850031010300002d2000440a1540078100b04000f1b040c880f00e0609003000c42e040c080b512402c201a1040000460309502c901109604400b05c04c40c040c1c0915800403005007000028429103031080c400f4041590000e0325481054058503401c00c0040254003110800951174103014820081000101d0304007200f25000032170010100ca40010345640014956465507000390b005030206a01808041500d262941c081d023a0230121003a040e444114010720700d4400c0070000001000140144000e040c80c80c11050b14550a6840e04608841d0002c00a14094065420035603841441d000041c064141c64284010340c028050340324001c4043c0c0364042c00c1041450003650a06200440c054105120f03201c0c40e0004214001c0c04100050f1400c0f8000c2020341c542000c2098076070 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 719199748 1250 719198498 719198509
    0x1b060403080901021905063309072a06060b131802041716172a1e041103130f1b0303020102120604020a271805180309 52
    0x1240d070440c0356a5a1030720030800407401e01050100700840a001c150f6003c1c2070000000d5414130803819010032550a01001c8440c28901d0320002c0c4010403510480d081c6045405d12094494001c0f04038200340c0404540500103903059000451040040e82d0780c814440c040c0003050041c4401850040b5105240200f0048584014200ca0240c12941044040c41e0707000c0607066411540100704000741c40841820444265458002d00240d46880000000010660454500200c42c0f00c0100702c1c000d18000828449451014074010400c640b0b21814250b0340101f0389032210700181550008150350402d00503841000f003220b60000e0001044541401009a4813580314688a0f60a4014200034240700302d034513180200d412100142d40c0b0074010000000100741e015000340c090384201e04000000d9540e10402d100c00c900640c0303c600002042c00c148681d9440103104124002002c2d01031103242e50b500c84418040c000401552001481e80c2c440c10400c00c00382c1c5261054010798410007561900701861300198 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 719200998 1250 719199748 719199757
    0xc1002070308010902130b030403020a03030b12211e0409140412120b1f031b0912031103030705070302060a090b01231008010f06020c0d061805011b021b06 68
    0x1a0803a80c0001c00c6c03072806640e00300b454000e0060b06005a96450f007032800940364418440d044012030304027009041c0740c1c03502d01803075034034140080010308580078907900780c920842c003055400c084400200541c01201c99001c2480300c502c1e000416440d0745900d00038584007290403080034541c0112490003844001200201c18003100c1d18645404120344411420010041030b03007440b0b82e9408080341c0800e1807181041c1941e034143e04580d460030440101c60107170310640c020010301d40000080740d0490600c4550854460440240d020749004143e0134100808540786500030740e201004944041105c030200340e41003082a40c40070190b60140300c0800c09985003000e208041c0205000c0700b0032800e0a0709000711030001c502c2c050800400038181007003650400751084c6000e020700038483c00e420f580400e0341400040e4240300c210010703000d140b51455070b0720307800e00500320b04600c41445a0704469290201d4401d0041682c05041450850301c0c4118020307010b0b01d040c00151411801d0414402c0d82c01c400d80d1400281d9 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 719202248 1250 719200998 719201009
    0xf030f0309030d0509010c1205010803030609040f0609030c2d060c1704060b030c03070605120a1d060a05011203020a020420040915090b031e071206020c100207030801 73
    0x240c0d141c1e11116003141c110b01550100701c0a442c5410200152140150032201010800303444060f45401c1c101c086a00742d441c24043c04013a0f603c1040400c40d80e0503c40c0d10306901c24010b1013020442c00e191354403a41a101c071080e06134000ad809603d04806d01030a0740c0c6020301d00d094207030703201e42c402c542c0d032100341d03603a06e004001801c0c01d6640c1c80081c109a00501810324014800714140c251443e042c90500010909280c01502a1141200c0381e07655003000a110b80a0b1481d6465031350422910400d01070420800a04982503ea140c1074101c000300d40704228500e00004210240c0110300d02a41e0700012a04140c0c465150b820f0f0340c480325804603401040641600b5015503010601113030b0484101d0341c1d014828140d0300100000540040c40440c3e580c41480761001e880c603101c509940d00c2001106480c0180343c41a07145d040340d50954040e80c0c0042e21107405031114016586020384d155440c03051044192800d0390311a0700040d0342c0007009002e200308907036030001c0181141081c146840040000c501401070 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 719203498 1250 719202248 719202277
    0x70312140c0703035d0906110f0d0203090102070c031a090c06040b131a19050333030303090304030204050906090604030f0e032a0f06030610030b03010f09050607020f03 74
    0x5020b0001c8940d040340c01c0c80505e100710a1020008205844020803400106844261800480a0000b00d18034115107031040c280d4134541c202007003000244001c7d44090300c411400d6508026200025601c0d0b0101c80c001c5000c2c58141c0c14101c0245145c02c858400100b241d00a80c10043c0b0304c04259481009950507a4111b415994071190038040c9404034034883c0e0001c01141d00f540c3d0903505c0300402e50f00181541614011212207080c1d41c0c210581d500d01080e40e011625030f610084040403c1d440007806180002c5031081114401c07921000b0a003568025505820240c00000c0c05006500300707801f546400c002c0e13250080c0701c11300c2c250280603255200500020100302000b020380c60310754400c1055680520004099601e0342c512280c0f03800d41e5107644d28459034554181d0b90824034619020700c514003e5100513007130f203145d03a07101d004000d441c7e410a107504051507074400b19400303152403d21070034910340308481c000260200d180c14000d103012001440d420441d0301401c5860001d003030100c140d400c6008034064 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 719204748 1250 719203498 719203607
    0x501080121020a032301020c100f15090e010b0f060a0503090a1205070303050115020c0402092e41040306020309071e0602070312140c070303 62
    0x41c0d0400701c003a101940c0300751103000110505c0704c5a40001060207054012285002c00b8400c09400c0c0d000c0c4c90100b501d550010030a0841e07030704154000c541c10818400c0009400503d4a890f4402d800b145e0304030304040ca03136071169210440741c24454998446000c59001ca0b0b451034080009a2a20032101e541c030403c1f80110100e13219000400003100c449511805122840402d118010070a4020710403d03000a0f0401000141054241d030030086404410790140580c50899810f20020303600c0525810f0b000f500c0d0042a0380d030403541c00050411091070070074221801d0841140100f2585411450104000d290500c91440e0884106013210454001b13040c404010020a03e04400340215032016040391300020400c070802d01c2c04507003c0181c401408034010007003d20120354404001034001d81700540d04c110401d201042080b00d4040020340240350181d50000c0004045817143c0000700194a0f036400601c0c24401c00d60460581c000d1086490103041c0c1c0d5480074072000a2281e1b00c0c0c0c1040006109006 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 719205998 1250 719204748 719204789
    0x608011116020a0f06020a0507380c011514090f1807120609120906090b03061306060f0e011b03050d0f02130f05060408030f0f0403050d0e130605010801 67
    0x483c61000300410b1070790821050791124040d454522413002140c6078010a540071509031100c0000b1401124a441107a5002d80b65501620412454490010003040c00380000f100e070000034021a03070340b00e40c00030b01c415000c1d150007054a440c2c000441242c0c801d5051804100ca10001407c1d401e0380315801c08088c0c0040c2d50001e0946090111a401103980441507030b80120a001494015201c0c0074803482020a041d001103404446880c128001c4e0740c002a4410b40800554101c1c502442d0401802040d449030035503085580700072203e0070342c0010007203401070541326031072a080030351404052030a0914003103c0e100290041c01c645440c100050910002081c880b1042d103ea90298401e02654942150313100da400100742c0c03c03e8403d210348004900c1142c00810303241000f00030b440407290001d008608201c0c0e50348444031203400035040c00390129001e12000010030070400c000d9004084c103499100100b03241c01c040c4070b4109804020b00000340d0521a0411a0341da000803c20304450a8101c1c6401808001 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 719207248 1250 719205998 719206009
    0x1518062307020d08072603060f030c0d0326062202070c0905150315010e090a0b0c0406090603090c0306020d0e0303090714030f0c0f0d061509060801111602 68
    0x568040d40000f440c40b440e40811800070000c0044070702941c00c422201d41d107203910b004c81c45c442040f0848440030600c086120ba041112100720718a174003c1c00c0d1245d0071401800b1070308601020000f0360001e0a900f00008001190103840740751080c02007801e01c814901000411014110200c850301400d1006400880c4e00000d0fa040d202803681c06401103180b540e581d02c5440c0903290a0b02e502c042a034200e4010b141600d000070300044400c0d4904441141603103004400d0182c030100410340c08941c02040d1014000072080c0c00c01a2103020b540810a490b0350804e00020103810039600584140f602d4882807034003044080000a040b0390b4054030150740c840c02d088009002d0071401594a81e948004010302c88400c80c0455020151040c0d40c00256002c0035480400d940c4a00c81e0122070100d800c04442004a030801828017034900c40c014114000d50002c035070b03032141141e00c4079031060700780b945e00402485803801c64000e20008101007002802140442c4503090101d1240400c0154513000010b0310308215160b8 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 719208498 1250 719207248 719207257
    0x8030f0f0f0420040c030606030e07032a080604050307050111090d30020a17130603050a15060f18061704020f06030903070c08161e090615180623 64
    0x81c04c1800b0780010483c0c0030303003e08418000c10340403d080090a040b0b280000580c582125081a03100b2006050070b500602800695400c0c0810a540e056011420701c008020450050b440360006540d10802e5040c840d0840340d40101b900010b840030000001c550742c1c0d400003200c250b9009921241d039880c00384031840c1d069542484801880c0c0d036040e8020b0f07010360086a4541001d020702400ca4290b04040c0051080c3d05c1241744c0d0401e020340b101c1050081c1842070340f02c2d5030300003440d0b01e0000703440041034109140c4400903842a8000340c2c0801c0c02545042d4841c0c0403c0326608030100780c030022030900602600ba901d0a01045215000e1500000c040d996111006010400c000d001c142e41c908108498030303100d6200c010150352030211007400040e84c050002e52080c6c100350500c100c4d20790a0400640e4000c000442000540f401020030000c0750b203d42c18401c40008200c01d802c130403650390701c043c4098400c084010310084003600120042001c44c1e00000780008910b000c020020141078903c409071814002c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 719209748 1250 719208498 719208563
    0x1050c0f0f0d020c040b0a06051303021804120c0b010618031719020312060609130c030509010b040b09011403031b0304061101091a18030708030f0f0f04 67
    0x5049201005080081000780c2c1100d40d580c25200461000c03c1400159001d20580541250352034030100019441f54003e41101000e801050207055503940001c1d01c59030468807510944001d40c0d0034003041240e1480d050041c10040e0a1081200c1c0003510340c1090f5500512449007401480d1861040810fa131800030b0000c0d660240703908804446405140a480c0c00c54031800130010301030781300034841600000c1a200b541500542d001482c0d0b44403014014660440040c641e040524010440e540c903156008100b00b015241d034000840346004080c0078251054118550700451802c0210391964641c810198151001c144096600c0e08112001c2417943c421a000703101c041c6820600c0126442011000300200c40e020340d6000c040b03100c1e224115080f50100400203001141c68040441c0301d0340c4144e091a4040c00811107540004408091981117900205c0c080302c0810000082080e144240d103103a6401010407a41c00445280c01140e0f01403440d0050409004040014948a0402d14030707520700c050a0b1 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 719210998 1250 719209748 719209753
    0x304050f19180f0f020403030201050601050f1c02090607150501120804030209090c0d12020d03050c0d050622050109050906130f1e0f03090902180d150606080a050c071101050c0f 78
    0x2d1113030291100940141c0402c80c0154241008070300650711800589403100800b961052400d00c416074811804080c1920319010160207204010507a924000501140e42c05010000c074941c803000906011504160031810450740c000c424040402c1c200380544065a40c180c0d5091015100c08606920b458040075500d035014022030900c800b00400b010b5604a80e00d41d80c2c0840309002034030b4606400742c84003100c3e102c50a0005002581c64820740d078002d075070030071400340c100c01049910f940303020307003411503444a03030700d25600c4800401002d00c0318442c103980960000041c2c00365051607240030384a41c0040c54060f21841c0200180c0040c4540342c20b8000382c1101c04d0004404001d81441c0c071304031030b041022003607001c184c800100045c0001c460007284c0e80880c41c0c010b0428404034280410440311080f10342a144075144038a00741104105100e02c0c0c025103510740715040b082c501045648240e03130008020580f40f000600102c0001070f24428114099a400d0803c0c58640040c94909498541441e945501c0b41c03 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 719212248 1250 719210998 719211011
    0x80709110427110909070e0109080f0717190b0a0605030a1406090a0224070818130209090c031f0e0a0606080103020d08030c13080304050f19180f 64
    0x242032410704003200c2c1c025194140f0600480038100d01007401040d2000e034016000d000082c0029104101346840c402050504140701519180f04070b02d0a00c00da0b21264155201c00b00034080c2d854a40d250086552031407000700310f54001809410701c03901588900402d42e0b03003108049a0300c08000e4000d00c0c042c10000d02142e106c1015420200d0480f0b011548412180c052800804c0d0020b00119803000e4094000e07041c2d90442d800044c20280940802404070120982032204c240054408002403007a4a9030365421003141640404100da0705028070f20351264184100084000c0d5200c480b0f0141d0b022402650f032540320f07519001c00624404040c0b96900859090002c080b07072003c55003030064000c4c007020400b080740b691901300c1901d00100c01c0c00301950000300e0f10309442c00a0800300007154000c100841644c2807013221111580d0710401500510440c0c2c00220f8180542d0030084101c50441c00d084801c10040072002c10748a031242464040d6138160761612070001d00f10b5146410074000950b0b8100c0401c0203 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 719213498 1250 719212248 719212289
    0xc02030304060617120307020a05010905010504020a0519050405190e070303091a04030602161205040306150605090409050c10031506090305150604110a0315050a0807091104 76
    0x899004a400700c40941c54030001298405000c42c4031100e900e0b00300c0050281d4228814074070616040200441c0c00c40c81801c0200340090428020301c00c81c0342c820400854075050a01c10007031070380800e400041c020207404089140e001c00d2222448211502598009002d03114116419a5890003d000152103820b05c1d01c0d144920500140b2002164000e070b40e100d14140d241d00300740c004410a0421081e0740c0a0a11003400410341983c01403101080030b060400b16070500b40c1d03035040607a12030f003c01004505c0204080050011900426007484a000701c0b6030a49414180e01410600603041c0050150759181d055004100e030400c0441011a80288862110000d0940050203019008456a260b19008000042140c0198290380075640d01a010b000304001d1003100e0413a1500090449034420307110000c08429402e000c1c02000880441d55011a014010400800351107200b980064000e40c0b0b040c100700815903010440d10290b0310b80c0c00c00818292080b04010003180150380007007402c808401a080c21 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 719214748 1250 719213498 719213503
    0x80909090d080c0a0203041e0e011203030e0105010f031104110f0406030f0e06070c1e08192a030509060a110f0c1305070201092001170402031e030408010c02 69
    0x34161540d41d40503079a640b40f070040c0c1168024074001d071000d60300512040c0180c002400c000c140786885100c1c0f01d10300c6a5036031030901c3c4800007a4000740c100c1b16408485000e15a06014601e165120100280b00d29450003054480e440407522010b4038000c0917801850721542e464008110303040b0320f4518280ca502c02041807100903030162050501180c034002068004424078020480200c0c132203400350402c1e546150094801e91103080c8103c5160340e1250850046504c0303940310065560141003980d403140c1c428003000401c00444840e2034140315a52030104d49003012a0292841c03151008143c0c19041c80618095650b801000c481c41e600240100781c2e81c5400358401801054211a941210041300c150000503407980d030f0515a05030000510708120148825503000550045c4c0f040c400003800c40011b845203008008204400c02c001d2036070314050701c0d496920540c3c80d90606c100404440090500d41c0c0004d0b40e914440d107080000c0200d084019000700401e200341c030001c0c0303c500e00030b20001d01007460094 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 719215998 1250 719214748 719214763
    0xa17011404200d080f0f0f030103030224190b040605150316050a0207050613080d030510060e0105091306050909030703120515011218080c0c090f0703050408090909 72
    0x144950409048002d2401c80f0b0001c80c21a00704100e285482031a8080e01181c0c2c0c403103401a041c4e06410403120031a5805480118002c6000354080c040310289a5041c00f0314011500300e100e1194101002c0c059074401080d100e0b1498045114000396450000300401d0103010f5aa11240e807120135840d5503c8407294142c010742c41401494024101214284010f940c140a04540003006a1042c081402681000750040808c45140002c01c00040d03039030b07640c461809076024044000240c9640034820842d180d00e4452010700300c1c40c2810304000b945040020302c507024280c0c49610130301480400c80c081180c19880000075141c0640041c41901c0c05c074011660300d0f80011811030002c0c1c0e20005030188107090384602d600849010a43c40301a50034100111080c62405a11403405540c9000300603440380b40000d4000d02c6449031942d5512058414070761420300511721311042c0600401020001c44400c104801d55008840342800943d40d03c131411301000c1c0e0b004244105400c5184602400418880060040c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 719217248 1250 719215998 719216033
    0xd0c02040b220c03060f0e0910050a0207030f0912082107080f0a06030c09020a0e0a2304020403031413050d08121b030c0c03070609081201140a17011404 67
    0x70f00600600c03010440483c2c50710b109843d25920f40500c148015060300c180c00e82c000000d0380407666040c02c40080541111401d071140b9003510380c005110000c042c5c0008158801c10140d050102040380303018a2201c440400c1e400c0100268000204821100d2800c050380c2c14114508612190343d1401c070703a000c0d000d10f40c02d0b22134400c10f1101800048202200d4051201641c0e44100300252503881c0c58a08400394220715282424082d82c24020010364544041d000300602281c4103141c1c4c8807940121a44400318141c1006004900410007800440e802c0781c0401001507540154035564080030b034894101c403120390840e41c1c1c0052002080021701c5400400f8007150000001080c0003911403e194801440c50040c07010700c1c0004c203000054200d4005000b4105005003801613929024440d0744000c12524400001c980d104c0b004101c0c4002450804a45030151020841c0491080741c0000002c1140c5400d20407000b20810a030f0068254620030340100c409003644142c080d40134209483c05400e03460002c40c01 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 719218498 1250 719217248 719217251
    0x27121201080303040203030d090f051b10080609041b030b010b0d05060301020c1f06030803090303010915030507140406030f05070303021c1b020114190e060703020d0c02040b22 77
    0x42078a0341c010088030b01031030b402401107141c1901c1103a0755024055018003076070b104907588041c00201e03400f40f00070200710b0460818100741c0c8401d0000c20080d00440025401004012800c019036500d524aa841d0001e401c442480384130501f50108035070a20280e08002c004c60a05000003a02d1b501200c0600160a840c507030900250790b54906040c00c0b4002d4003184c405030b030312400043c0c42180007100040101d041e50200407410f00c0c0c90351100b01450340152100e0100364000401004401d09500c540540003805092070340c1d007a860341d00d030301c0d40c1c3e030f0303141d00a00c03040d181c81030155a156540c940c0020300443e480320802c006080c45d81855600e41c0c40c648001d030090f00039107100c0c01c407140410100301c04040300ca40f620411086240080381c6054400e000490610460440b2080e0407080c00018005060a030802440e1502c0e810780300404450f400d400d2070740540d405101080c0082d402042c591941c56052601100a0940d400040e0190081030022030300400e860469008140d8489070b01c042419031001c0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 719219748 1250 719218498 719218501
    0x8071b0b090a15080402040b1c0818040e061602010f06031103011a151c020708040f060801030c0b0c011e140f04050712060b18012c271212 61
    0x7032100400c60f004258000074104000540180340a6000c003a0504014000b54034407000510400c00d058061a03040c2c8542c0b4010034030300440d0150100e0005020420780f41030240382e100c01ea020307666203405082b4224000c00f090348160803510035800074002c0c80004606006495890402240c98048844081d0003035003042c0d10b0008442101405040c01a8042c2103050200010f900100d101e0300105074201e80309038841390070361034010a80085c1c4070960041907825a260700d0100501c5504210358012000e00444200410204010244550485000c02000750f5280080e01d0424010100780c3c80040d106c1684018610360f1a81030790003882d1008280105908544400ca40203c0c0008101c500820b2070780f0404003401051044280361a8151007804040340000500700011540a1209111420807452100402016001101d00c6076400405030501c241d080001115122240c0003c00b070401807c078403c200c06046030b142042419a900c51400e5900258002a6102090b442400b41d540760034801030 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 719220998 1250 719219748 719219759
    0x1a06340b16210903170705040f090603080d0c21020c070608060a03060c05070804151d21160305010501050103110f07061109030f06160e0d08071b0b090a 67
    0x20b500c0260281203102042184940381e000300080c2c49010011010466039401044501e6503201c2c009020710320701d17101d041d00c0b14184500d0003054a43c9a0003598024100b502c1007010640c410700f110140c5181200210360b01018480c1074858401d9000c0c089100b90a64480c10f0008800f40d0291030010324500c10764120076600c03c3c00703d0b0b0001d02594180c0d8400700340f43d41000041c005501c651480780c02d40c1449800d11f03150307071900e0819400982c4115150554041e0400032140e000c02104000140e004146c0703901d0b040c41001c16100740042010500c11840c8030303243c110860080049403032003010380f8084241d07240c81745450790280100780f00c0c150109080500003907140c05210300366040603401c401d515041c260359407603040c0a48644003101d00b00c840d00300031001c8640ca00b48440b001c600e400030000c0c5254200f1540d4144840b030300c50451020064450401b19480c0e039018841c08420341c010724901e49034030740c9041104070402c1c6108842c100d158072020014001300408042d10403201c0c211954454039540300c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 719222248 1250 719220998 719221007
    0x110712120c0f02122a030901080c0f160303060801020d0603020f01080702030a0f140a0804030e0111030726070b07080f040c0b070c09050907091a06340b16 68
    0x41c0d007103005a0000500103511070914009002079000c2070029517071007020300e52240c10310312480780f84000300e4100041e4241c0307558000000c41d420942d900d03403091411842240c44100c0f80200d14500d042400748000c030b00141031103600a00c004d0a0140000c654510001e28000e0040945d484204d0081010b561000042c0d8020105a4425a0355401452030000b1441d8112156100705098200b800390001100351207280c1c14000e07000716030312612129103a0810b418090005070044452504005451483e14040c180200c19142030690149000c0001d5003484012040c64800702015100100082411800e00c0358905540d805840c0301c1e100d00c0b001f51a10070b913014008808071000707000704209582c10040125810001c20480d40a104020340c11911504014140c40040d1003000e02c0b0b1b4090a0180032241a510410b0400a54103d40a9010044001080071801441d504071090b094031040750034158210041c42088840d0a0030f01b405041c1d05260107000c10b00c055030911003511113200740c0101c16015 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 719223498 1250 719222248 719222267
    0x509070506030c07050a0c09050f09070311060c010216110a1403031608090a0305030c0c010302090a090504080d060608010905090a02030a1b0305070b030603010c14030604110712120c 80
    0xd01070714038698440000507460b13800044100c8591081e0420000032a0840501001520b10035801003040c1c20428a80d20303903240003420704005500300366000c20008141c00c0c141800400240e62864482d504603da0500a015025040d0407083e40c8601c000c080240940510300c0480381105d1195003992682425074451144114280d0164020403104401241e00b0769070303803d2240f0600c5698542111301010611000701503004407081e50010508074003078130080c00103c00452080c6004c501300007100c000242e1155143c440c201c0c28640d41c00c0480d00707002002c0300300e0300d00c40001c801c00d0185076500c0c84014103e8009114009900e4a0500070600c0c000c0c011629000c0c0580003001024940741c543c5449900b020010980580741e65255000800900184066402418040c3d1025106c0c41d086042c9829146d0094182042048555045809060000603641c004100782c800080307880c0300b00b5540702544190217015095901c14941c0004195110120507000b100c21a41405102d402c9a0141c3d0450300c0c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 719224748 1250 719223498 719223509
    0xc040608061b1806071202010c05070c09020a0219030507050d050306100806060c0714091e01060c03120f021804021602041a120a030915080106201e01050907 69
    0x100c8128030361030100101e020f0806101d0590740d0b030342007660f000c000404a40c880c00d170171519003c040207140c2d29540c081c4aa10001592030030030a00d0000e40796149950920030b80148a0300c55404220680c00c1d40c4200f000c0d114041c000c40d1010510152800c010f0295040307884115010f200f03224451044038850800c2d280500405070a800c824240740100f511a414002d2015402c5002400111251a401c02c0032800619000240c0114507100b0010300c8002e0307000411954903403101100c2c0d8a001c482821407241141c040f46013480c0322100a18044504100c2e080a5604103810480101c0069106a006010440441c604050b00c40b00c2e032000e01044c2c0c00b58516404694285202e65400360500e5002062076600401101001320440d6000490003102e1500705140c83e403001d4140010560089039503c00351003c100200a984403001d0001d2080c1c60501078042085500c0001c03141500b20313402d03408180701038482074070001d1614040c0b00d0400000800c07405819801d00011444000c00492550240c54 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 719225998 1250 719224748 719224771
    0xb0d0f1202070321030908040906030507080c0f1207050603150108090a05061306062129040f140f010509070e10050d0f0b0f0604050703140f0a020c0f0c04060806 71
    0x5581c4161029608060301c1550217040d00c5040010001344400000c1000e0001d408000515904504102d0714010141d040308505511030040d2030481c0c0d4400c0d40d94040b1500448043c0b4a44900c0300c501418a07199034080340d000300020047c0007812422502d040c1a00748280c2c0c600c22185d0b01c4210b129a85e120b49070010300315800032004184903540802112807600c0c01354001050495440180390b0100383d0100d8924881c24006031040d0400803005248060400505101071400d001030031440e90000024100800142d071031890082044100ca0302d4154980d80203099500061b2040c0e2814003070300b01240d024550340103641000c614201d4004282d1700442030205000119410001401980c0d1090003040e20360315854003407000040c0d402211980700700346440c00d513800ca0810b8001d003c107803000075188030149811f1500030145007a0661280d54401407469039102d154450710040301c020b104d681101d8941e406446404910783c40006008030001c003080c2c60422a5980c0d4400703454a80605803001080071 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 719227248 1250 719225998 719226023
    0x120c081602062509051201020304050c09011401030519090f12030c21021c06140d11011d120a05060f0f0414010f02040611071a070212010b0d0f12020703 67
    0x10f0f4050b59560081c4120b4100000201d4540380028000b05086a02410316034001040004002043c007010381a000306640c00901541810080c042d9106d5919903141055504c000040241010039040d000c000440c807420080480c490404c01030510401000780c640d89000101e15811174803d100b45400140c182e80c40d20f03100d0202d05240c1c144000d1840c84042003940910490710304210f078800b00480c6400f40000058924500180c5101c81401112a90300c981042aaaa00400c0403085040303a02a402d20385182c5202500c9041110482c54007aa41c1d00092a0700c090307510340400052006180d80608101c543c10303514480c06840190007114064410140c10300800d0014100e601001440d2803c8000824503107025185075080741c1055001e10700183c0440c02800c1010801d00c080002b40540749030310000c2c55020f0454080610414200a005066003c165244000298010f40d00300703200402c0c0d0300840940d03040c60b540320b0000f102d0130303980c03a042814800055400042c005003140c0c2c1c41891403499 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 719228498 1250 719227248 719227291
    0x105030309130b120607050d0509010b13020a0c0b16020c03161205070801020307030f0b12031e0c0d020a0308180d0834091a040504020a120c08160206 66
    0x64080c06407140c4c1c1042d25409071382c0c0d01e180d0920180380b02c0c000c203030340d099241d0503e01030007403d440024140c01d2060f4074005002c41d00742c54203284c0c0742910420120140c1c1d65078103904211886c088950000d440e9030204420701c01400421541e000a00a480e8201c840c03440e0784404142d02c44100640035404032510000070804810004110b485240c0a00181c408443c0d032a80168207a9104555000c0000d81d41c00c21181c418000e4810041c1030401621540d12031042280755a949114500c940c1c003040641c00c0d0307049203443c0d00000300c81c02c0303a000505840940c540610041e5445c2143e0508402152a000c0020b0840351468007607013524101d6402062156000c0b501601d07030300720240180722102402e048003600e45e401c0305030f1885640484140002c20009d2541c00074102c80381604040d1058040103e0740f0250002c9409480580b6070407900181d0782d0044400c1501d80041c0356600340d0600303042000781c800c40b98105e91358910a990461800c070844005440032138455104450a51441c4080500c095a = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 719229748 1250 719228498 719228501
    0x10030203090a1e05010507032c120d1d010603171c02030403050909090d031b120e0c1302031f12030e03011d0709060b04050109030611160b0708010503030913 69
    0x42054002c20b500f0a0211980c03640380c00d44004544282c04640c0b00c0800d0244010206d005075070800e0b204801911b00b6080703040d059207a40403000ca0380e0b18a0008504075188c90740c3c592061804510031030303c58400c42d0240c2c2c900c90107848103200546180910300b04145003442c40c8404c480c1d038541c80421860140c88418807840003504094410341c1000414054105951181015180503e0a680040c50350b9911044014151000001d004074408116a03241011641224404041100278132020403100342c48240145410054204e80c0d60011544e11200d50111403903000790300482e111514120a102c0c11660296820603510030007c02c07508511140b00840c3c4101d80344999114010008102000c0d82c5a20b8107008080c2c2d4610801a00658001c00540100f8814200203000c8049114186441c0100291040b07185210180c081d0341ca44504821040340d40c0122220007401c1c01e107040000d44a400c0c144498a000c035120f201168404001241c60300e400826115581d00052120100e800424074220 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 719230998 1250 719229748 719229773
    0x61e0c140d0f180b06010504080a110d0c060c15020a0806120703021017090705060a050a031506090608063015042907140f090d0b0610030203090a 64
    0x50795510200d0382018480b40c0074071103002100030350003061107040f41410102401c002e403070305050160400040101d080301041c0307650050341085485004034a83c0010407000080c03100b008104000700e01c800b180150b004040294480d000700500d940304140d1410500403072041058190219610800103411441d05c90704c1c1601164500040d6800340ea03581e03020800880d52801d4400c00300b0066004403807103414040402d50b0088003980200b00e0540380ca0082419440340450001c1001030004185000ca402070300712121002c1d211211a01c0241d0b82c140007804092a406550005000400491301d00e150050701c0021005000340c22490804c0010148108003034605007100c05c6005e041c24188113a40c0d100d00c0a4410b5000320a951008152210f8060b1110b00b0555007c004124100c180502c065100c25035070700141215101d00e90b02d41007009442d00c80c1c000c032042680d000003140461420401032802e201d024180549600791200a200425010390201f01c504130076607070042c076000010a00f10318854 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 719232248 1250 719230998 719231017
    0xe011203050c010f06051201060b0306010e1801031b080d0212090a050616020324070e0424090c020304140424120507450207061e0c14 59
    0x41e032520110788000741c25201c540b6a841151a501c0c6401c10660a000c6512840c000e1404020001c003800d0461484243c003014041c0c41c10407d00095041654036450032400e521104090003041c01d40e500d10b0312049090504403801c603c03040590380081c2c2a1000030381a08074504a4000e003080341c804a5110101d0340100c24820f030b000d06600e80000e02611124000c02e070101000200301c2c0c14001c140141840e192200c406018203904000e010040f103144c4002003600b14036580780c60083c0650f08800a405421005841000d09002c2170100c5800320080001d5021507040a20600080d0b16080c420b0381c49010f03510980b0303901c1c0c18201a0f1682840c1c00d52114110070503054000800350010000d4000032119074001000400d1450b81754014441e0800000c80200a03204403130111411843c004288082d1400c46460b0340b100c0b6000c64036440802d0f000d03100032007011031003c54842d086420504060400400103080800440d003c0100429043c010380492800c0c5031a8143c1c410803038075221070355911100c5203 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 719233498 1250 719232248 719232257
    0x705040b0a080a0c0f021b0a031a0402120712020607060f050403021006050603010b0f0a0c0b0910180b0408030a0603021e2e0507050a06052503060e011203 68
    0x20801910310303800340100048942d1115654509001d0010450762003403880340a00002441034101294001140c000840303485c1c0b0012200075450020540200381604020014070624001c1c6840440488016200e50f00131291441c28081e03072201141c1341d4000b402440409101109804054100390000b0300c1e80728482d1400055038406200b44404070b1344295400c500503041070190081115031030113124040c280803035119246501d0008100d941d072040d0107031000100790208420350018090310300c0140e0642c0020480030070f440d11031075454942c1510a203d800300e42c50030110055428880c520b600c1c1781640700c1660038070750303d4689942415420040508814a42314100070005880d400314410f0030816890004c03070600c411808000c40f229800001065800e2880c11960031b50011406c003500842903403c162b560381d0080c0c00c00740d0600b5130141015218905000600440300044100720f02d10403c0b0900f0303080300f60410302048065402c0382c4140c03c0519510401808071664508076845140c6c441cac2023 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 719234748 1250 719233498 719233507
    0x1005010c05150f0117010b1c03020316081306110c010c1b0b070b070e13050901090602120403080919020f01092d050111070b0d02040302090103060e01110304030e090705 74
    0xd0740b00d4224001c80d1040c0421410f0b030010000b651540c44000381c0d00d48840003d008070b140300300100b10005d544a00201e0303034030682c41d00c000902d402441200d200500c25540c4000000c184d051203441039000c01c103c2d5821888088000508520491820400351514405408003814401c011110041903402c1900c11452100b0000c00c18250b03406454002c0c0601116103840b5192410301c0742224200400d4401400790103201390710300d0360305e000d000c481c042c110280005498a608040c14010401240700070f000510015800703001304458950b26129a1003503442e030010340daa18007401c0e00d501e00034480440e034007a04201d8a00503d032804c04900148010303d484004e4a5442da6a4400b03403189040f4410303000710080c40031400f03140204a000c045c01c030030b0a00c12650308800e03008a5a6003214401d0074041c0d600032441801c6292a50122002140c004040c180156100d081c071b01c0080094101c0760790298a00994040c1038070060007580c1c032a5415440d080d9a040800c401d0086d842c00090401d41005000c00 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 719235998 1250 719234748 719234773
    0x4020c0d0c03021e0d0f09360b091602030f18090c0405030d050c0304050a08160608060a1815170609070305250e0c0d141005010c05 58
    0x100c0105281160746200e51000c5900b00a4240301c0d1544d00d003412513401d11880c1c1d1000c00c0008003540601e100e0320300402c101e450020100c41184040c1c10803260140e9102c0c1d01e40c00401400c5001740913420302c00d05403405003c0c900604046410301200d89400424400002c0c0030740001d4803030812300707800300c0c01034918003a01c101051740c00d580200810600050703241814034850a02e4042e40c0c2d403280480041a19190401000030360751450400700c102000000143d803238080c1004e20544d00100f00180c08581d0740c0d0b86580513907032214800c681c41e100010300e8400005147d4031583c0f541d409005d0141c13480640c00d04064403902551140354150581984811440d85841e040c40d81100007403654105880140a0303822506080110207000103c036a442108148045075010070420070641600c29680741c0417a960008009400036940418000c0900b07038104010308011070024940648080f42c00c100e4a00540030404a48a0075250307030701000c942c11020701c1300c0e50181100a441c14007460840300e1445426 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 719237248 1250 719235998 719236003
    0xc0c0e0105090402012a0c1e0b18010c0b0a1e02030403050403030806180103110414040812060a030f030806100c03020c0402180306040812130b07050a110105100f0f06050f070204020c 80
    0x804104c074500c42440c1f04000c0148291807014005410200e941d4010345443e000c00940e0003009648150344201d07030700d0b000d0168014444d01e0440c5601c504000118a8001c425000130000061446504c4c2102c12038084a4070180c401c4a2041e0380c90380380c00d81014296102115031040c000c1c205904492500301056111807107009181c000c503c01e94608000080031010301003510641a24880389000041c04e000c0024699800d890001c81064980c054540ea03203030015444101c150302c050880004a034600c0d050661204451380b00b410140c460090b48600008100c491014882010300140c00196080c481c520f0190005c2c4609a401c018416030764015000090403c50280c0d012122010005401408190080c0600b540b008903d00400082c4001c4c0e01c0380d85900c07000520920801c6170002d000c1c440b1f2070288803d180020640310003001149040c0c910308202490500450941d100812400500310800b45100c0040d07034942e56485041040404506100350080081283e00c55000e11003940014002c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 719238498 1250 719237248 719237327
    0xb070507050114041818021c02010e180417040b0408030310060c0b01141c05010b0f030102030c04180207021215090114011806030b070c0c0e010509040201 68
    0xa800600603036490040090030094614022502000c000c0c04104650780000407100c04800c107103040030910069541c0038031140f510040000390300c80c103d02c05c0d1041c4100078a4004480318400c0e280c584071426080108a4030b8050069001c2c0280064400540046c0541d03220110041e1170402042c10140c46406400d00c5402036003102049500110821004041c640d058800031700e41d03405c12020500e019201c81413181030500504101c00c18191244459031210304400d10a900001a180110711341454100e01804040840d40d21a8502400c544450700d018400c0340d0042c4420203032945003d181540261603501e100307140b00312141c3d0034801880582c481e01c082c0b0a902c0c211074042d00007085100c41118a80c1e6026000050682c50003a480341010500700c0341c50f05542c1c580340c0d04c0c2c0c0407107604a14000034020070f40004000340000c3c0d0031301c114207810001c0b500d1a07078410b07014490a607803031307180002500000f481056132009545010801550003524020052442c080c1c4c5a52400c03403004441842210 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 719239748 1250 719238498 719238503
    0xf062b0c050630040503090d030509061603030b122e1d0f0c090a0504151514060306030a290106120b09040c0512030d050a050f06031903180b07 63
    0x1c081c6407404030040c00324040240f68102004080c0c2001e031981030b075034068003900c1c030702034408007042d841414007902c01c2c1d0b00034890003408250359a2400d001240d0311800404114042401c145481a252604051000140c4021002049640070500c520585103075802001076070200455003100c071032940c40c00f44902490403160001c0c10441c1c5840440d24015680c1d44003c0075030081e0008403070b00c0d9500700a85412000c0044045400c0d212414000c1d09176206a4100c030345c80d860141c58030010b4030190308400c100c1c1c2e20040550318803000c180600c64603201c21100182d05030000c803840310005031416500181d1400070640c550322150b55041d0078200301c50a8000b030f00403c1c0610502e600004980c02012408801515200b0890400340d88500e0030f0103150060314400d800c4040319400300303141001510a03140e5003990501c218242140b5510003003005403004421110070800168281c200005d038080760b10404000701c0000d10707880e00c00b11007480000c0241600001110700c000384101000c0c01604440c1e0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 719240998 1250 719239748 719239777
    0x62906090a1a0a18060801030b0709091404060501140306040212010e07171006061b02040e071202090603010c0215070e280f15050705070b0f030f062b0c0506 69
    0x8150701c8002d030001301c40708003107810380e002c0c06001e009042d4481c2e01941102d1b0b000000103070f40e4540e10025a00d603d440d40003145031a2402c402000060303400032280340600d019000401050362100072440414003101c246c03d40581c0100045401400e0010b180407000400d100005040b060180b411030420300f00d503021024603500c3d0240740e0b113044803d0006c0c41c80d2490a800400c403a52400300c1c081d050013141d40f002d445604240c5200c000f0345d103e43d00f051402c110940f05948003942c0301c0c1c8a120300d00a4036502680070b0030503c2c00217040c60a0503c03032401c8001244d0000c003103144005100342c424090040090003000003050340895181c6969000188105480b984688512864250380341c015066070b00c8000901e200201c01c0110a4504040341c0d400c0c0c2c15490641d03a5001136041c030702d103441c0741a400310f070350401e002648204e94840b010280d4082c00e4590000c140503110402044074811440c600b0080b00d80d0300001018102e81e8041c010b042c0c0750b1096007442034459132800080c0c2250040c080c902d0019 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 719242248 1250 719240998 719241007
    0x4050c0c07050904030c02015004082a0306100e15100f020102040f1415040b090111190503030702010c0827030f0a020a062906090a1a 59
    0x1880c140040c001800050b0764000440c0340c91388004000c40340d050720190600003806105440f2140036110403064030880700c0100103c5152483e030420710307846049001c1ca400259218803001111070310484080360014401000021408d403c01e9030200609511481a956000c4c8480a5500c0c24000107101da100a00001d025502c5c1c50710a0040312001000c960000035403160384020ba40d42e41da000681580c0310302d1b00103400d2140520690082c030a5400c181c0c4842800d43c40010207100d04143e000010301d0035200741e5100000501c050103240514000c01c50410018002200154071480c99601c00ea001c072030403940945400080202d00740c9900105039003a800c000704001078aa024010f03051692110f14100e48d42d80341c4141c41509090507030301d191228500401c1072904455007082524680c0c102c040034140c1e90f01c2c3c800390180d902c840180003181e4440c2001203809581c800c4000744182a214203001c602680380d04001c12107030780e0011603201e41c0640001808522030000191401c14000c000c04480c0d601e = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 719243498 1250 719242248 719242267
    0x30f13052505010519080703140f06180c180a0306230903040503100902060c06130b01060806031c030e010c03140907060210051b07061e151205010b04050c 68
    0x108000b50000d60502504000711405c0d540c25920510b960401c42c0340c50807213070319007070300c08c030041c00394418010b14429641e0b09008482c444000214020304080311071030303148212054203d030007210880d002c82e03090310280240c07070701c0d20380365000c401c4036400c01402d8100c2c190301c86d5a45011260800c040b07100a069620004003402c80981800d1740115000c4011030030b20f0710341800656078030780c00404118266252142841191a8002036407002d40440c41500c0c5d0900e840c01e007506071000030342c400342c1e07030b010105000240303060058401030702880f0b0103405070880106401c04504a050b552484070101680c81e800818101401c1c0710364103d030650303a6808540255000c0c15240917181c0502900038a0b081b00b10200704260300003074403210902c1902e801258594441d00c0c6980f003000610056920031200042c08001c00c0003544c02040000c01900008d042c221400411104540402801c481ea01014407000d02c060200c000705401030b144030340004110307404180c002c5000e4413020795038400f0608010524000 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 719244604 1106 719243498 719243563
    0xb0d020f06040f080f06070e1011150c090a09050705271e010305161407150c170a09023a080901090b0708030f1305 51
    0x10381c0c4d507101d551181e01038a034080281c0142400a0110360041d240b900c40c0b8540a00000e9001c1e04000c03096402100340c04074548640321f000b20200310000e2411740d0747c3c425049842c04d03a489840020501100c016503812900c9410b06010402c04802e82c0310701550b180d5401840c4108401200c10002030700f075200a001c46821219032102108a644041c0724107400345003c0c1c2c2c0c100225910b86042d008a141d4208030326000440c0c030070301d40b05159511409014010b00a00340d003107403903001d0740e0020100e594012906001c2004002c03083c0251039a10b100b254807a2165201f405620066400590342e02c001222440281c01503054200304a44c9400c119514040c440c82c2c00f4403812801c1c2003603d01070f0032441215002035415a404035074041d031030040d550303040d41c011b80c1d207810b584071010980d4282c2401806071006c3c0d52440c1310140407503410030091181c0040c00c5450090810b008a403c0e1 = true := by decide +kernel

theorem cover : BRFrame.Cov 719064748 719244604 := by
  have h0 := BRFrame.cov_init 719064748
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719064748 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719064748 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719064748 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719064748 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719064748 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719064748 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719064748 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719064748 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719064748 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719064748 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719064748 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719064748 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719064748 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719064748 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719064748 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719064748 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719064748 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719064748 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719064748 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719064748 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719064748 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719064748 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719064748 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719064748 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719064748 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719064748 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719064748 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719064748 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719064748 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719064748 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719064748 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719064748 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719064748 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719064748 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719064748 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719064748 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719064748 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719064748 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719064748 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719064748 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719064748 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719064748 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719064748 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719064748 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719064748 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719064748 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719064748 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719064748 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719064748 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719064748 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719064748 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719064748 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719064748 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719064748 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719064748 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719064748 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719064748 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719064748 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719064748 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719064748 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719064748 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719064748 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719064748 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719064748 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719064748 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719064748 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719064748 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719064748 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719064748 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719064748 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719064748 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719064748 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719064748 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719064748 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719064748 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719064748 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719064748 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719064748 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719064748 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719064748 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719064748 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719064748 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719064748 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719064748 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719064748 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719064748 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719064748 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719064748 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719064748 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719064748 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719064748 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719064748 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719064748 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719064748 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719064748 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719064748 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719064748 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719064748 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719064748 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719064748 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719064748 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719064748 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719064748 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719064748 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719064748 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719064748 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719064748 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719064748 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719064748 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719064748 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719064748 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719064748 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719064748 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719064748 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719064748 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719064748 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719064748 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719064748 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719064748 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719064748 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719064748 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719064748 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719064748 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719064748 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719064748 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719064748 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719064748 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719064748 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719064748 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719064748 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719064748 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719064748 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719064748 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719064748 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719064748 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719064748 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719064748 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719064748 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719064748 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719064748 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719064748 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719064748 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719064748 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719064748 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 719064748 ≤ n) (h2 : n < 719244604) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
