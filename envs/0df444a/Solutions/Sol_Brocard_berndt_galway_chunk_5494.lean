-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5494
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T16:02:23.716968+00:00
-- url     : https://prove2.me/submissions/2fa11935-7251-42ba-bf47-6acdadeb0496

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 987949640 ≤ n < 988129496 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 987950890 1250 987949640 987949709
    0xd060509061006050a051e0f0d180b0a15050402131a0a0806150903030a05030402040e0a051e03120c1b011a0618040f0f060e01030b1609 60
    0x2600c1e4103640780c41280c0b160b56020302c1a0000100d0810140e0a282c3c0f044016140010b07802e1a2440e080350341d101c00c085103400c54402c2c0440e240000407501810170b41849011000544040c507180c40c00001d45601c10b038a030006005080441d2251000b5081c00c0d10740305108044c283c0207004549400f40543c20301106a0740740070b4031941c2e06102c0d0450011000f060b0607117148036060f0b40c400300a0350f220024040442011015180942014030108085503020310160a4984507607550355103074a400c1c010041500e5507103164100e140c00440140d008280007003600c011094880e4074122030038059480d20342c918840c401030301c1c0c440c3c45c219003884518003007440103282070210440c0704043d00800b20141c9003241d4aa281007528118460018445070800c540a090400e6010b01045885480840450240e5024982d5650082d58400840785410302a1041d04050040340c2005003040d03065586218801d00050200451842d5681a5105132880782140101425006440070200c10007030749002006c0c0c052001 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 987952140 1250 987950890 987950893
    0x40312181202010b240a03020a0516030203070b010b130b030603190b01030512030c030106121803030902130e06180f1618052e12140d03022a0703020d060509 69
    0x78105c07580b0314a080128840110304400504c0c02d00c003072806400a511400884003030000038000c003e007080b5185060704100740a0380203160385144529007071010400503005840d2100040c0300d08002c08011304034140039150a000407607503e845810000303192010001030040c3c8031442980d8a403c01c01c0142245040ba03200340b089603448251802c9400c1d02d4001160100d000e04404c1c801000500c0c495041c1040c8407001d0640040c0b01042843c0b502c1d05041100010b801003070b1540701000850609210072113103070301c2d8241d0801c1000c140e8003900e03880d803c000d407803980b0f0710f920181d480003401d1040c00304201100404085600350b4007503207000989126107124058500d2812010328420804500910f4482c01001c61240e01058803100d56484401c41036004250600c04110085203505500140c100b0850259445600080e6441440f600e0304118031404000c0500610120031400144c00c440602c0307100456401c2c03029105500310740d00e8108103600c003940c48045004004140306640c2d01c01802a5940d40 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 987953390 1250 987952140 987952159
    0x110d02040914250309023601081b01051e070309090c080f0c0703031118040b0f0d03080a200702031501060207150512180d08040312181202010b 63
    0x40c40306201c2c1d51901180040d40140e1003c0c1000d40b0303c641c2c80069400e1000f854811028040d0515154101d40300c0d01044103e18140303842210ba01041d0010350040c420040141076140001803045101d021074a40c032414028046507138042650401440c440d0280c07201c224070789440507070800400704000740c46503412261405240c2e0700382d076210300c82503803088074060b02c9400702d52961814176800d680602010350825542c0c52075107041e825440001e0003000948009208400450403c100c101c420690f4124030985610101507115200d259000346d1158060800600c150b0700c3c49114806000d441031403219804078110010b070003104400140207a20700a034204e81c180d41c131155074000942c0081c014580542e12480c000c01c0201200d441d41561444c1d60314002d400c05000d8404911004003d0383e0311600d00080342c0d440300d40c45004020340185842c180c90900c01c4c0d403c0c07546004e0044410640c1704103055881d1f44190302c174218081036541c19075900014000b102c1c0034041009008084400395540302c1c04014 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 987954640 1250 987953390 987953401
    0x10203010315020c03030606090f0907080709061107060806011202030c031b03060906060313050a050d26071b0506180c040b01270f080106060806010302040315110d02040914 76
    0xc0c0300361000d20051344001d51640c0c9a042c00c102d81a048420ba041d44202000343c800055104e8052990003002103031100021820086c42c058880034041d000704c000c2020001c4400008103000800a00300c1e151418003030120b8480304012568411030f5003040300075a00000a00c4001030703104008500c110001c0f02103c000c0e85221042c0d240500c4159542a408889200450110300d0010000d50700040b0704103005208800650382e6034100034201d2015161608250001503089030001e10340c2d804a600005031162011194400202e60600034188808116002007203082558082c2001d100190b00001190240e180c14182100c412441e5000c0c3e041a00074080d81c030f6481c3c00c050040780b0100f14161191100085000d10740c900e070b00a0b0681d48001180750300383c0001c01016900e08100500713006800803031401d0424801401c8120098401c0d1304151040000700049485000e80d410070303a4090001198101040040ca00315002d90b52000032003a00c00039000400042980c0404101803902000a0f01035030345 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 987955890 1250 987954640 987954683
    0x5160e100b07050c0f130603050c130216030e2d01020c0a08070308030c0714100506090708130c150203040e060d02012a05060a1d0d050f16140102030103 67
    0x40c00300003000303075101c0080c0c01035a180020401c917050b07030040c00003118120b940c140d540039224641e00603102c82d00300920050b541d0034403d50318418105500340551410f0445400d42e083c02c00401800342c100000c20b44500e205944181c0140da090b10303030002d20f00e085d00f045000132054110040d003590152240384210041c17810002440c0b01240c2282001d0a4401c3c6141c88080f4036038001480d0103400d8104000c0c035000200229010001950711000804203a1100d4a0701400c8542c00b44c1400c1c40380b5040310800200550001e001c80c0e00054901c141c3c500b694661500707004413411604130000c0c034014078801211803503000024004076440003c0c0403080707895103000d1004401c1c00000223800201800c81c2040d00002d49000600e01c640c112200c00170b0b070000c07a214941010400c2c2c030710440264036500380078003428842a8010184440d0400391142d1140740b90080c0462180720407401d02e06c4004100b4100d0042200c0c60108080d030000300324441c880c202c0c0c081c24001d62090000712284c034035020180200e00708 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 987957140 1250 987955890 987955897
    0xd0605130618020a110f07260307150b090c191e030c0c06020304081c0e0a0b0a0605031009050f030a2709141504020c030d050405160e100b 61
    0x8189248081c502c211551202a40c00983e003035040c010750080c15808080c0c10029150b110394a5030143c52074505088010b40e1514814444030f0400018160f002c4e50080c0200032222490392008140300b0a03c00c4003400400380c200c0c0b1400701d500c0700c01602081110300c1ca80303005258044011107030303007070503180400146c0340340058001c0c4000c0d043d0302c1148002001d00962000700d182c481d909007000c01d0074042e0798401c241d9108890031034010102162a102e2005190300405219140800070700c10404001c0f41d150303071a650708501070600128000410001000f551010028041c05070a4400c800d5510604002408200100311224031811442400c5e808010095940c000030350b5842610b282c000c070301280703081c00c1000c1154100b0b003a0720900151003940e1380b1800007885d0704544e51880c586085854010140121706410740600d004216504040d0000301c126407040744030303400001d41d548440c20414035000300c81c0038460300740c0e0702401c0201d8180000404036118800090526007005d464003c002501e01 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 987958390 1250 987957140 987957149
    0xc032d020d080f030703020c1c0807031e02071a07090605030c03100f0314010e030310090504140307141c0503010b2d0909010909020d1e06020d06051306 67
    0x45081000514044045118003030041551500b00303101050303010728590003581d0480210b5400038551054480500038501d00b080c3c81400343c03604505011020300390010041101c010150380e00e01d101082030355014a1074101812043c21502c58500385002221020324580b181d04049900d0000b0714080e20581705036041d01e580799100760464032030300c20b444550b400281481c003001c0e0070382201184100440921030021401081d107200d004481c0d030340320750849a5500d000a00d507002002003180b4000c041c002d0400b194000c002c0042d00e50b40c4e43c1040850540703040e174008442d00002603400b040c00012954225403059010a54a0104851014906150744c02c2282c10210704244010016440c40e10090000c440c54998500c075484504c4002d002808030b04600d00302400d0000c43c10b85103505084011a004d01440c410422001c00e80d0b0f000034100c02e4103c1e90003800200e40078010081c50600a554468580d8030050640d114000111508050a071901a10340207500d032141d0403080954078003600c0100e8 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 987959640 1250 987958390 987958463
    0xe0601050d03200d082514071505040c0503060a0b0915031c1d030102180f01050d090b0103021e18100302150a1b050318040e0a0c03 58
    0x840c0ea550161001d072046000c0d00c0e00304103500c8002c483c8081c240600682c0ba1802ea0b198050703071a081d03500505c050340601c090b8510402d005403019100707420140540030310080140c10b0f506c030b25492410045406030051000c5034a400c1600340310420103400034141c1690303422000c3d14104d9580c14215400c0f00c034080000b580c8001040f0101e82d6000024840e24040d0b40042d060f00c0c82d94049600403040000010910750000b01061201250013141008103200701108900075850302d500c010304003007100d83c104000c0c0e04c00d01b4081d60840c65030707000e03400315001103101010a000091035070501c000348007400d02c0241d0080030480c541d1185551509420490740100410340740b000743c045c0621341140c0b44018000039141e681c1420100169503030030600c4c081103070f00d56400c507a5042d00703500003480e809409414400c1888060b114000050000c416a140001c05420601c011039402002401502420700003849038006d0b125010280040c540064003524010003c0c03010901c035a034011400c560320b06190b00350b003 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 987960890 1250 987959640 987959659
    0xc010c05060a02030c07081215011b080f040f0602030703020105060603011d09030f161a0130080d1a0109120b0a020c06090a1103120d020715020a03020403060e060105 73
    0x205071594044e54000380c00c05802820b080035a42c8507200d41d4403c0c0d80c0c4400107500141040310031104400602c80742e070b00a00e0000c101981c0080d140b0310191544800608601000c00c08128450300801542c008001d1840700e1107003e81e907510040c1d01c0740e0003c1d4042d001035003030500043c160300781081100e0480311840780d2070300c0704140b801c1859100d08001e09064001d01080122803128150035014001d0321282540c07180e81e4021074604060038008003041c25000342d0090004001405886e01c90280c1d0304541b12100c0c04201c210440c0c0c0940c481032141c0104004000700f13000750902d183d03510603410020440503003e15066414015a000122031003036812160182c80c6010000301000ca0300d80c1c204000b25809800c03c071042c0c101506166045903400c001da80451441414001e120041c011864415405401f6405103001210481c0c810040c10484860b0001102c204100c02c0820360040340001c010308540707030184460700a01070350043c8010b41d842030034405109821440070940b94103c0340000c084040 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 987962140 1250 987960890 987960901
    0x5010c060b0d06020f120114090f1e011d07140a050703031806020903060a0218010c0f02030a05030d0f060503070909080c0d021e01140106140c07080f0c010c0506 71
    0x50701512160035000a80c0754840c10001d050b500281c201001d4101034242c80700072000000d103020b03405920002d5204e4401281a07165101c20740529000702e4098000500da0b07642c410003440d882d50b4402242660074296000045030800d401300722007011480d184482060b21204011242c046030040204011801041070302d8460f8007070002040402d1082c100868101c910040b10a0300d81c41c8400c1c1560b5094000881e0050b44c42c081c0f00650344240b08080450801541414040722000c82928040c1403250311100303502400103035451040b01507801002c80340c0d80c20042c0b030410380b07039000f2480c0c3d444010b0418a9401d00602c4900885050b1800135000f4240b039890456100c0180010710400d4603c41420086090440c00034007a191500d040c5400500e69017900d80c140d03101e141142d041408041e40340810f0300024100e175600043c11a03c2034908180401c090240d948114400d0303660000d85482a03440005121f0008101640e2145201007543c07035441845006440518540c4802403503504240b00180 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 987963390 1250 987962140 987962153
    0x30c081005090a0e03160302070e150609120f0c04050106111b011e09030308100509180313030609020f03150115090905040501050a0e0102190c020409020418150605010c 74
    0x96000c584948045046070104e840f1504652050344d400c140486508102010f1640411005d001810294028140707407030441003209420b0740c0c009030305110701c1e800104105943d1b1000e20742c403007403c2d002c01910a40814041880d55a4240d01540c038040d03820800005401401085164040ca40510243c00b0704840c009000401c000302d518028103000410a02d68140c01c0003e40c0c0081c0000141c440407011411410003030000e010040007414901d0545000380515180c8010080d0440d090b040c60010348403400010302d00314040d0b80c04202001c00a40707c00010300c0a03980085101c507000f0703145e88040c0726188080c55244c185540c024100c0140c8a0010840d482c0b0a1800302102440351410580403034072401e038481610700586d015074040c0c0d114000e1141c1600395109408031011003200861030b1007180307000441040d04401101e001e00c4220096074056407110b030000315101c5c1d8010410092000c04d1041c0c02000300040c0c40944685082407656100b00700c50f80f0488050b5041616007000c852039642da2007 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 987964640 1250 987963390 987963409
    0xc093102030405011404200603041709030c04022205040228020a061506110a020f040b06070209040605180f060f0403110d02011a09010b070b06120616030c081005 71
    0x8403804c3d036841030b20b494a00410000c3c1405244100118002d4800c00d085096440841100e00d13442984100207000010381000f10318000c0280c2e50010586a4807024002405c00441c45c01d03040c0c00070700010712030b802620a071042c00c10070f0381803800308403c20352143c051008030300508915407400e080600f0719900d448240f844815454980744100e070807914060380c5200603200310b2940481082b20b5040c00f880020740000150005072542002081c0f681085c0e000902003030010400035018503561008001151036010480e0f40440d0090f0150b40305041c9450204000c090480b00b0303040c955940307101d9520700103012070344212102d540d4008020b10b442d04c0342039110183c0003500403428000aa0f4401c0e41080051026094000564000050001c1e85081c112111900d0fa070007548a240c90800520501c101c00c0b054030308058101c2890246541d0f0040400c2070610703040f10010719407141108200b880c0c107501031010070001032071380c0901c203228003074006540c4a242602e003541400e4456006000d50300f080b50300b0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 987965890 1250 987964640 987964643
    0xb1c091104091509030507060605011e1b050f0303060901050d0c090f140907081608072d0905190603030c1226090f0606060415030f02030c0931020304 66
    0x2540a58483c07400d0010884540c0340045020580114515083c03140500c0741500500b400c0c06c00841e03800e4a510180d6a44031280d000304113011005002c1100c1e081d042c0741c0d0148040d4014115922420488501e940e00d82084545030311901c0200004981d5040551018104651058410401604261a0101911754180c00501036640c1e4045072400034103e251441c000d041c0e08014103003150410340041c0c20013a83d1880310074840d241c0780b000c20200b400000c000080760580e010103011500300b06a1009100080402980781845070b46010030050b01035845a07000d00807264200c0800c0c03102040c14415510f240c40050080f4151200c1da1005c00c10250240b44204003a180c00041a41141142158202080391a841180d416420000025020807403091402d80f48001403400c1e02e0484001041403140d809901c207505401c6417840b00d81030090300502054125140c0564403464980e03203040c26504406549481500040c007140c5044141515020b128007104503000c040f00020355070b00000c1e5002410 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 987967140 1250 987965890 987965903
    0xe01051806070c26010b0a05041e05010608070305061507080a110304150e0f1f1806050702180609011a09040914060a0c05040501030c110105010b1c09110409 69
    0x4000251405000c0c07001d0550300a0000d03060103044c1c2d072614100030004203903445030b161010b465410342d42c4600701400c40701c080710080307600941000c8800880d0109903941c000749081070300114103140c00c14a100d1194606940030001076444c48104048544001c41582180000700300000c003092070400104813110080c1441e40b101e07401250401e01e103038801e6124091004522001040d80c560140c1d08104100049075520380038030081d0002035284002c040c002d450701d00c41d10005507666006407804c40046150001c1c3c1c00c1040d9449a0180503a800940300300d119505d60b41c0041c40d5007a240c9202400380328050681a500e0382880b014580c60307025040b00f542c103c4802e2208220075070300ca014095016128031481c2c43c4080e10f0700c11080ca440303006441d0ba600303d420121030b40d0950b47d10109440c1280d10034a4041101e400d002e00a8032000d00f09502580194248000810380340300c0d030300040591000916010140701c023000302e402c0c01c45000800c01043e80d900003043c0007043c5442e4111050b80341c040d6a = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 987968390 1250 987967140 987967147
    0xa05030115051303140d09051f2c09090102121b070b0901090605011505070303091505070917010605011b03020c0303070b040b060f030a0204150f0f090c0e01051806 72
    0x3502200100f80f03680c8100d400115040d00e11001000a100700202d07401142440e685190509001507038a0141800031003c0c101451107103041da502c642c0072001124140b00007c00203102050300c21000b841b0781802c0e140035425420204152400504c02c485405a038010300f6031580d21854101000001201140c2c89102030a0100102281038076103214000c0b0403a1000140d65202c82c0341c91819103130141c0c0411451200e0849c0d14030550b41120480321650b80c5440c000450320110324182064011040790601d0141ca41020000341c0d036000f010308419140a0f00c040c00d01d0b000d462200314281d9640c3d0041a000900311280045001d00886002410714840e005642d94401d096011929507000480c0076141a07101500f400301340441c41d5451303604030740300341d81d0280100c031a140801d0b522035100b80d00a01613a69400000350003c81c2c1058400a40100351400b0200b959500410410000c103001c2d031400c5030300e00a0820080341c005c0481c4a544041a180c1a041401c200c80300789d110711524151035007051041 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 987969640 1250 987968390 987968407
    0xe150703031a040c021b03010917210c0a02100b0307050f150309072903010b07050c09190f05130f050c10050d0e1b0607170c060f09030a0503011505 65
    0x138000e00130b2101145e0b00a011a03030010b0000c070450b100082c078640c042d034500080280400c0c00c07008800700018030000c400703070f440000f101010076240d440103a08113960994400e100c041503240b40100203c2e030b1182e00700e81c43c5641005082c412181d954110640c590703c0408200910b00308003048010256000780300030402e02d1802001e010a5008a90200f101e80040d1000e05c1042c88510301080b91500000043c20740001107030026170b1900c4103005100c000007001c60610100441040f40d1441a80302500301807080c280440c0e518100855558054003071814003214441c1042e01d8130a1a1149420807441312014007140c483d440500000d250030754590003040e4104903c3d45a0389940e0f200c20309181c0d03c0c1e030340c1d6042071001e190444031101680b00751a00014006030021141c9043c1e03a400d00300456401790307110b5051130120000120144c00c03007441503000c11403a840b00350100e6650300c6640101115041580c880c829030ba128854451030301c000c00d1007480180500741c800048841c40802c03d041280c40d2042c1d4 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 987970890 1250 987969640 987969649
    0x50102070c03050f06070203030f060d0510150905090a0f08041a0703030c030c020c2b08120c1e03130b18011503030e040c0c1403030402010e150703031a 67
    0xd450035144400c0c1414200104041000304030b100740440c070007400142c00d100c074009440344800b800ca140f40755030b08400700d08165201405400d10a070701100b110281141c04003ea00034107405550320311540c10b110000035800c0b505000e1144101c05480c041e22612030243d890882c1d20003803d00c184c80b000ca05000124240e03070440c00c0382400100c02038a0507100ca105280c0101510840d0403014101410400800c00050300003034000c1103000f0444803000c40c0106032200e40180034134220307400003c45451011105208600e401800341c84464081041c4a554048584040c0d10517a030b1522264201c48106a085003000f4000e19000b410800c0c103034240307110507103503486c0c0a0070a07203100825450b82145207003051002d2152040101c0107a0b42800c00310319503200940489011100c04e4003651320340a0720903c6610921409074203507030020a24110070010041503540b030b0403c6500b207000c1003012200280324a0500e40044416a820402d5803034000203036012400b40996031010321003900c009a8100c0c46075079 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 987972140 1250 987970890 987970897
    0x2090d080a03092306060406030f0210120204060801031b030308130501060b0a020c1306060e0d0c05030a08040f12110f030f0d0f02010b1002031b1c03051e01050f100c050102 76
    0x1000f0000c3c0c940b00901e0300c80c3d41042030180865105a00d01941000012400410ac28107180c044841181c0e01803407010941d022840600210103d620019000c6455a0130108444c142d9000b140900e4000e94544076000141c0d10a000c0600032500c08000504040740c00100e100d86c40384510000300d1560780d6908070000b00e030406040d01001d60031817240c1e2504c5060032100c1d0090300c0c85400c2c081c083e0524020001d04001c0d46294520302034a941c05000c000d0041c0000d10b40001e01000e82103c810118500300110316400c140a03c26070561400c400040503421000345402503a00540c09075409a0f0450030060400c01c0104036581600030411810b41003881880440458403586e11240d42401400e0f80090845124401789803041c17504140c81224568000103945a1441005481e101d010061030080e00d4038081d10340b499030400140420108541e85500010300401645c08260311141d2864444543c5100034000c036500001400e0780c0c240349180c00700c034107503c0742c5131420410124134260303c4245c260307030 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 987973390 1250 987972140 987972173
    0x30a0303020703260a111201080a1b0506030109240605031902070f0303020a020a12030c08070309020f01050a260615070f020d03110105040c170102090d080a0309 71
    0xa602240e008107040d04043e09080e05214039031800c1590f00e443c0e200884d010000b900206140e81d40d410844a40c40e182011104000c011401d036034065a03440c1480c40e0b444910707543c02c43e000e1640c40244100c06402d8290001a5280100810700f1607003450404002000c030880c406d8440d8106c0e041c60003881505004910280c00c00b41d591030b81ea450128100041c810522010f145107500c104140c10100b98209102603e080e818980980d40300c0e01508124680340501d4005005210700030480d8801ea82c066205105805c01e0341c035050041c1c0e540e01000d030201c0708083e402a40203070582d0041c0350300d58890350041008001e54181004683e182c404648448203011448142061b142c0b003d00401d4909a030706e00e072041c0742c0c500c1c1c1c2c1e13440e20301240d48000602c620203030000c0c059410030004000b00f60240641d1650461210300810061405090004048460f44030703030010780d030b10300c43d01088580043c021503110718409000703014201e003d80d9410030164413034050324003010755481071180000d1804840c02d9000d0b = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 987974640 1250 987973390 987973397
    0x90312020a17070b060d0204020405090705090906011103030708040305040b070620130b03090102040b120a0b011814062a12130902090d02090703140108010504030801050904050c030a03 81
    0x620035072a2018200720300703940340d00b805103007406441c00240e201c1d8540d50744040700fa112552903042501c0424017a009030340280764040310f45000c1046030b660000280c070700400125001490340d03d6020064507543c2c6c90b4200300c1ca00e60010800030b4031a90040781d00e10b40144c03003482e11928090b0794403001d1650b074200b20800c17210991a0542a00c0260548005c4118170b002c0000c036910345429000400085441c1d44038030b269070382d000320018880ea1402e50584004050000390556600007441d0003042c5c40318200d420f600c115103040120700095101b0704d40440708030315040c1d48100d00340c100024403006038014071400d64000c0c0c041003021b41c0706207088060501c211102840000201d001040c25080080107040b02101c00320074080015081094213480c3c00311414030400503030b241c000c03e000c0f4540c04111030020350402d42240c14840700b1365241e4420361a48850b486000300701e0340c80d0900107080c0c50050300c02400040200c401848075241c048222a000b40c85801210129800b42011a040020009054011 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 987975890 1250 987974640 987974653
    0x3060d02120f060c090d0f1401020d0b0414090303190e16080709050c04210f05060702010b0114091203071b050a08030c0d030216020301052502070f0e0709031202 71
    0x481d008100550300060650041da040c00c41c43c40c01b0503140000140013500f0090106052014000140c18081060f160100299a02c00c040c2041c14041c000301c42030580550315045500701000100d03003080d4017541040002e0b52a6454180328400404c04c8600524800c55035500180090b003001c210317010050b15040441c80d90145000070031410902c035940036020881c24402017148108069044805849544402a190b807400f02001c00e0b241b21451002081c40030041c00100500c0000650507201e0f41d0543c1c000e000140c044401142c4009040100e982c02201c14440a082441d0080d098541003103d90b007140c3c01c1c0750864607014070748860954928071900300c4120500040c14210680e401614981004510784030481120642d5400560707480c10405034085200c0c0303000f0035104e40d407108540d002030007400903061402c0c03a2002c103446620403030aa20620742ea405000340c0045402e800320744151600b400c407103240280400800340c005010b0400c00041c07010220000d100e54094034501c1100e81d0042a4 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 987977140 1250 987975890 987975913
    0xb090f0102041e1203050702010f030618060503010501060c1703060d050d031a010f210609020a020304080106060306032003030f040602250f050616023c060403030503060d0212 77
    0x3c00c0d0115801000d0703852044501e5401090700300040341c2071b140e03081c070f07018000501802c02140205829049140d4000b052404140741c10751a41000303007a200b04500812169036201c009032103402008000425041c0c0c8101c009070585d40403130145501c040068010114a5000ea4070035003403000401c03103140800d58508801102c800d1a40101c649a5400c0c00c0c80000303400032400207000030340350000000032040301d014280d040c20700c1c5030094801004606019034540d2544030020f500c0e5005801003550562801c1e0b0001000c074840c2c0240812640c200319140540100f0f4540d60440004248003190503100402144188031030010090000300b880343d018008171841085612425055040402e044c02c5003108244010452581c07900100d480c01c075401d55a501680009070340d003d00d152406903020213000b0503d42100d289200210541d42911901c008a002c000040340550045a4840350041400d00080c80024000c4000359000035000701400a81105540003401100070109025502d4211414411 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 987978390 1250 987977140 987977189
    0x2030708040b0610080f07170703090317060d0f05210c06090f060109090c0f30080301060305061207030620091005072409030e09130b090f010204 64
    0x81e0080300c00c9540c404e02111004000340700340c0b070240c50110110805800b195000d4020164405002c0030100410a54600a1006001860103450940100c1c00c1c4c0b01c9070701101c2c02c9209019100c1d6400034103060000070340e91500c20015060000c1164030380b01c0e001e4401c800c850303509098495000c04d62103840c1c0e614040603146090110142c1547c10b2130b41b028940021304140402c141d03040d90110b100018420f245410b0100e0f200780543d104068529201030301248503010061003202100142d0403281c40025001d00d091909200350034003409080080c030040c040203110350429500401c000788213155002c0d0041d0000d041100d00e520454003035656003c00034500310f40706c1d11a044215468203060400e902100400c18030000c1c10706000c100600000c43c0003c1141445a4406242c039803405540804092a05080107101440060340440d446510030406031a0265189209610740d40010403550701d10f5690020460001c0c00c4201140112900546c100e01d09101070401802107100d03003080c2001060408 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 987979640 1250 987978390 987978413
    0x1b0c061b150a150519140103060b0705250e0c032d0702071712030403050c0304080d0215041e0501060504020a0801030b01050402090108040305090a050d0807031205100603110405040203070804 84
    0x450240c451050260009905da802120840b1548030603864140b8044004a005202c2e0b82c21941c0c110f031001ca8036001b4008c0000d1b00a106000d0300e2003401221051b0441c0417550b8000348286101c0f000d030080020001c00700c1c1030196070021110042c101c0e200e41140040c01c0600c03548040352081e450724400300322131150304121a030020b01c60750004422000c01c0d0404c80b85c4500280003000100b01c0000003142c10107206070700b1105054500c1059a1b1625180c401541d00e4003848240d0070014440c030040104c001681c4084c180c0115032213690440b51200c6075190350345103948103105840359547d542c0001016156800184007100b119036401202e58103601d081da50914060f0001402148188098401660800c4845402c5038241c01c1003a281d034078480029001c4107050308815002401c0507605810803802d6005011454440c0d02d80c2e0340400701410404045400494684040c44080c110820106010340c1c0a500c01c54248609140303401d460700c0104040c0e0b4030a41c1d04000146402d030070031007888041c2608 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 987980890 1250 987979640 987979649
    0x40303090501051f050103050c1b0318040b010e0d0f120909050112050c1c0f141c0905060f041d010618081b0414010b1b0c061b150a15 59
    0x21310468580303842c1802c0e01d2081d0740129414195650040760409403c0c80548003040f814030700c0709032806559414542c503904141c6003102c1101202c51003840c503181901890303403a031a060b91030b5400800441c08004441080040907070b520241c82010f24003241c441703124207040d05415100c112356140780c071208004940c0140d1001e402e400314a109a00003070341c003044144400b80704840c8001000322040c2e16182d0070700004001040b40800d4241c807001c100403040280c00c0001c486058a0414503c48085120600086040c8000810219050100c0e103001c0c0082c1117115214800340303040a454501082c0f4401d000b404c0d501c80311001000401105a202080492240f022200700e00014a400c3d00d0a60340c141c01c11416449801c020180c24807038540d540944000101c00440c0041540c3d245840400e40d0f2000c0407540d13030403100c201c148601400000f40072101041c0034283e01c0ca0410350854850b01d018030b0843c0f06003a80220001045200c914084040c02042e17192000a61786211400201030300e48240d11 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 987982140 1250 987980890 987980911
    0x10020601030507262e020702030d0f0e120c101e030203070c12030c090b04080a08031003020316181118010e0a0909060f09050a060207061404030309050105 68
    0x62001900108404003102c00c074002030701107180c03903488403001103103211201c448a1140c41d42056500a081ca00020345c2282c1c00c00207100f035500f148485059102c5d590010390940d000210a40b411313880344075828840c071540c0c81c001100e006540c00140a440a1042142c4194004c2e015105a45444101441e148105080001804c00a003009404026010b00c20505041d40070001480150044c00b8000c000c603842102d00080f42088400a002040c000b081e4000050410703d0200d222280c4034101e40076613040b2001402c0744401d650318000c285c0d0008048c80701a4075200310000050b281040300c000341c2c40c14014048816410503c00c24a11a1114800400d0904060001c1c0011041c1821256200850120b86045034440340c010381da0146940020b5420541c0c040c00001c01503513590000710303154407801c018464000741d4103142e020340c0c5a0180203003213504403801000c002446035000b06400c500c211000b260000c001c10344140301480444065010980302d0b40f0b030300100f050a214041d800a949003 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 987983390 1250 987982140 987982153
    0x24306090c1d04030807230c0d0311040b090f040207080409050705030601080612150a0207140604030923090c0d0e06010f061d0604030305040f0603090201080406020a2c1002 76
    0x1802015250000707800501440303003007404141030620550761041c5007071f00702c0c0d202c040010003003040f41165030140c9105450f40c0200c0c441c40d07031442d11034021307910b18281c1240080c0c285410120340c801b090b481269180c1c3c1c00849000d0760723511501ea5001812402e40604403a03901c462a24040c01c01f41c031401024002001000c10804c00140e80080300103070082019140040b035100001e049030f00d0034541c04000310b4010f14400401240c0b00c45900240b611505c5184184400c14140c50303851b40d1014159401070104003080401d00608400342c07541d440c8540020034007c030a034854404035208a000b9186249a00c40024141b201c0001c03a00850784960340050040c0050f61600d0703a14103064002d8040c180030803800200d020440c054480d1408000040100180e58407540c0380b6000d00158024071880801c0c081e00d2000183d0140240302d80c407082501a181c01d031550380c2d10307560700300207601805200702804610314003010341c41c94031020b50b409071910218640481c010f00f0100004402010f0b403070000c551189 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 987984640 1250 987983390 987983429
    0x17120708061f0f0e031501180e0a111309060516021c0e0102150f1005030a23070512100c050301080a02191809110618040e01061206060f0603024306090c 67
    0x2b102800075070451512042210079200082c110742d480021003181c203040a00c80301c14000d103580308a008001d019600018210741260a82e201d081c03001c0c0051842e0590548039070b000e80540e080e034010f460144140c0b441140c0d01c03181e0801e0944190382c040840301c0c5090401003031103528404440640f4040b4014561621903a4464800b00c85d106214401c994400350300b24501c910402007500608001031200c80e5114031004855079444500d80941c0c2d9060502782c8201d14a4010400c070790581d4000d40280290300c02076000d02210403d1050302c0c248030840d01030300203036910040c1c20610300d50069940107c0d06403450705281e13207500e44844516108441c1044404541a070130201d00308070300025030300891741c5001301c50101d004003501c2d4000340203c00601c614200f0031000b03911070320030b4604607005001749503161a0220202d01810025845180c440c894480200c03001800f0540d070540c41c000a00c6041c000c00e05500c0502c00e5122048274190b4903100703941c04000101c2c89110291290540d00d61605601c03 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 987985890 1250 987984640 987984643
    0x708061614091c0213060305150f060a1403070f0902070312060506091306030204051303090602060135070909020a050405100b0717120708061f0f0e031501180e 70
    0x1100c4030f0304890b92445107484119164004001d00b04151010100221956418956100d0208500c005046801040061508500011002d014500140581d1401424010b2460b084c107001d41140e541072040900c0010b0410521018030007620004401584461003454064180b200d030344010345156003800d1080c48a611a4016650391840441e44c565221303c007011240002e10285d000030b500142464100060340f000003040c540726502c42c0e036440036401ea5442e030032a21040e00b07008071035911040d2200700000040014101c200c00000c81e5600b01001d0703888d80d500e4a481c0d1941d002070207941d2100440000e601c0d0480c13440700100001d0b00d09004514013001c40c035241860741e0149c0254180d0104842c0d003400f0000b0740c10241803040d168401e9955581d2002900d1520003222081c0c00100d110700025040e0074040c804a46400740c055403041420804101600c03a10b9090303e260041264040c541400e698042185500f4201818584050b950415542802400c0c4800d200b803429030800a03010707100c000 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 987987140 1250 987985890 987985909
    0x12011113140a270603050a0b100807050d1403090a03140714060409020a120504500f0303010320030307030e130906021801032d0e070806161409 63
    0xa200000c040381c1003100803503c005041035080540140f18007a0440c0c10041c80340301c0c49014664550350760500c19950f800d2031780da5842c14080c6581000c81e4110541c0018400c100ca0030782407041d901540c0c00c1040240c0414101c1010b948240d135544407410305600030940c2409203201904041842c0000ca100e0017010407241e10551040315207850340014456080c1d4030920344034074105030204d81440281498100400c2c02c14624502c000461400e0030b064164001c582c0300310341720302d000005600301c1c0c1984e10f07518043e43d918050000c0c072038018041c0c12151001c040c030055019520030703010b00d0034641c80c04d84591282a1001951400b0764806c004007404079820849031030300c1c1442202c041400c1c034030f8150120058025a54020b090a0000c0340c0d10340c000c010100203d0400d40280d07410080442d049018070781e00741c620013850019070300c0c40521140c9032246801001300b080020b4111040140d552420500d41032049400341030b002c00e10b24118526550080c440c840350014003402c141410b01c058005480c412 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 987988390 1250 987987140 987987179
    0x7030903020609012304080c01110d031508100e010b030703241409340e0402030a020303070308090f030a140a122d1a12011113140a 58
    0x410105444195038031800658920f20382085c00c01c08440d03207144c070501c001d40050148110a003e9031090400381d52190002c202000002001804400c01020090f0001c04c51445c0961b044e1104480120310305c201006403c02d051403140000410100f105034075402c444c04405010300c40c0c0c11484013040072400c080161843c14402420440c42404940384100c0100440380031008192201c904000c3d600d040428194209816454154000180d0ba0700c2e51214a42400b8441c40302203460000303100f00360310380d00d00a501600c058112041d400f031640000f882c58010320000c4001810321000c000041c1401d00203441101c4c110001107080c908040301c080c103034003010a9100c0c01c011012a2483d0400d21404604211014680e4100140039410250740000c9c02e030302d1180e58a45489000307000140f40b8070b10880240c2c24a0701c1254800340c0040d001c00000320045550010306648800650900301c0051000300325a01d03c0d246143c5415141c840002d0498660320042445031800c0c110030055030540210401c400c1 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 987989640 1250 987988390 987988399
    0x80a02130e3103050910051e1c0b100e121006150c020d030c0f0210030510080627070b0309060402090f19050c1b030d060f15030902010509060715110703090302 70
    0x1401007600c1114a40940160043c0b4004581d44203080f50108d0b87c010302000160440300003800d040c000b00c01d815145036940d1603400400000804100b1841950310056403500208801c0003241c1c0c80f4041460090b01d203130300c445801d0b80ca8100700310682610f40035100c80c2106080c07000020f446600001d104100c000c030003600b0300c10112140030030400801c0e0200034141c0c0c0240404c0001c00341860080003010200d4001102101c004400f01c0c0f0044001542840b0302018207240002d8120040220101d04583e48004014850b0f204041030380089103016601c60164200104858070f0315004200300f02078060108502c071000c0c2c1c800c4c0500d1002c0710207289040b07003e1110200705501d800b0101c0c101403203202485004120640b072000300b102c074080020103801c42000d6050248039142d0030b000c01a038060b8420008030240254000f880e0703d0003a00030007406d41c0141842801c00c4e00e001c02259240d0f01c98842200e140440500803250312403e445038060a8201250b002e09001c1c40d07a0b40581126564040603108 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 987990890 1250 987989640 987989659
    0x70c0305071716020306060d2303042d12020d261b070512030a030b01140a031415060403030c060b0402040320060703080a02130e31030509 61
    0x1407041502e110000c1e0705103406502d60703441500c06030a20700c0c11800001c9100b4003134034020980500c6d100c003800b0030702c0fa04480e50340800001c00c0080182d4801c0d0200c3e214072400b0500002403109103503507184c030303082004030b030740c00940c00e40a00c1c0481ca10300550081182c240307070040454050f071680880429103035401140181c140b12650055091710b1149990038080900005821105050b10200440d08089074411180655110000c02c171007215003003031980c90356100307001c1d070820a4820303000240952010b06101504000c484c444c640e05910030200007000c00e45036032086040d141030008070360340050b5426035942942181070000380c4a02c0b0302e11010301006494000c0c2d03414854a58800e00400000900842d5103640c1c2e40b900703180390350341d0104600041a140f110100345081c0341702150302056255580b40380b2541c458000100039001102020b411114606010a050120074000c80c0529805c00d6840355070300c0c40d0f038a4a610001415100707541200e840f402c0c000002c0d04101500d809180451782c0c0b004 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 987992140 1250 987990890 987990893
    0x60b040303110c060d39050d06080607050703020606030f100b0103110c0a1703090c0409050a1202011a0607080a05030711030414010e01030504050c0609010207170c01020f06070c030507 81
    0x1404482c4410031364003020018036608007220641c805484c4e5509100c461103045900083c0c4200f4401c80005108000841c0c40c010401c0c5120700000d1007418414400018029280c4151038034003d4110f0f0940b0101d00001019003e250f010060564044070072402003a113441c1c0c20030065164080c0300448414107860700112151603000c0d422000d40d5130400b41c17585440d0101d0000b515520040607401351000c0c8060703580b1910030302036207044034070408540b0000c064050b1440203002c000c240004055420f030242565040000310181e81480246459500205001650618100038400c4210115118181c10018400020303043d500b0303280c82c5450343c00e0076a200d41d100481594034191211510885003c00140441d519030b903807150a6050b04282d840c0b654080c080e200540032900c0999000d401c50303010a040c0d000500e003180081c403082d141071040e40c04441c1d07500300c01a01070021a41e03a1003660000184c40b002540c0c100520843e0109440091116003003040010340071002841c0c0250070003100250300320 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 987993390 1250 987992140 987992143
    0x1a1008011503170d09060b1002073f11010906090602120315180a060b07020f041d10090506060d080a0309020a03080a0507020f03061e0907090c09080d03060b04030311 73
    0xa80100c0401402c4c05070140c1032806ca8000c104290402c0d1050a0202a0b00745880c070004440c0c040e5104035201c0140c0085085114590404007084138807a003002424040b40480c0c1d90030041c5d2014032688550110b100d003c8005400d98409411620401078184000c0001c2640020074103c3c3c0394220a142d6542e482e0300502c0c020641100010a130032603030610000010b058444402e51081803001004c2203a2070316400d200701c0910a0500207507201a200103107052915060b44051200c00403001030061042c0c0d0101a10b041110300e8680c083c1066542000f201404810b04c4240e42c0100b0403261341215102c2c80d61394a043c0e000e0240d0003030405540b64415821500d40707500b404051138100303a4164480b9041800182aa0f000e014101c1c00340040b50481c2600e81130000d08607000f6414241e2124089001e48400203030380000409582c001e100d9500c000810305214811090100d6071a0350300400c842c04d01e8850740c0350035951034501c81018541a0204085550300f0195001d896252928001a591804185 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 987994640 1250 987993390 987993397
    0x60405090d0e1224060f010903020105130e09010c03272a0e0919120c030c060501080102121302030607110f060f06040e1204050904020d1a100801150317 67
    0x42c0b029105108100c0c0c4c00c00428001c054403080f0456119070701e942e807202031003503015183e01c80340d020072140f03c410f000543c041d00203004c01100101560395580c0e910400c5060784841035842124076552040804415941400b818031702d035032080c15411322800d695000d00f00100710000043c0c81c4403c1082145c07a420000360624840101c8600780003091600c802e2910a206015182c80c4a1031041c40e492104801c0398401e00540c07180c00032071055a10025910036181c00c0e40c840c00c12401c11100d1706044000424611a140c040c04c00e201c001600c3e00c1c1c40f0303042002000c0020b42450400313404016104016a000240c0c0c0f41c0c4111545400f481d0502d480305c17090b10344040141c0c00019070003040300f00700040111145080c490002120207016034074002a044c1d84404a04c4100300b840d00041000740b04a080c03010f8044d030410710140414030401000d4a40c40100c043c0d240c8000c0c24001040c0a010820141c843c1d840d01030921000208540151040b0580c13090901d40310051138455089818245020540140e = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 987995890 1250 987994640 987994669
    0x3050706090c1d100303030c18030506060102010c050f030411041b1e0c05030409051b0f090a0e01060e0f061b0708060f1306021303060f14060405090d0e 67
    0x40c054108640b40c000011000c60041e039069003409400074000000c0c180016028801c003000004500e410741c2c0f41100941307800129501070250b4800c40001e11050604080700450140740a8800c80c00c02c00002425500d24640b0441000b1050011070b20031041a0100c0303411076809440004403080040200340500a8a80954500f40c3c065540051098004c0c2d48030b003800c40b508e203c01600e52012841900c04586510003d01290b01c10320041c003658607260301454004030298258001703450701421071b501c03592004d01e02d03d11aa0340400d2104040c105028590301402000070040c60310b604111000304442003440907030b03100d507141c1881071b9601c1d181c070022111891104000406030308172010b42c3d035035901000d2041d03a0355840340100080000c90f2082c46a03000f460b06114040605442d40c60342c0c0042e420041108107004440788000000490030300c01d0340002103507400c010407021021406541055401000c0034052030a2400700100d680b40801c0c0340e10311242030304110881818180c00b1139090031080703a0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 987997140 1250 987995890 987995903
    0x9200c19062007153308032205010306031a1008120403030e0405040236150f010201050411120106360c020718020904052404060e040f030507 62
    0x34045400818000f44900340c001c0650340303120382010042404440405400650781c0e11a807400d0840580e5514030090044207682c0c82019030360720340b00001c0c00c6034000f0403d1998000c0c0909280e081001100c0d07010001c1909080401000e803071519010b40001d049050000100c0542c0c00103140085c2020910000d0316200080354980710b0240a085038940c0180016004100c80104604a5140030b00805200b039901421014107034110800c1541e42e44444000e00008403600081080c0d001d0b00000d14034071030311000c101d04150300b20060501400230024110581164107010400c000b00e0304903440f81c07500030010b0700d40c1080d540e002803400b401010b0395085000f240403208503140e1041b88081014154180c074006450640301784100804c2219246000c803c05038204210070400c1c02046d0344c45c42c180d945000c001500d0f1020280010f011a14211030000c42ca4081503080300000b00f40144840d100b0006840c04c22a02d420001051106d40c00100001c18100019140400301840f42d01034a2909030b02c900b = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 987998390 1250 987997140 987997181
    0x1061805152d0903100e1504030507050607031d0102031b03150d0c0f0807060906052808071e0806040e0c0603040f0506071706010e03120409200c1906 66
    0x103150880341d0f440042c3d8548a0300c01d0f101a159408800d11a500144e29600d0041080b68601046440b00368401801030342844018400c0d800410424003c0c1845560700f40d400107042614030481d400e10300c00790345860845078414820048000c1a45448158104e002c000454699945028481c500700ca081c100d1900018426402c00410010440940948845021035070304135407910b60295035014148507020012381000410040d40d40100020300c400b110f00348095000700c40c28001c003203d60101241003800110011304110355141d01448100303810403480450118a901250f00900302040500362510459a4409401c020b40382041820041440503041756100d2a00d41010a8070001d1b8a6040d80d40f4022080000d0082c0d03c0f80030039448021800712075041945901004440f009100301040f5094400c444c17108011101c45401392009040c1c002020503c6d01f9040130610b0f2076225100e881e850361200340305503503102d440804d01420700c00610489640718040c0f0b040c8440a40b2310169590b842a1000 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 987999640 1250 987998390 987998467
    0x307060e0304050414340f030b100f020618070317040e010f08100903090b130306110c0f0a020d0b0c090901030609020f010903150216080307080106180515 68
    0x2407012403141100792001b0182c2c0d82007000400c011404c20700e1640c1611880c4081c02180303402066440b44201d000e01d00001c1e0703418171902083c07190000c90000c801003044055060460765041040b281e003e005641e2003031038113540d56a4140d655000d404000c1000c4042c003102d45204514100b0340b0f00a05c120501585556910201851207440c54003c03a000d90152084844170b911140c000c0c0301b94254955520501c146c039107462aa0b440c0c200251130b892842003054000701080f075070f0103044c1c800c1d1908009540daa900d5017486034070b821000c402d05180c40c2c00c4440d41901580e2545194116107400940300081541d075a011760b82ca0f03100d040b00e016448074510b030022041c0906584407600c0541300740c540184403105c04005448016540c44020298291502c001102840c0c0d500944002020305c1180740340d0801d03507070b1f032341c00c40d50001c07690f9400040c194401005040d80c401d08460420380e000220781105403d080200f40301410010b0380e540700788000a030b11100301c036040c0c064210390301a0304031038411110f54 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 988000890 1250 987999640 987999671
    0x303010f050307090e030a110a0b0c0a09080601050f060306010c0b010b0a092301050d02090a0308120f0106120b0a12210504050d150915020406140a020307060e03040504 74
    0x15400780314068072070302c1004070741c509913403140503480000700c5c004500b40b125010b0103c9140b240401055003902480081800164402054500031b000e2103000b281c9907000c00400410303000c25a0300002007a40624010401c9403038101958540c12001c1c2c40300343d0740c1c0d0381d86001a1400301c2d07083c0c0020b0005428200004240300e1040c00b0300a12a02d69544c00d82c980e944001072a540481601010710240e00c144000030b066004030004c2040741241c800c0582088840d000152000202c1c1d4810b8550500c0041c50103800013601c00c049a005240e2030114105504110b40102041d007035040805810780e803024804003980e14018950001c00f600301d1f445440d00110b1a0006208000078200103000d0704441c1035045090090059509407000681044403011039619010a544c22000034514115911301a0030b01280354a142c003034004542c0c01c0050390f600c2c035000c0001c00741440148160401e88c0305201142106901104075094a034200310701040d400303072060b1603504610550b0f0001c1c2d8090f00d030000c0781d43e482d0308 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 988002140 1250 988000890 988000919
    0x140304030b0103151406010e04060b0f2203030203030f040206130303031b0e0f04090c120c0f0503030f2a1e1c08012d030b0a0c0306030503030c0a020a05030301 70
    0x41a080c8200c403841e0000c20905440042941c13440000080700058440c1d4848e01080122060003080070407102d640702402c074140c1d404100e03000b04040e0006188000b82c070090078059241d130203e440420f4030500e1503e0003916404060203000144403080d020505559654050750403001140e03800c0b9410503075078900036000f020020540004540c00c906e244000901805406d43d0440001d0140c4030041443c1c02080000c00340000100c544080815000c5802160103101e8250148241e810a00542c24058880090004ca0380b00c40e104c5d42c0100020040c12840c0c00c2510030b081c901d86101d1840ca00f50007600a00883c0310400040c441c440d111140100b4504480d07200c486660300003c1c0d45c0410107420f01110071103640e44102002c921820f0040219011192140c024030007010059203040540c140c1d9901c0c2c424031540282c50502461040c0000d4010320710603e01030740c10302d0070200b05103403030b60303858035128040100b103c0d018190206030407145074000c4c0052a13400da444801c0c0ca54a60319030601c00c105d0320 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 988003390 1250 988002140 988002143
    0x90503012d0b01050406030b03010612080a0801141507050a1205041d0105031b1801090f050f060a030602130306021209010509030a30020c010605011e0c0609140304030b0103 76
    0x7004400c500ea009112407152001125041e540e5920700742c142903080c0c4c040e00d601c0034859010765854a00140b00c50340d10b0341c4140024424904683d449141c00030003031040e541a0801c000104441110701c141d80c0c0c0d40380170800d00e603418103c200c0d1160441e08040d400c003483d46a01a14840f045000e8000465004004000340d03003443c1c496207048400c0710510034101509000d840d8056020210881c042000804034124480005004000c011030310b1007004e1080c4802e900481c20310752078104104010328940a03041c0c1c004100c540c80700d0b01c0d140c502c001680101b003522001d0480d5078005449603000001d0741d840800765400c02000d6503905500c8c0c030138a40230b020880718891254079000200d01c40c000044110340040e21180d8075407401701d440b01d0381043e0700080b05141c810040c0c1103014401c0b100c411800a03210000c0c080300001425803818002500d0074099034000c0c0c1c12000410f81d503816064024142002c1c2030f801180006020700705250403100300000c0301000c0b50500c00072134000b04020b054044141a42d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 988004640 1250 988003390 988003451
    0x90615030f0121110d0f15020c0d171609091a0f041e230a1b14040b032205060a0c090b030606090d060f060f0f0b160309050301 56
    0xd03440f83c018090303945090b16006004205a401e084042c4c50039500b03440d00d103070256041c0180e42c516030b81c034206038482c94400010007030b0300800c1c010300320300f02400014080308090401c04124132629a1000d41100d000306400780c14142040c030f00b60141c4c803482000c000317414520010010040e00710745c06103000c292000454411003440880300342d6401c081c015590240d8020000e6120f01c2d194015a10140090000101d000c0003c4039661003170050702d41c0528081c5104200020744080d190000c20b40c9005042421404d1103005040c211a1244000494044a132580e024a480391a250880d4114200c00104007854140f12040031040c401c003c0303043c0d409014241000c0204103103075801a80d94142d14426074014540900001e00c00d4140000205504000100301e800302d41c80c913a682104540c25550425107040d51500140003002d0200d84120103051014405a003c03454240c061003188202004a1280c902c0ea4103c0c0c0101405503a021024120040c020304c900c034280c036408850101d4104441410 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 988005890 1250 988004640 988004669
    0xc07090e10060b0405030712080d050f090f010507081501023c0105010b040509130c030804050f1206060d0213050403030209040b040b010f0f14040902030402030d020f060402090615030f01 82
    0xc0003690100d1303040700c402401030882a8901803110f28281c9030b0100568201c0d500b0800320300314207828803c41d8412030124917541d01034140b06044602d42410310300640c81c50ba1600d018003800c1c580140a665100304040c4084d07041d0103800c40102d042c2f4844c40d03020b200346002e00842040030118503540c085601c20700c904015031000e00d9000c450a0318020301c50208102004c000c14030150914850300703030303000041c000c41850540d902c1d81e481985001c954400e492000b40801c0a01c040c1c9010000f601c1d00c0e001c1103c07000395010709403266076150000601000c0c41840101244c4003191901e8003017840300c10b12483c00f041145818100580031751710005103948103901e480c1001034146418810001030045c1070f0741321107852400040994000385046040800d00584010820401700110014000360084080c00345c1c590601c0d02c10716141c1030f0208800415500324055410b420400090120b0380690103c0d044245902c90350003043c0896400895021072440000070041c4030030011640c14101c2d80480140803d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 988007140 1250 988005890 988005899
    0x140108060a1b0e041109031e120703120b0d0f0c03020a060507120f230d060e0105030a03030902150301030b040212030a050a0e0a2c28020c07090e1006 66
    0x7020b841c45140c0c540400d4060a5551403400c10794000281801d041801c5c914040b04807000a03c1d002040071024866030019040c2e42d20307560305001c088141513045d040ca41c1040002d81c1c02801c220001c4024050351581c54203100b9503541d0391702ca4002e280d80c01c9003114800344814242240701c2c590a00040c0c0c0075010354200003030060310500490f001c076030300000d03280300c20030880704120f61f400f204003003002c200420310742c504081050f40c07840704032000d6848200949c2c5100c400024001c4e43c110343c2c46002c40e0400350004000380d0302c2c0820a0b0100c0c5a2500d070010f941502d070310003e560502082081005103101000100c02c0014a000c0540514021509000f4020600594641da48551268500005d4080c0300e0009041d0042d0340b4803001c410000c0c00440d2a41d2980b0b110091250400810b124000c810309481c641c0d0948400780c41e0b0444002ca5400c051060280c0c000400364465245c003d0801da80001d040b2038003e41480080c0103442d5001c2c050003c420b06040eaa9550010380700c2441600307161407800035 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 988008390 1250 988007140 988007171
    0x302160f0c03140703110d030e0a080a0b060f01090308030a0609020711040e0a020a120309050d031e02030705060f130204060e090d02030315010503090f011103160806090c030604140108060a 83
    0x130201c03680001c0c0306010038048810300240034860f41c02141441040b05414006580e480b0070781d0060130f010b0008001400b194109008105006000a406084100500c1c04e05903404010310381500c2d003200f24140d9a88070040000b00038800c581c0200292440400e946c0c0820609000c0d154120748100c80910040d1030f2020150385411415030001d50000c0c120354200003503401c81d10910351913402801c1114803255180080b510700c103112401140041e5048a00040d10050340300c11004d0400e05200560030080c0703035070721543c0c6d409001e4036503491401c00200003a94250701a8022980c03590281052000030f6403241403d40300d00c1300b910440b400c1e0003a0106000302a10000559200d01a0421402e2503030210100665442d40090464081405808041c100b5240240990504d045501c0c8100b90342c3c0ca0041240c81e04414100d60035001c00003000306200103952503c8003030ba000700e9140d103055030342c2d01c805c0c0c00a0000c01514003102c0740361400c400000344450b40403607101d100307540320071f402d02c1840d11140100 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 988009640 1250 988008390 988008403
    0x1b0b0703090503031809060612100f08030c3d06080c181b07020a060f0906170f070e032a031c14071e02100f050a0302160f0c0314 57
    0x6050040e44501500610314100700d546400c004040c0c015481d0501007801454040d0045072440c0c02d400f40302d0010881006100044402480a08041d505018ec0000c1160b00c0b240541b07203104e4044101006444050708001d19040c6c102c25070040ca40803102d02c002040040d0100f44039120b028081d07000140c2480c00d040010314a103081c14982c0c95a1542d90070600440c500c0c00c4188030344c04400c103000034030060300d460300000050983c94440c0300641d4528100180500000e82000d4108654001d07a0001c0c10303a081c0c4411340018031090361002555035424115003001c00003034050746c54030500450304402100c1c049d0f0700c0e09004490110501c0355910000b495603411103243d80116044d00200100b510714400c09070011000c0c08a01c0851030001141c681a81400c110381016120706506030000c0114500003107110480091410301c0360618500c076201071700b40e0240d098407105250700001c3c0504500003000518840e00d51041e1001c0700000b090422009554541c08201c03642065524441401400003030710 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 988010890 1250 988009640 988009657
    0xf031416060e0402070f0204020f0301030b0115120b030a060f020a030b0a06091206020c0318030105090a0c050d061b030207020a0e01050d08092101050a0b2b1b0b070309050303 77
    0x1044009542e480074080250304c40c4400740e03140c3c00e50680c2c0d200140d599000500181c5440003030b4607282c1d411030804118152060780403001c41c1d0400070301c40480a420640403400b00030088800511040320741c0120f0b0810f10040d0005180c0c03860070300f9100f180081540a003980c040b0551782003000290b100d09001148501d40030b10070205149802c108400031103000120b41083c851403001d404c0408082440d4a5a004000002d01c043c1c05102004440d0600344151540032003018000d2242551036100c8030342c65841780c0151805002e00d2504042445215000b40d00c3e0100e040b5408800c000d00c600c1c00400a4202c240128030455600000240000d1800a1203050310b13002808040a401d09035501c507459401a545e190304424490710844480c545907881c40044680314001160900e000001c440c11103424840c0355108091035400421100d40c4480103d916032401d60100e80703841e0700750070072040b030400012907170101d4000c120f808204020914007804a1902ca5281e0443e00e6840d0800c0540b280202d125 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 988012140 1250 988010890 988010897
    0x10203181911150c0c0f010813020103020901020309031905060f01080601050603070e090a060501200a1220030c10110d090c1d09070503120f0a03060f03141606 70
    0x191808502034164210300548003c100f11095100741c031644030241c00003a00384210307810245a2860380c0c10448414800d8402c01d2074550b041d031410030603000b000f01420750041d0405078086180000c6034002c008a45010800130111140c080c18407000c0c2d54102c1040750100c44500609000c201e41d9402d0f0f5460f24165004600601100e07170808051100c0c070740005200c3e800f0401d2188084429841d0116468041c21040002041c0300e82000d00160000c01d6100c0f0f103d2090346100c44040c03580b04003190040280b6448405c82e80c07100010b074002c0700c80d442c90310030405080c5503201d0b000940b55400001407034004105c1d4190b0761074401c100318140c1261503d0600c102054000c2000204060099010f00c0d03149100e51040a0a251900d25a402da03803120148200307484130000034001110310822940c001844114002d000d5115110082c0304a409152a10500301c1c1003c506110b0050081d00528050181482d00035000c80d0b41341441855403042c9000c00c1541d01a01401c412941288010201038401544 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 988013390 1250 988012140 988012183
    0x603050f030f04143c0a1521060605071101020304030b010510110d030c03140c0406050c030c0d05032505030c0711040903020c090c07030c0f020d0b0901020318 70
    0x115500ea4011030400c1c083e521280c0f485440640030340178080200d014000b1110900e04031400d110700041401c4401c080c61080c603d5440400c5020411320702c11001041301d10344860020f040410302c000510046100e208100d05250003c81c06a80c440054007006001e42c03482d00c0c0c0c1c202144010b90300c900c11400003420042c000b00c01404107003089004400ca01c20149010043c0c41c01c05201395041c80ba5129000000940f40c505042d981c5500d030059255030fa154807a4400d580c1801c441c88400c0340f285205600174800d0200364040070040034801d0700e18107a5903c0688a43c00100f5100402c26402255403402c0340e441d190480840030700208003d0078a0b1500e803502d516585400101007030035000290103d6001c08007030107540107130b01c07207005800304d052081c2c00510f004084c80c1c040011810009204034040f8105000c3c101c003103540030072a005896003100709400c0042c894004201c0400c90300101500b285841028005084015402507200e081c1d034001031405143c02d140c0366502c1d10521180f0011060401 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 988014640 1250 988013390 988013399
    0x40b031f0b0a0f0203121008070801060e07030b190902071509172215030507050c070513020c03120a0629130527010f121103070f090603050f030f04 65
    0x41020720030711002c3c0c1c0100c2c4d0410f94030060600030031500311440307842103c44203820460f0003410030a4001428450f0b0007480045d0900c407104a800748003e011500b01600c980f5920402d845440020090072480e01013a00c0342920707140c410340a98820b03d02294150340c25500400c0c0c00b00544105114a5480320900b200c1464009034200c0f99000442016800e211b20030480035003140640c080c030002c050740f451035038203071040c2003016003211740c01086002409010801500300f13801c0803c0c0b54042c0c42c001c032540b690700ca10b49003980380240139840907a00c29100009403880204400121603100320b00c2088103102c416210b00b85501d40d0814101e10800c0e200d460501d81d40c000700f801000d050915200700d008944240c0c0c0e0000039070001c81c0c07024001c042c0c09610394600c0780a424520980e014002e0301c40394001c294641105804031001d40031010b40f410b00204200c50380d654003440004024896404e8403404d41d8aca807408a002820b803440100c44511034000c02014408012040c1d98881c2d15112070941010300c0d1 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 988015890 1250 988014640 988014647
    0x203030706111605100c0c03170714030106020606101d0f040f051e0a050610081b03010605120f0708010e280e0105150a09020d0b0402040b031f0b0a 65
    0x324446089a50024001e0341080c101038a0a003140c01d010318001c0804c5d048441e04642120303400720054041280c05600344011a8000c9c004c6400c41c2110003400406640701a0308561820890b90008119000003000042013540094018007680303086803403044806c000f0318169240a9806111004000810a1b01a1a280040f0107400000001e4004203150f0700d05c844c0a01212422074240301c0c01210b2030b0070032104188410101d580070a000304100710904010b07002454459880140000b00201480011240c61300140a0901004103c1d01c0075200d503100e44000d800b50304040703810990400c4100c0004d14201c034001c245400b4060603240c600c02a402d001058484000003049108010721140042d208000cbc03c868820510300c0311000083e25100301140c15081d034a010301b85d0200307540c01035080a699a6101101012501003082c010394035266004124040c3c108043d120b88d10a01c04100011001e454000a600c1070091009001c1d503a03050030107801e0b440402d03010f0300b40a40300521000202d13501 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 988017140 1250 988015890 988015901
    0x1101020708061801240f0b030906040b04031b120f05040b0702040e16090506040c0e010e06031f030503030106020c0d17090f0d050a020f030109080702041802090a05010614070203030706 81
    0xf480c8002040c88905d18a0100562135200c0401217017000f6010100880c0c3c4c00c1209034409040c2c009800c13403079810618842a680e80c0b0140028054a00401c007003010940103900e01c43c0c44005076140500f80020350704156000c8280c00c00c1010105410840305c1e04cc00d40720f442190169150900c1c12810002d079034003800014a00c402c408000307031241c4d800080c6032125072101d0030300508000402140601d40f640601c420349400000034018041c140582522680e0484a01e103800c1c64256070f40c40d181c2e80d805402c00c1d90b0059110042c0c2c0e10101035407009c0207110001c0002e5040e55042e40880f4603c080e60f07801d01c50380f000b401a000d0009030782001850308101000c401002c1440005001d441c00c4400d03200010014401d0034801c41e1160300983e182c01c1142040c84218101880440c0204000145904d40440c2c52007000310081c0708035620360170701803507040022a40450940141a1000c60f1419855aa0040c0402c1c0038007000314801300405c11004500348104d0341503e0740500503604040403962803201902c03 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 988018390 1250 988017140 988017181
    0xf0c0e0418290a020c0c010e03060604050c04090207080310120210030906020d020c010b040501060f1b080403060507110606031f0e10020a0518120a030c050109020901060c110102070806 81
    0x30491800c8200b20b48428140d68020000e01c0e100595a20304c101c00d491030156000c04907410300464014940035aa00401c0d45688032205a5012400d5540e0000c055007501c1946c2081440394030110f40380d82403162482c091881801d40c0720b49003401e5502c4000a036012100c056000354030910140b0200203680c0b11b0340214200710710031400035050039a0004150141e03003084050155036075641d140c0d1031031440e1034000c0034010031050070510b0300102794000023403142404018121413844407494003400c00c83d102c01224011604800c00b040f071800c018400411b01d44080d6407100161280d80007207043c501e00800c0402801d4586902c0301c2d008607a501d020340c050071801c000c800c2c8600030b10004e0450302c83c05000400c01000c00350b8540703035070b0a1505480c40c007641354112081d0249605148028000700c0c0020060380031601070401100d00101c900c1c00602422107200025003200b6002c0000800d19084200451264400c00e10545608202001207944062502c1004860f41c404408034501510b840502900d05 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 988019640 1250 988018390 988018433
    0x30a030506060c06011205070e070c120e030309190e0c030f01060504081b180c0c10060311060c10020705100f0b0310050907050918060108070b07080306130f0c0e0418 73
    0x159a00d90b001442000200c0304c43c004178be60003540307600700701103045281e0501c80079051401c0d200c3c482d0130100703550340640c080070382c0280000c0200c409804d03010300c0d203413000b80724411035407050745800070581020ba042900c0c40d401a41c0108004a4903070f0251b800d072416101714200602c0714030002072a10344922180154181c02c8620000e1140140c040405810311642e410f46510350740300c15041c2c29500d4440e401d0040d03480e442c50300c0e0081c00010458105551210000c40c5d038140c0b140c000034805800d112245601261035032001440f041008004a00b82a015130b440504028504103c40c05006903041c102025a15030407228004070b1002040d400590403c940100710f1300310342e883c0c02c046201c0c038070103590658000e05c9100070400d45120402103107014042c1ea40180400901e0080700750682e000c0c035000101808004000680b064880040e0050440c4100f84244140302a41c40760381e00a1a00200c0d0380005090955504c0e92410f10b40911008904010f101546802e2540c82c0c0300d103000404100c11915 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 988020890 1250 988019640 988019653
    0x3050309011b05391507030302121815070507021e1804120f1d0312180301150f06030209060921160f0e0406060504020a02030a030506060c06011205 65
    0x40b4000304001107102c8103403010b8113050b00c100c4403440c1402d80e0020700a0518040e8140c0c6201c1a1984106009000c0300030a0040d250101403405070040d020b00d948072020503610304100220003180740802c60f504407800c0182c0e6051250001014840001200c524001c108108080001814a22040c1c910040c000c0d8841861007040306c00a10003250300c0c19040d020264020078031041c86022078203400341d04654100341d40300c0b0313907072440252a5040130744004031300711660310b61120261001e00c0b994044100068000f0354a6401f01c8a4204c1402e60b02c0e522800f942c82c1c5480d010862400401c00c0b02980d886031a10201c0c0f2789007a404401a500c03500c99281c1001080c400c0c01c4685c0c50360022a240034038200d518a206d0b0420103241d0745050a10a443d03a01c15488210810007441002c3d03076241612074038105010359942c0c6090000c0588015406560860301c00a10341507032941c080050603850340580d406000c1c40d200c43c0c04120710f60080701801081900008010072540a005022510300781c0703d0703000d43c0c04 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 988022140 1250 988020890 988020893
    0x50c0703120902101205010f051c061808030403020c0a03030519030f05040b0f0a0b0f010f0c0c09060f090608070504090c090203190b04022a0a140a120903050309011b 73
    0x701a11034402401160050f0400702d5144058010f00d4054201c01d113141e112300e0f10300800541d0070003940d000c2c442c01c00401d0350f0b982c003400500c0d004a1160501540c00744030b02d070305030329140b1640c0c2d104a41c1a4014040c001e5150080c0c070b45146644c0440e609541c405062541c48558020400e101c0281042807650703880380091034070154058144601d0088100803003518201290341592000240720101480c986a0341030001c1d41c4103010007401740401c0c80e00e14900d014444050f6124034201304060142c0f400045c0010f4548159045001601c060412580100d40e40e0100c1d00d064900303900903001144c05c910070a003c10304280c1d102403505402038035980385440e5240c1a1070101e07401a60101a480c070800c2c84a44101c040740202c1c001344038150340461500c580714880c2d000c00a00c3c12101d10400d03181c50f091a220150410418038032079003003041419840c20004080b561400600c070200c2d41002c0010340402d855016011602c12a42c11101461511044400440703c200350459a03840d40415401c9040 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 988023390 1250 988022140 988022149
    0x12140115120e030a0f09030b0a0b301605010206180c06040605030105040c050c06040605190f1b03051605030601020a120804150c0c03050c030d0c21050c0703120902 72
    0xd90081002e4007542c0d4800601d60000e061a000e070000704140880c0d210308200003001d24203940e901a03030020340020032100801c0050680d4050380014103150380d01c6020100c00d80104604100d84d20b82c010100d03050345080010054030740c041c9100303079400740c2c11030000035a69041501e103480350800c100058410084010000410308d40241e0032450020307d01000500941c1810700c81d920319958030b03040c920304295241090701d907140f200030801000d05803a00d0110399a500f10500382c42d148100241c00307021400030400b0080061000644c000700e42c10269108034400f074042e00c1340602a1030080383d900c2440c2407140003070354039500c0544480d0440c403a0001500c045119000c11034018540c2c1c0d9110748890800b400c055540341c40680c2d0f0074042c00d00d44081050001d40000103801e24a42c903051003503c3d4079044503028194028080302c9106241043c0d03039542d5035540040e604010300c40b03103a07148034460719160441c4100c0f041142d1000c58500c0421203100824003402420450900700030380810b00d86034603400318 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 988024640 1250 988023390 988023401
    0x902060309061008010b0d11130509030d0b3f0303041103010e0c01020d0f050706090b06100c020f01081f0602010608010b01020318040e0307060911011214011512 71
    0x1950039082141400541a00c200a03e0024401c001c000e100340540100003510000c04401d008022200314120141c1645403650041a40c891214040000d482d2402907140c9980c02a192910003610b4003500e003030b8a15200d07a000700814584811380000340030007104411045800103000500c100155600c42c0c804030100000c41c030940c800e01031081180e1850081c07509442d90302001200c2908021420008c90364001516402150b492400865121403184259094494020b01030209814075103200140310080d07002500a43d41603c440c009032540c00002c0394420510b5400a502100d100e038100300302c3d841142402c0c1c2204002d11004929102c1d034084518058456002e0030150f51651820172010702c01b88201160320500f80040c0d4034084014042021000760b91348010b1080703a42d40e100c211b80490400554840582c000000c10122038a402c0c115240c414250780c0c035000a040c0f406941188007103014220395520b20294074821139003801c41041031003040005410400403030002c7d034403d642d09070007203 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 988025890 1250 988024640 988024651
    0x311030a05120a090b0909071d12030c07060c0f0b06060910020105190e0c060c0a0803090c0f040b0102100b0f0a0f1e060f030c0c1502130501020606030a02040b0409020603 75
    0x41a52200f00300c030050586140741c1e01840c032070314092200001d140c640711181640109149441080c0d2441d2510340144003061040081e042004204c0024005a0000003049440040404c03607a026654800c00c42c0d00f1415290002c1c41101e0f240e02d028005085030f0803282e04040010007290814020202203041d00411240a81c0103039100d40522064045a403030034869548840014441600140c01107a41d414004000900842d400280741042000c00c2c0171141055620018096070390038410800b503078841d4143d5801e8415500520807041d6460240f03e6809003000607005403035428010750040005059004001e44c0180200c0390b0707201e00c0e0b650b61400380c0107843d0011200f909079007810301e0030211050007020340040300700300c10301441082d412524540310a10103180106009242d218200c480c034940810060a541c1758100c40d40c000c01594004d44016141c5005142c2c02d15030350b1004981e60107040d500341d80c041e00410b0802e009400c080e0041012048041c0010519040d10f40c0070400300e40c401c0300d1 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 988027140 1250 988025890 988025923
    0x307021203090d08060303030601090323010213060306080304060c030516021009031b03020306041e0818030f120414120f03090a140102030d0203071809020d0c03150311030a05 77
    0x400c16202c80e001340449421080507401503007981752080000e00403901c140400b030035820614840040b0700c0290b0100c40c49940220000359181d00b9442140300040025015001c0400d041c100041140000042a6011100d20347e442c00204031641e02c3c1551030340e0044040d4203490354521840805601d80142c102d80d400255601c681b0700034070b142000351500b1400508080715665000080015a03030000b5a541c006400103800701c0c00c0c145000c030405600c19070890080c2020070109800c2015602403120580911065003500c0d03c1c8004040c200b034a4444052000e00d904405100501c040d00714144c2c540c08003e030107403038a00b4a255134035041e440d01d51250b1100c43ca85e4000076910000c0d041c20002c1500524006101114810350100080d490780142c6c00100542c40e40400040c0056104801c5101459201500d820718691600e618401a5025a2107078040c01d0600c16081d400510031b109205d0030843c6905200060f5095a660114100c80740030f00a0341845003c04070008a04107001032500800b9952 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 988028390 1250 988027140 988027153
    0x130312020d1409011503080702090c1603020106050f1210020c0106030506151f02060114040212040c03060e160504020c0106150e0f0a060f0804062706140108070b030702120309 77
    0x100b0310300350707200442d1750030781c11100f410200f0008a4003015144030550441d181491580c8003070071101c15008451400d03260813900301d1180c081c1a010f5020383c0a41d04140c56208a20b40800103003c0d01e19284040f07807200f1352194a09807280c1149501800741d041d1f1120000c1503040d5680c4901e46822802e0320034030a8901c1c42140c11603d86050032068040c46107403895484031088001c0081d458103c14881d22402c07410380d030390400070765a8a904450400c20f03c0c8a002003603040c5414580704d16056070000701e0b04249044075050700799000084100000406403240074409082009002c040e402c52041c40c1d89a41d04c81102003807445103c251500c050320280d542412041050741001341600014083e2401468044818801345034080c4a000d0101c5503400e228006840ba894000c004080418a800f10702007200c4515001d56190881c000c41503005540c144003014803c030448141d48001e10462106501540d030030811340b000c0501070359101c565401660344a40e0f0700c401c0c0f10342d80d41c41110a52120340260 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 988029640 1250 988028390 988028401
    0x90106140306090c091305060907090f03112205090d022e14072606060d1a030601120615061e0201150605070501200f070602071704051206130312020d14 67
    0x49c0100e41c41100b518000315507618103c0c50181b180090702002e0502450420001000d45941206844005940410064a8661003c20340041c84180e503200ba4078020b441d00401d207244005201d0702c8600150940c5001c4141e061182c0d40861034400c1055412621030540003030030007424442504c548510785541518050420a90700049100504c40d1144440807051080684500003501e041881203a80000c3d1407a4044800d0b14241320f002440d43c0c144129000851202c0b800c0c0c000c410900c0c880c030828080d41c0e40c50310081d950004240034000008a003020481c8103403041042025000c5000d00001810580610b01e070a028000d640009001c91800107400040000c00d20400090350b411807041c1c00703044a40c4554104600c204420f2015044000c1604070520406604403030341a03611003000e540400c01c3c200305115030b410a100e01446101e003048002c1955001148070fa1088843e001d04031aa1807003031b5000ea0f0341f411140c04940c08180d09001072254020248079421210b40c80c0c060f15961407810 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 988030890 1250 988029640 988029649
    0x212010f0c0f081504020901030207120e0a0f0e04030c0804120b06090903390105040b18060403021f110a0215070207060509060c0102131202090106140306090c09130506 74
    0x15800190100060f80c010011802980340510046500440b400f6903075542d203100480c0640200074021704a880c642c43c1d00c03e0a01d07008550b031a41c9000c1910116009580d44080000b41135240c400e0825030301e00c0e2070002d0002407052412801c014452003480341890703162000c00c14521401b1a0480310555038806000291405600d095805507000c001545400c42500485611010f1408801101400001c83c01c514203903c0b0004044107210100800c041d1603e8141040e01c2c0401359981c00a5444951010701180004212603201d03a800d40c006040c03107215001c0b103000d1228000700000c000c0355a0340e1810420310401c001401d05210641c001d103002d100340202405043c0001d8000c03815988074400c10040140c105041d44d43d40e4004032001500c038480741800c05e01a114900c034160030309010f14030128011459000c1c20038124000c2d01c091200d03a0300c0d0f10b41510f564411800150301918140000340d050310b000e0400680c040da10105140c280042d080104901010a01e164a64941c498040200e40e060 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 988032140 1250 988030890 988030907
    0xf090504110a06021c0504090e1c020706020303040f050721110f0d0336290d05070c050d0e031c050307080a180311210904090212010f0c 60
    0x101e444180b07482c43c242e0301940e201164a806114059507420b43c2030020b024000343d07402058150001d014698486c5100750b11030500360340c03610000302c0d04040300c0413007440060031070300f903451507002540f66844c0e54880701d010003000c503000c542c54400c8036808170301c3d2607040240803d03684622802c02100707012841d2501c040c141e50f0825034000d0200c8103000c0c07016a90848084034090f01800d200701c062400d4042d4400d207402c608000c10b840006006c02505158002044004aa0040e40005d101110825a2080454801e864050300342014403005941d00c1ca240c0c003464010b001400c00745142030450355042e040c03c2c6e041e48190049441c2010001050400740302c0081e00c00c1603503101c0c0c0964100d01501412900000d0411410490003100049901156601a02904c070305203550011001c40b80c54000c00040e011140400e06000f02d0030554643c1c241d4400c16104020071030445030802000c2030500c801400d8094003030741c2c4041e00619014202c02d0a205018a8641c0e4000200d5141c02a6801505011 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 988033390 1250 988032140 988032173
    0x8030106120b06030105010c05030702030a0311100e06070e0102030720040c1422030807080a0f020a0203100f0b1507145a0717150406060f090504 64
    0x60401c44109083d940310021a410f4403024202002000b840707080480c5036009d1140c1c002c1d010f04c261141c400615400201c8070802c80502003c03580e9550403003a050040d03451104101596a01101c04100c1103801f9070200c4032514030610440b13060903110b80f105502c103002c05115040c0102c44681d0b01e002410f1902441d5440010340c20040d031070181e10507511501d071250180d52900481c5450b011000311038540801320003550042070040e100d80e118104070200d98041403104010454600902c1c5e021400410040540358004002d098414540041d4002412880c04604c5a0742d540e02002d00d0a560b8030441c10658044410b0865207801c03040c50164008000f00000b040035a00200c0d601c0c0e00207003a000700032702c0b80658456400488170410160115500510b4800600c841c42e00c0000c84040c0c0b1580c0f01100e400d0009040b110003daa0340500e100c907143c12092018141c0104805103d00c030080b4000c1500305108000010b8038a0b65404c0858055600b40c00c03210304d058417401804107000300503a002c1240c1 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 988034640 1250 988033390 988033427
    0xa0f110a02030f03090c06040305012307020a020d050111040f05040f0212040609080f07140d141e130e09010c030b0a050f130c020d120213170102130308030106 70
    0x1a148440c080d507240a0540456850040040021039031a01840256210346029000a480380c0d240d21b0000c2c0030b001002050140804411015030244c00000e40450180034103401034003055085e502070280510681d2415100e641d00e8038001c00d1041240c0700180010034101c4a980031341410b01c001c0000b070340c2a041c0ad0209035401403150848104072400150707002a8080c0c1c000501c044603107420701c3e1301d004100c4070034000d10011072001d09000b0201e89180407010381e40305542510700707800c006582c0300003c40c9041c0009542403180300c074001c42c10360b13440b030840007501c8143d030604c0000440c0a56441f400e0300a5403040160b0b005001b8500740034081c2c5036980460b0704060103140c1120000c9404403c181c441c075441910140d4003100030740c8561411000c207442004044c00540d00340f5402942d62120103500000040550b82040e082c82464030946001c0842400480070280c9040d80094021107010003010265500304100c0d1903d120500e5001d0003544900340f425125850301c100070700181400144030010 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 988035890 1250 988034640 988034647
    0x210c1403010e211605010603080d0506030d080610020114070f020d092301032004050f01030504050a0f03141801080603150f0c07140c150c0705010c15050a0f11 70
    0xc8841e101481c0d400d070b03c00512107840c2c400c20800880b92088000014240e0f5107428808803e03c04240c0080c0044c020b2004240081e032114000e166544442c486d4400004009001140c0103180218000e00600381610020600e50700e82d01041c08290f0b4181c40c040041450071a039911155010710819240d9040f600b80409094901b41c5584440a0740005c0e41b00c02c01605001c004503a80203a01c00c0789005062040c2c203100e442030034217204550f840b80c001d903441a41c4655030320385507621074080c3c2071145600c200a807a41070003d0380d8030a41e90350fa0392001c80074000c04180c414084803001000c0d20825204e80302c0d4203a5184040c0c005458603a010b010039000341c001014281000803103054060708070000c0c01c00e20b502030791791125200f001c1c0900c01c0c0081034113401109031122740c8030002e41400c0302c1c00c0c00c0380d00303201d10385100b8620141c0744180c106900d1135400c101000c000f5503008074004620a0300941015080a031500d2841d000c9540840f540c6038600d5440400e4461910319100b80401c1500741c0744c01528 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 988037140 1250 988035890 988035913
    0xd0b03010e1501051017100519050a050904111302130b030f1803040b120109050a0902030d050703030f0203180c0312040e040f0204050f01090b1009210c1403010e 71
    0x10070b8034140111801002d00d00e25114210340700345d0040c0d0302014448901211803c1c0896a4136800c11544502c40c4680c008040c00e00205101901c03260441d000100500c55291801050210f0420f00500079501c0701010014500b01351180c07481d0030039203c406a0016a0398160003105002e07100136421480c4510000d00070046100070740350860760490005622090182d500900252031442150082c928071000491815480c06080700710b54141e8140394418001d665039042842c044407a4000301031340c0740e40036020350203c590203003004240c0203020389400309002c3d03214074041080e60310507078a00e09144c0e2a5403c40715403000900c201514006c00720013622030515006003c00f030314092405041c8102c04400c01240400c031110300c210060550141060166240c401480349203c442445001d421904012000c0d056140403a0301e641c1c02502900d0b090002d60900d604134002c040e0a80c003c070741da00e052030300520202c0e00901074000108042c0e0900094014510305260940e03040c03020130000b6610108883c038 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 988038390 1250 988037140 988037173
    0x33c0c0b03060f0d06111b060f04050a0b04080d18200f01030c121125020a090506060702040e030306040b0a1406070201020a0c0f051002060f0114150d0b03010e 70
    0x300f126044448055128440c18540d00504856041105600b00010b061001c2d00143e1401c411685200083d1a920340c0d465040c581503007002c480007082504000d00c0030340021901e02d20302d03405ca03010f103003913a01300100320311000100c07200603084003520100c080a2004101d8601101740d600a06244000e54a100050129458805c1c18079058149034881e80509040741c484e1008200004402101344554616a000c00210f40d0004150b050f4051100e14070010701c07241803000d89401e9030701521060109142011900c01010040c3c40513501c41c2c01007043c60056640c038040d0b030a014550302d0195669060400820080310190f8101d68092a0710314010000342e80c0d84010302ca940310382500e61030340c1c511040c80100d08103898281c0c014a02c1044a0021821188280c5030b2001d032032045d10300c1440c8c5414034805030b07640c0004a1301240018012401400a11401c0b0b1100c59003d0002e000e201d40c80d592100000110b0b0401c000a154650303843c000c64410b03107070074054003001d094201c0107059459049032050 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 988039640 1250 988038390 988038409
    0x30a030e120c03030f030a0b061e0a0e0315070f0908030d2003100608070c150e01060506070b0f15030d0f0507020a0b0c0f060709033c0c0b0306 63
    0x151080d0344500c031106000303038148094404800e0080c244c0759100c03104215048990025a881400c951400401c0b0b2000d08241040344e0200c20421400c0444103000d20070102e60b03a2000b0010010000028603040094034200f01d02c41565020590340c0340c4038500100300820140da6401441c0406c011480100400c40000c011101d40700442e0740042012402045078074641208400004500c44000082001014903011f44001703454403a40c2c0c410b46a11240b608035514a0560000f03030648804c0207100c0c074807101c658024815170440314008107109aa0b04006501c40c1c102c2d20041c0c4c1c0d0000c1070030800c460401c83c600c5440d4481011454210450a40c1d008260344149010000d410300010b001001510341c0102d003600c0382d06034010045911240ca41001c0e2505800801c0c898001d84108011410812404103c2500c584090703511400c109140d0746403001032080b0000c45004103120702000b60843c0100030103c0144015901c0c01ba40d8280d180e182141c100e40540d4064038004005009100c0340380d9499441 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 988040890 1250 988039640 988039667
    0x1c061b050f0d0e0a020607211409011107033906020a2a030602090f04062904030b0a0b12030a05040509090c0a0e09010e060f0c0a091a18030a03 63
    0x140030780d110400f151400000c0f0070040c1d84003801103400420000404107505040c1485100d01e421103a410314190b600c0a031a19117000c859001f40510301d225407141c211984559000760031104103a0392070301c8034406400c0c220088154103117210a0b0b054056400c481c400000946d05408003000d502e030002c000e440d01071000000340300d5400c0001807807929040462001d0402e514022417002542e81c2d250a20096000003501401504606216034007490140320f504200c50b0621034070118003003044120700303000303c9217102501d0200c014000440481e900d000d2080c0301798801040001e8182003d000c00c204100100c629803650b9000300302e100348013580a8180c030708850064034400c103252140751801d402d1960041807903400c00302e040c1c0c00098020182d09258010515000208408542c051040e48c541d43c0c2160047c046a0340310020410f40c1d04104010940c02070300345016007a5a8458030040f14a140841d0b00c00d86565011400140140e0110454007615108038001c2404810503a805820408030031130 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 988042140 1250 988040890 988040917
    0x30603070e101d0105100e090c0d0e06130b01081609270b040201080c090a12140708030403051204180e0309030d1107060f080a0b1c061b050f 62
    0x481c00c1082c80c0714100014002e04040c0340f0070b5081d1141d00d080c0340d001c01d108541c4240094808600100e014200c4110700280c00b40c900382d003580c0e61030040747c01c0da480501c1607c1060350b02d200e10220000309003c5540500c2d55644003400029040c11700407140041078201d55929080400300c0340221100544540451b00c0000e000301c0e11494500780c48500503040f48804910b10000c002807006c00000071000352140303100362a140100d44400c07001d84410b000380610150844e4001809004080304260f00c061054440c41c1c030a4040a110480c485c03c01079103034481c4500b03500208080c0300b00071041c0200d40c1d007076a0441d825803d2528100c207455850f4182c0921440440d9609190441c220081c41114285840901100c0f6550700d8164010102d200d6014140d0241c0103082001c129944109801503807210165503821050300c2e0300840100500c0d064110701e80c40030f081c1c070540343d804444400c94081c850040c200010780313030711303160100d81c000b5210400725007004410001c800900201c0025120003014600 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 988043390 1250 988042140 988042169
    0x1020f06040b1b0304111e0109050607140f030705240606072609010908010204030c061809110d0f0b010503070c0311100605130614040e012405040e0303060307 70
    0x44031140c40e6100c80d1001c07440c483c1c001082109014054031040000c00065841b12a880d15052800d00d010380c0034104e103400181d0942c81005149080340c0a00400b5016110301880c00101d494110320b01541000354a0303941e04081450810312106100ba0300300504140c0304040d107420320905503061008001c142ccd074800e0b0340200d01d41d024000140e00710b03c0030300014810140880b0300650f1000c51900701d41d05060000d803411074082024141030017a01c1c00c4079030200e40c400100e400c000d010b9420b410004051019130061450018800c0f030103001e00d07107482d02d001e50000d5490b201c40001c001a104c00880f448000c40c1003d50207143d699005045030f50100f0107103004c0c40e1208551404843d001c14456001c41984203a2030351003a1148203911450854004650408040358070001c0001074800c1403281800120484440d410242065000340c0d0414103450300020ba07103506a655070600e00d42c0000340420104404d6030901c078034106480744c40c442ca14941c0041d8110319002001a40e200c0440c003c83c060b01401e80c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 988044640 1250 988043390 988043401
    0xb030403020307060f0e101e020903031c0b1f0e060901030603050f0c0a06020d0c030e010915080105040b0a0b090d060908030703020c07170a0b0924090c01020f06040b 73
    0xb40155185158011424441617188610000103001448501c2a15001c0c00507940005401480b03941c445941c40b031084050111019207140003908180700d0b181d014041042100070809205018002c001c9030510f0000f00c00c0c0081050100041074a9460a00c01136880b08d0b13403801e190013600000c100101120095501d40120004802800c92940014081d00c01d40b10f880307904200c00700750202a64402c3c3c900602d40b071366644c0c00301e0346c0300148121034010039201c500b4240801c0c81541c0e0640045c50605010340b00c555902c1541c04181c410030110000034031000014011480d040c09054400c0d9070464664100074207002c88512076101d5881401d112b461030751107280c10012a904001c00c52500f052001e030301c92901c0c2401038040c3d4840e00d08800c09000720040400d03151160010012900d4211004001600720380d0384c0ca800302e200c05401c02c0c80511442d001040d50450308040d800500120104459540c01e003503a865243c00d144002003815500600f040d800c480700001500c9a05c65005000907003541c580 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 988045890 1250 988044640 988044643
    0x8090f0406050616020f1816090312020604060c2c0a030b01120b010608041112070e010b0405011d010c0b04032a20010918060b0a0e1c0c0b03040302 65
    0x541c8990f4122030042452448000b51000c181c50860007904c150402c030011008000c0410b0720036100408003006140421300084202400500d000c960303040100c880c03070b160744400e17203402c0203403a007800140d02440822082140c24000c1003403090884c2020042c071140a0701c1403844000040c044001500c2c4516110225a0b68910000056400c0075000300d403540c4945603d50b200011a500741c900d02e210b00f0001a190f03101d0482c0310b11a58210307400003034103040c030303c100404258110f01c82b10803441031810211b444800301c3d00d40703402042d5100d0402e82c1c851420b000907019210a107201600d00149544484903a600701c00e80b00c01041d0321515100d85030751103280c180d0f8114160280c0c4200100076525400c04c0c800403280110301d00d405800c001c0b1910301003a1411032010a5540050300040120380d08101e003440d0285207017550315485202090179a02c44200050030f4001180303010000791080d44080c25070505c1e41074035495443e0041030341c10703001e41c03502e80d41c0d4a41b04a20038081d50400000010303050510 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 988047140 1250 988045890 988045901
    0x1b2115052d0f22060c02060f01150e091504060b091509210f070b1201080c010c12020f10050f060a03050d050f0f12040b06010513050415050d24020708090f04 69
    0x180518100300701c003403105c0000c0d03440c50111400d0321144901e40001c10a40705a080a00f0485520b94803010304060b84414442c80d180d01601c2d04280340380b0079210207810369990066502400070740305800e4403801a002040715000c110404c070417402500300700c440c038103898aa0307500041c005140c00000c101075140c0d04052400d616601c941503940030310000451091684c10007051403900f089641c1007075980300c020721602d80c5180081c507400f01304000c1e01000083d14918030b041007060640140d6413406060071750035041c584c42c0000100f8a179960320030800014044a400ca40008054800c6200141543d0341c43d0307030b102c0000a50109112000c202421440d00150807104c807603440e898902d440b001c61140445090400f941c0840300036010500103200d41d4850000e43d05111407400e49580f0852825041c00004c000640d601130742942002d10105658031609241c4486600c65070280440305a4015006407903001c40203000c41240c010800c500202e440c0c501030f42c20120301210b0b02c103131041d00c8000090091a = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 988048390 1250 988047140 988047143
    0x70206090c1008061c0816110901060206061926010f0605032a21010507030213090209030f01090b04140a080703030b01030608070605071b2115052d0f22 67
    0x800001d0061160b90005860040448c89a403c08500303041e0714042001c0520240034003401640000009407140c0340503448140c416242c0b0b41c80d01601354030f4110113586021840840712243c55250304138107000c0301c24811a4581c040c103040400071541070034002030300c2d0902c83d0b85005180b5170040074151440c504803803c40c6410401012800e50014050344008403c1d0f26107074500c00d80d441c1c140011541800b0307000301c816200f641014425440d08081c0c1c05002500041c00c0150140b0a00307007140041c80092142d44c00240c0a82a403078003602e410310f0117070301d540c02d90241c022268014400d104002503841c0c042d9213006134141400310f400320103031004030020400b0340d0028650384a036810014030b4680280040c01004d004810070900c2414011103002c0c40b1a0600c6001d440c0189038800d6100752155801e0080b01034030541d108840d1413a8000c944c2c0c01c1d01c10960355050361516442c00d44412508000b003000420f01000b0301249039181c054007150500b00000d000111001580c1080302c04610181200540903 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 988049640 1250 988048390 988048403
    0x307030308060120061608071d040e1c17090d0f08041b030311011103041e1a010306050a0b04150603050705040e04050c0f011815120203070206090c1008061c 69
    0xa02c4d120386c0c45815440001d59010116542e0404900c1c03452290f004481600b03460540100f4010184c0c062000600186112980703d0044402c40a2440c180c2140d48512256503500c180035062100390507881a40e01820b5001307240e100300d07407803600d182c1c0088500c0b002410b00e040a0510ba0354504101c0754000c0f94100000003000300301804410550400c840f43d08400b501802004440b00c45c024074070441c0300a440c09031240310034684041e82c030490307000026103083c401c0350781c0801b02c04503400c042e0304c00c1020380003214219251010080074078001e10601c001e40784100c4041c07000702158840280240e10038001c01003015159800620100c0c0100200e0700100b5402444207880c0c501801c0c01e42d110038082c0e00643c800d100c4254121042e40c03041420b802552044141480d1482c0b030030040785e090055881000003840311a40e62030a40d9003451019603c9001150007804062070150036681c00c1c00e142003000342c4604102e845040307241d50320219955100005660a40b0700d0384c66070301c0410030076031224401040f6 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 988050890 1250 988049640 988049653
    0x90c0109030c1a0d0212091b0d2d0609031d33070302010203041b0e01090c090504020423120d1209020a15090803030f0a0b010c050115140307030308060120 68
    0x2401c0440d807940340320305010340a451503112440d403680c07402c150300b405d02a400000d030380d00e249c0451720f4100c00d000d10241b20160801707035882490b0300200d00381000c0f20988442d0f0b982c2507080149504201242121700d0308621303010705096003000140610303d4050642601c2d40c20a009000d2511404000c41a0780022040c0e1944460080c60004d01035442114111380b00e40580310340340d41c03118413900d058081d250b10b600b00c1d01080e82802802c1000740801d85605003000b0000c080000c81d07031540d200a001401081418004803601c01c03040c0174403154182c80b079602840c5003440131217454401280f00c030020856071a040511440421a620242a00b007101039400b440c22100018031306070300741c2610b488041d2a01c507410016580e002658076400100d50403a510141540021001c0b102503101d4451f0345414145421184110345075282107600030105401c18118259003841a5601e200480d088160103d0040c00214210342e00289009400782040e8184004000140000009500c011503105401030481c6e14 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 988052140 1250 988050890 988050907
    0x150201110f13051f0f0e0a0905041b03030f0f0207051c0302150606030601030519090501020307110c060702040506130e03091305041208060402040914090c0109030c1a0d02 75
    0x350b0000455084455000400140c60f0401c2c0c101280c1308040c0c040da4001d14514144282d03500d00300c9165280401990701d10324030f80d41c2d64407960b20300504503044e400035043c9058500b20030b800044500083c040d4540010400c00a41c0c0301c2000500c040051074802020031410800343e1408480b034104546c0404a002441c044003042500d003540280a0b9084610802e11050001600081904c3c0c0e42e07000382d01080001c2e9554002d42000340c100703841c2082e6401030800070030840d080f100e40350021145030f50000280f002c4158866107214090700e607c806488100c106900140040c856128000d014540b80c200007a5190f44140391203030b14000d004c0c801c0c0005015543c009850383d000d46c50b410700c81c64040081050701c04040c49002e203d59030144017200407481c1840b0691b07101e1401009203902a401300804102c00c040c80c01400b0804000e0000f0002ea824841c2c14281010004c4006904000310050b0400223341901314040c211584003130447d108800c66007405c5441d108401d21020064000202d103403 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 988053390 1250 988052140 988052167
    0x61104090221130807110d12020f0105011707180207150903140309030a081b130503060601110613050307080418051b07080f0d0608101b0915020111 65
    0x9282c510419410b1a42c2d4003100c000b650150741c1e10240558206110349800210031b41a079007868a00104100340101c8159038440c070646404100c00b0058004c050070f15811402401864003500b210035075800e210025002040d980d00c0c0c03030f00c900204054102c42c1340c00729080c140e048800d0541c000e84d461101c4041101b001001c2c0c40503003c1100028011000501d410004d00705807400f0b003c400c00514a440e1005d041147d00302ca0241142001c4060130781b00c080381c2c000080081001d80074540344403120600d040304040c1000401420b0764188142c0c1c220309040f101000c50003540c80003030b15a0b1a844040b0504015140d405400c60045c00e8980025001c1401003803030a995040403031240c003c0c07009035140c642c2031003105a020320310240031400f4004200024450301c06001b9005034400450706103a1025003000580346642e01c60b21668111400b6580990a14058404114001500d011a0300c408100060030031850b07100310503003e0074401410002230320039086003440707203003400c180340c1c40c0e169004090707 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 988054640 1250 988053390 988053427
    0x306130f0c0506280f0f0c0309090203180105010909020a2c1503010506181b070503181002030301050a0b07080706110a0306090618180501231e040611040902 69
    0x500034010345800f0400c60361080100d00c5d0003030040c0e568955045844d041c156490103110f030084050014501c004900c44001d44041c6100e0a1540360240307820140d42103580c01c403841a00300c4440c43e81040300300405622003d082c0d80031203a040a45e0001101ea080505a44690004401d10307241d0007003003884a24090420500c91514048008110980355582003080404250205a00c3c1d10440c0002900b0075041d00d220091030480050b507a441c181e100d646843c1554001d40501030102006a41240603081480d00300c8100c07090340c0000c40c03455041c0760018240c0e03130f83c034418001e40650015a400c200030303401c0c0c1604c00c11035210313800788211481059141e40301c0d000321030110000703482d180300010307000545e019003000c503800c142400d000902d0120350000a0042c048401a0070382003c5035500020b0000d00c02e1440721030382c1c44a510010303a6550700d00703610300c0340183c010041148001d81d98072203104a0310106070040d5210030002a01c4180d25103c181c01d00859200c01e800b80c0c40480c003a0080ca5016100 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 988055890 1250 988054640 988054687
    0x717040b0a0801030218071205090f030d02030403020105010b03010b03060907110307140f0d050d0e0c0d08120f060f01031509090503070506010b0a0c060b04091205090f0306130f0c0506 81
    0xe080f4010b81d05548003045000441d0248000341d00e40381c03d45030323010f0340c1e0f0301c410b0b080001c0d201075400403003885c9041c078a9940091844485280e0010401c02450703420310909000d844d58003542d07803455140124084041c0006044a445914000b021840e41d5014100c0100c440c40314409480d00c0304c51509151205d00745480b01242d02c0d004074550100b0780c000200c0c08480e400d640f926550f081502d000441d43c001d04008248541510070101c2520050740c0c0d02c4004603c0380c4c070035210940d039003140b8100000011800380202036800002410b015196840625001504200b03283c0000e654416288401c4004001d070b10103514a03140c00d01640070701502100821030030f4005c404a8070325903030700c40d900c0d610340c4584a80c7c100060780c4224590002200c5811600c003501c0020f001048409190f11a00c810034a03407110741d40481c0000480f14603506080d078007801c1c5807404a0180c2002d1800a4058840c402010001010691800b03803c10030400800c0207031018010241040c2c0d1a03054454503400b0090141c2007 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 988057140 1250 988055890 988055899
    0x11131802120d020d0e032514100e01230309010b030610120b09070b0414010f1110090203011112090601080d0c0f0312050a1a010903080717040b0a08010302 68
    0x4210401c00e000801d0b403007000c0c90341d00400c52038004d50f0044652810340403465605002c2c0d034013010700700c8820342c8541054080842c2e90180151525240c80204460700751000d008096012260007603a80000c001c0510f10800c4c01c0258030305c0d1003048052084480220780c2030071001d010050013800041548030144c10142501140d4264542d1040044802410301c5101180a4403540c010002000c0c0c034092070f00143c185040b80d140c1a02e0710050703000b642064115840c0540651998540b5603448054614038005904020002e140303502200740d26942c2241210103090b4071004001c0031034400b548034007204a840010300e625200400c0bc2d82034441800d403121052031003020000300f4440030110341d014109070f0fa07455419491180340d45000102c407051400740d0510110f40d454941c1c0642501402e486956031050010b52410f0220380005002000440030341008030050341400000e81501c201e03050300760000c14100903200c0210510b006486150003103103481030041986a581a0800702541c1a00e10858 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 988058390 1250 988057140 988057159
    0x100c02150103080d1d10090c0608100b0a1407050d0809030c0c0d03030b03150406061703030a090212120c01060902090f101407050303010311040e030711131802 70
    0x80310303280002000c2c00003801c080c004012480445800e03901840600f10751040c00111384c0d5107071054900307241d114040c1003481511070081804002001071080003034103c0317041205807030510015140440b040d5002d5102410400100c800e10240652040725540e03803850080d90395055546020354403028209060b0020403004004205464000b0040d20100c02e40c140081036545004400c10162102c0c00d401039040c1907450800803c40c0d2030a009002505810710071060705030405107004422a200e5a1010100100c40414281c5c566800300c100c0f500100f40309000325868035580002a01c9005440382c940781881600403184000004a001d4001b040f6424001c0081a036130329098801c1c2d00c19000c009a020340c0c801c0010302c0900d4000c1160400404520380445200103080c4c0500c604d178010702d002c3e5881d50000c8010010418000101c1c0003465003940c083c8080c240200e40c035070303480c00740c500028010076111108248a450b9010781c0700341c5045000c001d06c40d0400c030309011448080304410903401203441e40b = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 988059640 1250 988058390 988058413
    0x90806060604030f200d06020c0c0109120807140f0703110a050a17070305070b091207030f0b09030d0903120f1e0b04020909070503011e0302030a0303050c0c100c02 72
    0x8a0075201266008142d04024502c83d50392299440128613540c561002a000c0c00d0103030786c0f80e500401c408a0310400d0010394520541904514021424401c54100a007040c414440c000e0a020082c0d00a5030dc150007584030728207880c001540c83d040d04d107020540d01c1440c441c90b1603100001814030032a806241c141442030304c4803040c0856141c041c00b405800840c5442d0401814280f682907805000d5054180e42e011900c0e41e44940c140035955004006001c808100b04003a46040440480c01c15403180040041910f50b41e101d001003105c0410107801004140001a02c69809000711401e8005a0b801041030b12542d16001c1c01309a008000c05a6080c50580c500c032a6404074451201d100c07040e0088420994260307009100034114012425811079000d2202640e284c0781c070136202c0d00482d81a03d030140c8a43c102740040500007094004039032244800102000541c40100d50032765015014030340410700d90380d440072444940c0310b6031541018610801c918841400c01030361100c0d0b0b1000055007076490701c4110 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 988060890 1250 988059640 988059649
    0x11703030903120a02070516050a0b070b0a0c0519091701050603060612071a04090b0108040b07050703140706060924290705012a0203090f06040801020a09080606 71
    0x840d51000c955004000004582c0c8140f00250f510400718078004d4a404801e94669040002181e45107100b07603120541445070386800d820303850182c54411603080c20591207860701d00900f200642400c00d160795980703208200c64420004c440041580e00000c2d04a21103425006150300005d10540001800403602102858018000e4500405d0f0082c020a060303210b0340c0030081541e00d1102441117500c900180052880444c4800c00100c440d00c110a58030f4a280541e880d05030341c158500305040010100400001441c5941581d802c0b2529103002d40d22921a454107907002e4000c200e01c84e0083d880407909030204141900140203079500d0b10300501512564050580b0031081c103980285000030700400074805441040501d03040c420792041364032840400b000a0100c503510035130003600c46075101c0d52810011500e0390003000c2d46c10650813684144d0100c0010094903805400d07034080c800d00074003c400700c840d0b5a6405450103000604021995242c5a04c000f0781b181100f0b108441041c000d400000e815440c1 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 988062140 1250 988060890 988060897
    0x7081903020a03080a240807090e120c03070605090c040b241810050a0840050f0c09061005040315020c03042709120f03090218011703 59
    0x40c980c00034100100d0a035029600460000e101c6000d2964502010300026560785000c0c021052802c20b0b615100d0600b9800740c02c04107540c0004002c68107109449500400008200c0e54013036100d1292798039040c510000d00e086216250000d0605400c0c1420300c00303041300c046641c6490720b90442d8104514078005050240b0045001c043d00f0080c0c800d0700b09110000040d00003080f034070540703040b80d039180ca45c40c4e0006042d001c0704180c0c030400202e02141c03c007481a0071200e51070708240413144d20362601039414414560202a82914000030420b4031401d85002c201400101107281d0003001d80d030b07088017490001e035501c1000700c164900c80c02000b030110b03e45041c10601c00d0960301142c1ea03a149403c0c150385860769080b081109260790303590700308620074440a051000d0f0001c1e010002c0010310581241e07100d080d07071802c40c891030780b15540780010400000d507540102390a03004190404840c14504440c054004009604002e034114020110b030740e11a5950f69011816a003100710001200141d94140c143d8900 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 988063390 1250 988062140 988062143
    0x30b040e0606010e061303050109080a080a051303030b061215190311061605030d050109060b13060e01120f06061b08040317091819020f0301090207060617070819 71
    0x1e13200d02800070642488801449040100d8014034440c9640399035403403c40300d020405546981000c41c4800c55254003502068018000c20401e00c07035400c259039408070800302020000c041c19960310b0244141d0701c0f08029200340118200c102c4149103404c100050384100f0100205100c0c2405442c5001000030250a503000d03281c00c0307444010103540302d1082c007000b1390012049910b44548607004d10300080302000100b01c26283e00d14003203160351508140c41d0a89590360000d0540d1202845054942c04042407240210390a901e44420066040380c01070320360b0003085044140050421402140004140c0c1060b82115499656050441e10601d940e24042d01103040c01400d40608000c10030120f106201c480d5403403140036040d03600c0d016007280001c4192880800340c0c0040c840c103008002000f940c05034554441c50000905501e05450540401020301c03050040802d1603601041100600030103501040141903682c00e00302c0c80d2054400750680d6050380788603d0550740320301202030000790440c1141c1c1c800203 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 988064640 1250 988063390 988063397
    0x31104080c1203090603090c0405160e10030b12010902150307140c010b04050f04060507020610031b0902070f06050a060e0c03090a150e0705060a02120f0c0d030b040e060601 76
    0x40d072068100010782c581d0342c10510781c40c401400341c890756a54407401140500c5c0c2100c01442c003c02c00301c050005640004044001d035410303510300c0204540e0001311075401d0002c12900c180b103440b000603094004100c0703040c20503084090140f0b16100300d801540684802070086443e20003400007014001b811780f204540100001c0c6182621544030342030000546041041c5500210f01c005022002c14200c41702140c0c01c0d8507860880c010712040c40450301c5100c5c0c025100c7c0c07000d000b0500c0d00002e0700e07565646501c0300414101046a00d0401c1c1c0c126a00b42c4000783c980100305664400150030003140c018a040e4003560214076040115146484034410030040b2680310305290b14558500070098005d0b0801001928540a4042c0740e0002860144101c148005560720000e03181c164050020700d0120305400141c047d0b20108041044036400058044a00342c040c1c44041d51000e190300c20001034060a018150f1520601aa1100c141e170960411001c0f5017042c0c2c0d04100280a800256540d03203c21354615021 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 988065890 1250 988064640 988064653
    0x607230d020f031918030b0a0f0e0f0d0f0216030303021b0a0c0513140c031501032702060c070828021f0c0c0b070b161403250305040303110408 63
    0x65801004400003500307411480f94171079903030398a41d088507900c120346011100c0d46c0e0b02110200e9a50910460180d9403e490081c003d00382d411030402d5440d850600b0b000280091104485102c5208203c0040c14601a80c00344040c169245806000303500550903440170303040b82501c0c0e11142c16001a0031031700e2035085001e5071026487c00c001e000c410082100c0d0021981d07140c0300303250554409450703941e010f007400d40a0507550b0f01c0c162004905065440c401e82e4101403c1101d496014003400d052840d41c030a41c5406001e070202188001155032260490f880068021400d00080d00c50010580b00d03946154800c00c07060804250450079414041d810303000f580400544141c614661041d0880002007071941056481d0310690f894500c845c000c00da10002602c0000074512007003015075800705400600124580c0b02c019070368500034007400240906044900000300000710540246040465a4035140d104900c40f029139010041c05444200d4080e80441e04012540303114119210485d801c50780524080c104 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 988067140 1250 988065890 988065937
    0xc051807050d06121518080904050901020721030606090312031d0307060605030706090302030a08250f021519030908040f0e07030f020f07020607230d020f03 69
    0x1d07150002100d80308260342d90072000c94103c4080d601c070461580030384429003c1c2080c1c030300b00109480d100d44c240401071150580c148005001d0006448840400b1500443d40741d03104080c09009004a0b44098103101d100203014100407902080c0a0340c0c130003e44c2e0203204ea1520303003130260382d017901c1484000c10700d8074186089184a4440e500c240b080c0005a00c0211920891115003803668020301c500751803c41d44c40b101007000e0f10301000598014a16410220081441c64000945502c09208068a0080b00082c0c003c5031081040b000a035030920765201c00200703000d0b41040c040c90858060100d004a1245070290680325a40082c0c4008803c2841c0b003c20b21020220210003402e003408080302d10300c20601000c070712001c2021080005d0491100c501c607283c64142c3d401025220924070040015104108404c181da2050013100c3e00d03175030103442e1141d45015501e081c50b24500040c0b00040002c500500c00c004244010031034000300c0c0c80381d500b1502c05d14040c042c02c0c2d440e445820000b0108140c02840b011 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 988068390 1250 988067140 988067147
    0x140403050c010609062115020f03150a030f02060721030e0c030f0c010c031b0f02032b260109141608072d020d0f080f150a080609010b1503090c09060409140a0c051807 73
    0x160041c03003813600305480c2c0c0b200c03144b0038891403002c000e20300031075150f241380405588100607803020301c0c500303c0007840d100c0117014145458814500402d410054607103100002d15000c0c0c503d10f442c7c202e100c80c0d501030304140b60410040e10043d10808921034011019004101c4950340c85054824802112842802d0540502500c00d5071a4806000b5403048201219414280160074140205405040030620380346c207800c6114107841c02402404100000b540403013400b503201d40f12903409495800c044000b401d4401c8040140ca10010032150824107155069245a5001c07800a80c07410380c64507400d65400700d001e0162142c0300c0889104a50100d8040083d810950102d1b241071101c40141c006c0381102d85409002d820312000f1103008510744e440f1619501c450030415082c0c000c01c41601d40d01800e600b01010983e4840c2c80c09801035124801c0103020070400d070f90300c3d8001c0c0b2103190f0204203403031403e030103903050b0b0344400b2400d2042c0d864150030324000455040242c04640034560741c0c10700e418560399000060707 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 988069640 1250 988068390 988068397
    0xa1202130b090310051303080705040b180a03080c0c0102160509041104020f1605060604090308060409050f01060e0618040302060c0d140403050c010609062115020f03150a030f0206 79
    0x141c0e4540308484c0c0d050080e40251003070b28015100c1340c000c90000c101300c0c180540317650006401c00742080780070803041000c8200710781130390500d4080310039a11005000ba400031700700e170490f5040500862400550304250007000a4400c2401d202038080e01e00e41c0391150100d50300013640c4d1040b2a0031070312940010300000e0700e0712100d06440c0c0c0700410042c100448046100300c59040900c05c0c840101c1c00200400c20710030100404c3e0780c003e004840a204040c1d450703070300502d09140075214601981c6c507204d05030100300c1c06002059441003450000c00c0042ea8a00d14540e01000c2038a03198080c040c0e02071448841950361404070310130358044e00181400c0d1100b003100d0300e142e400a6040001e050f07554001c1e80c110581544110b006074080c0c1c1c4c0386601c84200068050031140e113a448181868038010341040302100d9100e000c661102e010f00c0c9100490420f05040c402404640001c0ea1090310004004913102450030181d40540ca2072200c44515080d8941401900e50032400050f1040c0481141c0a0040c075003103004 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 988070890 1250 988069640 988069657
    0xc20030c04021303143a030e0f030a0905040b030c011b030c0b0a05040b060d0201020c0d020a090608010606091202010c060f02160305030601230301150908120a1202130b 74
    0xe0003e40c0d50380d1244186280c0422445210b60008005e001c072a0813000c0400144801140441c102140c0101101611818100c500c038145600c420300c59840e41c1080c440c10390b446e4020340507280d0f00c43c10210001c0100006d4000c0b140f1840c0b5182c0b124525050002c2c0c071000080043c0c41703844402c01804004021554100411003c01c01400082d00000744042c0d4200e000351070500011039141094500081d50b9000244598000c002c85c2c0d2010740941e0380003940480a81054965403014850b500109039038000c0c40c0c03c21114203040c40000565050705500050451306542c1c2c80803001ca0b2103101247c0054000800a800180740e49006801f14100d54407181451000b441d0040c40c01500610340b1080211540d81500810700100802c045542c00c490b5203824100160707440c0070301201d090f54140341408103020b5400d100f0110041c041070140030300350013000303040a1000c41300c6401d140000145180c1c8a02142000a030740c52a50b05c3d00f41c100b5000f03840c5013500d40310980c02400d041c070f0710400a94001994 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 988072140 1250 988070890 988070917
    0x3010e15030f10050a0501091509020a050c0303090f0c102304080d09090e0f0a0605090102130e010501033602011e0503010914070c0303150e070c20030c0402 69
    0x705440c1902d040100018550111401044e02c4ca0104110011140164020802c550502101d20400c0300c5d028806810b4810000b001a01c0b44021a021a850300800703240341128400001481030300100020303445a0410340504507840c82d4032000c24045259094414240801c01c1003117201d120070340c107110062040e281401c5d030a003002c4e1358641a900c2d0010000ba01c9000c0b45190409001c83d034568011610f07411622001001030450101d551a91441442c0014200594810106000302d1080d0101c52130410500900340c1744945881c045903006800f0310400340841d20f040d412018044800c2c011006003088001ea12001150310b005c41000208000022070400080070b83c1d400d00501188810302a400d210341e555501c0c2c3d0704103000e04040301c0c4035907c2ca61910300e10300304012810b94088028800342e82d05140200300104424001c010154040d002310f005290000d08001000da03000c007094071042c1c098401c640c1c40040300d0b18042c912403242c11015801d070b000f00340c4101c45410250010300011150b20f0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 988073390 1250 988072140 988072153
    0xc071e0e04150c050a080901020406120b0a1203120b090f06121e0109021203040e0c0c1c03050718030209070c17210a050606030f090a0b0c0405031203010e1503 70
    0xa5003031080303410080080c40404c0020a0f02043d16500040f03260f4400705ca60021132403c0c0c24580050006848030410700c080d00c0c0c60350290308407905e0f1900c050004005940e020a003200241c0b601904901d102c56851008034030380b40c2d00072624039041d55000e008a010760080c0541d6211002401210402d81451032041c0c800c0c940e0034483e0146015103441c0e801401000081c8510092040100701d015000c206500d540c000d100c05c3c41110001824582c120703194802c81903480498035075403405c00303489000032444a090010f002d44400c4e0103402040c401d68041d035039071001a52144090301070740d80303030301001c1e4120b060342d40000d4526018412143e5128012014140c180c10b1000d061104e550000020042103115500c0801405215002a603004200c82100303002500e0070307402081150200a08580319121401c020480004040c400d41102c290041c05148103881e1800007484154020300c44c82d400382c89840c0076250140100002e8a040e501003000f901e10030f0b07c0e40f080b0890f4041010b601d10f81d0500800 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 988074640 1250 988073390 988073423
    0x30215091f090605070c0e04020316080c09090d02072319050306012301120b09071716020a020906030f0a140d050702010e1509040603080c071e0e04 65
    0x544441000c03041854880d2440140558010203840d0154800f0082c0241030000100140c02421a10159503600000d1540ba40d2039000091600c0c55400580880b80c03220700c40440c00e9103010440e586a1401a520544192110100385548803200c030721a50040c1c100c2d5505104010800b4006602c00070480a821450000000003441c55241c03a18400503c50f0059000c00072810b060140320700510320606844140680d4400442e103185184a61034108102c0718003000240c80e5039440740b00244c4000d0309944031803801c0c210103002490407a6010b401300d016000014480d1400221000d0840c5c91a80030b051822840d03428040910320180045e41e06000e12148c4946040d401c005031100640942008074000018608540c14460304170210707810072a0030440800541d8100903080901d20b0260303418900c40c0864441c18445000b089040740d40035081600c00010702c1720103000b800850180c0c400703854100b560b54021488103500078020b21000c802d10b0804000040c08032008552080c0100b00901010344803 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 988075890 1250 988074640 988074649
    0xc0618040b121e010f090210050a02011407020303040c05030d05070b0a0b04020712030b0a0e010618150f120902150703020a06090c030b2a1b010609140c1303021509 72
    0x3c0b001e803103224140c2441d042103031800d00038481181c5400504119510503030b004904a1070342480c48500744040040c0d607050321403007584508000c000c1070340d10150717908090314000e44a900c180c03400c1d5011b041c07403000460b5510300400d1440b00d0780c506403641d91400c9620390301d003440d0200003000320f40100c1c8d0b200100765040e21940010060070b0300c0392250040c5c0b09000440902218a059071b01401200309040c00d220251620f44406d06640d036908100c0341820b103c1810035070008031a0400001c1d150800615032109401540e1844081107039102d818030b580c04902ca400484d240b854020354031003482d210402100303803104000d09e140c83c000d1040d01d101c40c5860b01c400095603c0c40e0000ca03080f007800074040040c00440008140c00090540000182c2c101800f80c110920a401d01035108100c03000810105a00714000101c1220300040c00a02405075540b8030107008000c0c2d40540030203a00950000f074280b07030650045847c4404071441c2600d1641c1181c090210302c030b810f0300700084482d02c00c0006001c1d540e40d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 988077140 1250 988075890 988075903
    0xb1f1a07080d02130f03030801050433051018031403040e10051002061b0309012304060c0f120b04061206091e030c0b091c050301080c0618040b12 64
    0x1110900541e981243d04c0042083e02d00507031102405c0800d6940920000754080c1003641104d100300c3c1d000c030300c00211b06e4602c1011514014401c8130490010014118040480469400c50340c044501e50820600300c07400360f80100019406990b2080303140c200380005032100303145655000c40038003100d090a4036407850f5a0298000c0d0780600c8400a0883c04001e54901028409a0014148040c0480713080189842d01e810300400000030528038040001055a00258042062240760034032240300c1003c1c104450404800c2030b60182d0342c2609000704010031070300a100c9251500e81c0c5684203035005d46a55a00001444c40030000d030b5015894800000d10441078400d0044203034000d10002509d1511803502c1f00404003420014000140c00d0100b540100f500140814201030300310342080c50036a05c03401300314100644600050301404806801d11581a48031b0082c3d4107859281c801c0784c08042c0c1410400070301e03000340c2d00320041c940d00303440c03806609042039048048825000fa029401c1704041040c468209032 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 988078390 1250 988077140 988077157
    0x30807080c071710060b180310110310170d0518040f0c02010c020c0a1205070528060c02061b011e090506010e0c070206030c0909010608040b1f1a0708 66
    0x4403c02c883d604010b01407281025400c1852000c0080c0c03458a10200194040c904401c040d014180846000540302401004400f0380000d404004c0c101c40c960300400720f500143d81d984248650766001040792140460b05420010914004007041c66031120116a01c3c2d0110304620300b503007008002484240c507140a0042f00e03104284000c20400c08900009086030092a42c0d08210360001e00d2800d02c50b1500c042e0901650f0f1a540ea0740c44500060504a14282165001301d4201999001c80420700c003856001400b03428561168062503590f400d0104e07034200b507991000c0e500c500c00300001d0114400084070150f0340d007641000400c1c02e40400702100311921b138a40050300341035107650385041000424468140502841100c510705420410340c401268042c1d004028000c503030010108540c0300418060362410200104040d81c3c03585c552000901108003503c040b1405049000420003480c007007a140e80d00d26612540b402c085a182006d050882400346047c803121440030072442c07000c507803100020441e03070 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 988079640 1250 988078390 988078409
    0x105100b0a05040f03290105090a0c0504051009231507020f09070f0207050d0c0b07030c061a01120b030606040507050c0a1103060105030a11061c02030f01030605090f0601030807080c07 81
    0x601c030310b0000511960946e503041d210034490001809240c0c0c0e405000f50300b05c0c49480c0300003035001401c0d0b800d440e40d01c500e42187da402084458400d501661120b074080c241c2d4215052074004083d107042c3c0e44500c0c40390008255002c8d02440e040780416000074090f0000f1030008220f0228001b08001080c68404203650404c0080c3e41032043c0c81c94a501088010000c0005541300c103003400240d01c0d221405c0c1a68025150484000507400c0245031044a00c2d06095400040401881804101d80d14580030691006400b00ba00c9109510386403d0310711a0084500028002d005aa030303800007004010003004040c201400018002c030610040204400803080d03102c1d0400d001c007040c80c041014600081644400d21951085072a540007851007030f20700005000030380d2916121007080020144483d40400343c40000e80c40802044003202c4c91030400b41c1280d006a404101d25295501e26039180c044e0044004005e50150004200045520b0010b02d80306019100312410149291a11401c010081c0d000d113162 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 988080890 1250 988079640 988079663
    0x150507060b041806050f1e0103020402030a1506050702031002091c240207050105060307060f140715050f0a061d0a1d060118090309170114010906170105100b0a05040f03 74
    0x94610106051f00f10386560224010000403e07003401c030308081400000d01903038012021a011503041c6c0c020000c81300002c8840000c2d2911844010101d0300b0101e0140e1080c410607510144104e01c40c0f00320f071404e080150408004a81204008840c805140d00423a5012503020700c40f00d20040301c07002082d80000440002d0f07950203446c10700d1401e40380d000c0c04440c0300b0b030040d800405c9002e8010084104900c0e10381003d444031040e2003090f203642d00076098050321141c031003200301e828009503600c01c2d48100741c0c0c2008400d054a070410100201c54440c00750358000c4a6545400751640780390b4060540c800d0b0202008036040300c2040880c541070030101d220700c04641c00640107001200d150707540c6801880003100c0402044c0c4403134a000b407030b580203032081c0b44100c4a0303e11034154074031087d0806110344500d1441016196500d404a9000300413610038501920141d04020802d66418060180152101280103104a0400101c3c0d030655200d1408182807240c20440005d0f0045000f001c2c1e40198080e0008150 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 988082140 1250 988080890 988080901
    0x3090b130e010b090904020d21080406050f090d030e0a0213021215031b120109080c2401090b01110604050109030809010203100317040902130609150507060b04180605 73
    0x7110340341a001a10810818000301480f910354841c0580d1143c1c040307a86102c203075034505221100001d03030300c04c4054100103010500800341e0840320140c022886050204850b94603d80701c1c00c3e07110001d4403000c4050b00603404500031948690410328104001d40f0039104840215400190400c4002d00040107490300840c480481c10244481d40b584040c0e00907074125a03071001d5000a854074100003a181014855040c0ca00700c40d11640b06c0d40703141d9148100200815251400c00084941020724080c04522a4449204036a040054040042c86c400281d600d046c2e400c15820102030010700340c040d41042088258030307140700760030890a80100d0041c00006291509800c0007410b10200500011941e07004000f8002c0b0050f4103801c07603040343c0e00f0000c400759000800b5210305003440f540d44075030510740c004141700020600201100b01207850545510085035528580c074154951903801c0c07040414400d11140f00402c0d01030b004049004001480082c8030135001200030405000c00005540707a5903a0003c000 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 988083390 1250 988082140 988082159
    0x7021e0f15131b0312030b03010b010e0102120d18080d0c260a0b041406090109091e0c0e0a09020a081606031a120f011b120903090b13 59
    0x184103042079100c0d400c151405044507076420007034080c020032003244040c515201400701c00b0480b0185902c400e2082101c05250001000b0f0522408441d00c20752802a0031845903000d40d0b00030700004410f0b005028200c2d081001117103640c2103e00d030b50386080c1e00e030422401c80301441c80a284000d445203240c1d1740c4840c3c02102d500125855040b000d001d01000c503054003c0201c0308071414140380c9103941c00805a50b41c6251050181100300e82083e0031504189454050900642009114190544003039403d682d8504000d0141e41690101800940300e09405460401c46204000121801442015850341c0c3d20414218112030841c0d0554803c2e90b540201004c514100d11403400801c4407800800e00e11101c208450040c0d00340d44549001d01d607a408001e00c07040c04200d0002058040181240d8214101118081c1c40300091111000c03030707501c0c02074108071010184020902c1303220346aa41c00215031000030500010501284182c0901c140b842000500b104400000c06034108204941c1f08414038204009 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 988084640 1250 988083390 988083403
    0xd08190203090a0504020d060e010906170a0308060d051507080f0603010606050906090409021201230106020c0108090a05010f290303072901060f0e1903030807021e0f 73
    0x58045400030409544203546043e254419a03004a40050745c1741484080740f801083c41d54800708003621340380000220b5400f50391108040b2050359182c800f17070015660640c0d803500c0503107000a01280c00d01002c2107560400504d58001075101c0c0c1c3c00c4944500500c00341070340200c4120b03103080c0050b098a0810221b00910a00607410003026402404444d0030300740080c00034042e07600024000e07000803800d401256155000140d1087c0c010300307041340340c0103441007050191002080713000b810340400c3c0c4000e024000c518003ca048564a9020b41141100b1400459015001401034402c0e407090300041c101050082c032640d20b80910413a0000b0700c0c561481d40050007645003044070066007511155032615074802008540041d070f8070500ca40c210040065031482882205504074018841f00c1c0004940b041d04140c5841107043d403502c42840d21103182080000c20310308a0b0401c11701c0c2510040802c0003a014000c1582c00423079a0055503510081c01e101c80d03202ca408010860380d65445480d040300700300400d2200 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 988085890 1250 988084640 988084687
    0x1303030f0203032503060f03060b0103150b0d0f09020916110304030c090b03030c060a020a0905090105030d0e0604091503060c02030406020304061b0206031e070e100c0507050d08 78
    0x30b07505500d00300d00d0149002802d40e10101c080c1e000d8000020840d0320030345c01800549110304081000030340f00d0401d040106014406617001c203290500600c0340a0100c0e1400c001c440840c10358900e00310541c071043c8064984070304040721311511441e1040044c0d071034507c0f0901c00c1c520303215100340c10705104070001c00b401d80801c80184660410003041c000308221400940c00c0c1c440105000c50340501c0310307001c2031851113080030a0f032940c044c440501c141c100da582c000317003012900d0747c1e6500c10103070301c8004000c1070180c00e204081e416440f180680380c490b4001e818028948070000c20160800740c9c2c52454070291000c000c04481c810072245000c2c0308004103440b911611000c1840254140b60410502035a2440396000e040240074200b02c0d155112400010140300c0c59034045c007029101d0500c10070041041c01a048408401244a40080c80075846007040c40c0b41880020007103003280248a03070a8940d4030110380103581600800740d02041684038105075800103132144242c00c1c2d81d518110400c0b1940c0c001842c1 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 988087140 1250 988085890 988085893
    0x906020715050a0c1d150307050c0c03010c1713050111090411090d0201200106090501060f0c200f0a0303081f08070b2a0d0908030304080d021605031303030f02 70
    0xaa0943d4540e00143c000302d0317140000300c8131580b50301e02030000e00c80741d00441c004005400c0010070014540c1d07020b8040e00070709401c4c400b00c030560311140c0205401d83e2505501c08000909180513854803107051410756030860b00042d502e16100959031107043c01c1d01d10071004440704a4000940d06031a0134244148441e801420709103600301031880e0001f0b61480c4020101030304024103000001c0046ca41c4400c0b10120014a000070401566200b5100d00948003d00c078180225891442682c0f100e4040d80c4030b000c64550180d660459100051280c402080e040701d80c8036040b90200f40e10030002c0c0c1b204800700c0040c41c0a03807104422407030882c008042003102021032402c01c22115004000384c00300000c04906841e107880c4069219100500c2c40d944c001001c1c426401035840503040c3c28442000458002e901c12081e0340d809034140e841d041034640e01c1c0b20681d4000d0a4000411104260300c80680c0a48200392512508000d10550394444030b285400144505200070404841001010b4201c40800b18001aa00 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 988088390 1250 988087140 988087151
    0x3091f050c2a0108040b0f09030f070c030b070f020c0603070e041113230103110d050709090f1a1c12120605090c09040c020f0a080c0d0206011203030209040906020715050a 75
    0x1b03403411440c00b4046c01c40120084011b0115001c2c14051050b550030310603103602c03607031110142d003000d0364260b40c5440240e6100e0100c2d40419481449000ca03801d1403507003500103008010519061012541c03000304850100101048042d01e550754501402c2484000302800d6500d03043c1d00281072210401981c0100c1450340003c1d203c003295180039330740e12840340090030002003420b8504100c01c00780c461404840040341c40d0104120181b0b40024550051300d00000d02049508000020102210080410800e03449a0007103030a0321450b0101c2112000740c031020348680701101c5a80d9560f00c00c04480411008901058141c107400c0c505031140b00b0090030122a0030141d0b05201d0318040e02440342e49405401503440350500c0c10000e0003045101416401501283c0d610141800c0107075854100c81c400c10814060740241030201031001417054141c9a000111403400d06195406070020340c0b04403801900103449143c5040410428409003d03500d001d04503a480d11a00707001c540c002c0b1400200150203c0b407608 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 988089640 1250 988088390 988088393
    0x1d0a111302040e01180228030b09010e0a1401230301060e0c07030e09070c0204230a1505030703021c061b0914030106030c05060a030b10050909070203091f050c2a010804 74
    0x2c00f647c2e03100b203d01400c05501706092940440c00b505001c401075802001800001501544000310f081c0309100302c8000304080055000c80308003034074083c071407507104880c40e010030080300303012a030281c0c0900c83c014000100c8594400100948900842d800b02c15507001180c14000c0c0358006c3c003050007411080b2018485441c0410018000300126803020f0f00459407145006c100007040c50382e1651110442018101c0c0385001c60a0701c020301141404940c40000d49400021581000203140f07096903801810060203503c030040345900329004140076205651200c4c00c0c00200c000d601038019900c3c1c55680d801080c0d500302900d241c8440825001c45029a240c0030707003013000c100d03621314030401c1e60000c43d02d02d83e89903a210012809001600e00e00c5a0100746a0103100c840c2d9040401802d80c1d0905a070400c8083e994a034050ba100e02504101c03e800c0104c03118032040c5000d2240343d0850240d001c0c200103050003041c0981f07610b40b1680600320450715054814400c051310100588881030074003440e00d04000d1816 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 988090890 1250 988089640 988089667
    0x90903030c031b130306150f051f1701030f120f0207091d03040905270a0305070c17010507030f020a1409010c1e02041d0a111302040e011802 62
    0xc01e07506620b40d4902c8550000e00804003101c00190002d07070084c04580e00c0303003001401060b0000307140764020305240c4001050107404500c1021184d00904002c082e800c030507440c90f411041c580c1041c040214415007d20a0030b029100c0b24003070340c01907650703d00310741007483c000d00000d24880d909401d01450754648054180e0004001082e40d071100004a244900310403492160030034070342c070000e0902000c5030100707030b101c480e40c016440b44103c840030144804480981d54908000684146040c1e00002000c0000c03c4c064030040ca009441882c960094594640c0680c0d100c2d2001050a4401e94441d028003010581c540144492361064450452814140c202c01038010f0000f035210100b1038001045d01d110316070191062032a46500500500360454400d01a4403032a044420100e206d14900b46030403007c03460b802e0a500f01700c40d44800034801d0500f552201441100e51220b2a6408010141260b17100501030014100402200c00002c1280d41001800c1184a40c0d8500d1134034014410300040240020 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 988092140 1250 988090890 988090897
    0x80c09091e011508010e0d050a0c0303050c1314040506010f0c0f060b03060403170c0703140304060b0411040515030f0c31060e0103050411010311071a0402090903030c 73
    0x81c001a18080c0301414107405080d40043c0c881503ca030900340041c0d094010340201c515103802c1810f0303a8141c0c424180c20746950150203082070005000c80e00450000c0e0080e8007054108400403d05410210141c0060583c6042c40e0000004180b401a0403c683d081500030541c018109027814080c03121101001072a0f126807110141203420324800180030701807658001010000c0144c00e849131307131405050103071112013800e40c2c040582c076036680000c0507610404295034030349905948103607011410095410081e0405082030b5202595101e0f00d00c0d140d030303a40c81520800c1d9004c030b8089464502d0b01c001c0010312032504c12a1240c80c28100100700ea80703050f00e07460a07403280b401801107440c1c03040b001c6040c8000c0d4141d04220310310b03013414006504030b107600d2031b903030341180c000d03640c1c981625189000450a03100c3c00c1d103004011401750b4140011640c001d8100c1c10550843d203802508152080c0c0b01c0b4001e04400c03032803c0e84542402c0e8103000660a001c0038080d070240c2a000210300c3c0d0308121021440b14803 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 988093390 1250 988092140 988092163
    0x924170712180506090705010f0f02030a031a2206090509030909090f120421380126030c0705040513150e010f2a200304080c0909 57
    0x940c0c42c401181c103003021110075400c0701c0d0400d0454039980b0300781c4009135543e00540182804078070600d03d964456842003968000ea9030090b07021714200b000711202034016042079443d540c3c4500c401d03403024100d61504581610107a05101c114280101200e002030201d0b0f00540100c1103150410081015800001007107a490740300540380350317840d5690b00000074181403401c3c1c08d81143c0d014041069a51b203007450090700998041c0000c0c608580c3c0034001d03075600100ca0540040900c035009044c0c4086110798920505122803c2c08c1c03039540d08442a00318090700800b42c20a40c1c0342d05000201d45010800d080000007031808810045203026000c11883d90790b210603200c0d552080e03442d0300000d400364802020604820b030f070000e800040300300489000340141c00d080300d0b1400c0940ca0400102c015070302c01e0151345500350190203541d81880408014017548194008102c060091800780d1300c69051041107441d1851101002440d15282000c18450038504040c283c544210720400c00d0210040c00820303d000d814 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 988094640 1250 988093390 988093427
    0x1b06070309031b0e010902090120100536190b0a0b0303040e0f07110d0909022503050c0d0914130f05011e1e1509241707 53
    0x420204801040c04046130004022411000300000c1c10807255000351560440980340c1c1144404140e00c10354411140041d01d54642c0c0c406000a601d09039564482604000c1d4110a0300721482d100f003103402c00e0054144a060080f0340c801c0511314404d002d02c0b14030204040350203031110880c030310746440012020207052080420f170380d40d001c1c01003650100115070003000800c100b1203a610b0000311301d1680440032181e800111b0b100a04440e102c0001048076a80700c5da060b15003841d01e40c14680c5820081d044000c5810321030480c51000c0324030150003840f409060b48203039946030740c40440403809400c0c04408a00f601c140b0588100134041c1c0104102000c030f00c50415100c0c490881d40e00c030705880240c064608560303200b61510001003510184082d076414143c50806904917119516054450842c03103030441e5070150303100c0020a200500c403402c06110f080030545000044e46440d690002112200e908090107129801903080d2842504516103d0700d001401c0c281650a1500c0d100c041c0035405280110070a4 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 988095890 1250 988094640 988094663
    0x30309120106031506050906030d021002070c030b0f04030f02061003020405070c0c1e0602060c040302040b0a0e0a020901200703170d11030406050907032a030501020c1b0607030903 79
    0xa0003400d5210b00001c60700000c844002001000d40318005050030300505000300d62140008a480c2800544500c180d55a5070060501500d0044100d00039001500c04584407250b280d800000321315030700d008901408084145400c030741401c0c81c01500d0103814800810640d08060104480c0c0e01a18506070101e0750180d80100e015580d054040303031000a221401003526419413800315105201e40c180062245040c2c12000c0c2c0345480d40c1d01603a40342c40c1112a00c48a903010441403005080c1a00403504610000c0c0400c5030071520b81c00404005141256519500c80e0301151a03001581e01c8034007a03401000c0c58004035003c0030310110850310b54a56000140141c10320540c485198502d140c22540d80c510384080402034044660f09200c4280c0c415507040d0340541c00c04000c02c100c0b56020030044201d0343e100907219030300890121952001d40c0004483d204002512900002090080c00281440071000b00540107540c80b00c0807001500910300c02145c040d180500540340002d0300721450f50240c170b030068080045e = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 988097140 1250 988095890 988095919
    0x3051e1905030313210309030305090313050d03032d0c050319050c0c1e01050106090b03040b060d02120c01091703090105070204020d020c0304060924210c090e0f06030309 75
    0xa15a0301210f0110b10080300700085c3d029415803061035800c2c801c0d6014851510384060341d541d40c0c01240078503c0e0880094208000a02d4100c101c2e0344028400e0502207849241807c1d03406a840b580e029825804070303046210140d6910610030b406061410703061041c1141000b540080c1d900e1034402d40407810b6643c0303001240740c000714801501c1021403807a049414080e00d140001c1440c00030f80664480e2582064004191180a10b5201d000d50b503691820700c1c19541d8684a021882001502e095041510038841001685a4501280c54184000000c058040d9040001003401221342d0007015406548513030321080c0d00002c03003100d212540928003280c880400d0b00000380244140d26645030454400074080243e218044044e00440d49151102d500702c60360307070198003001031000b0690700c07248040403030410300e1a01425114030845200750411081c807003031445000456617100c500034003180f9020010001c00400d0344e03910f6400300d0607a01d0300d0a5400e14201007640c0f03000303800442d4800c40d04801c460341c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 988098390 1250 988097140 988097153
    0x1060506160b04051c030212010e01032105091f0813050601062a0b090708030a0e01050d0f09060e0c1206010b09030f1f0b010c020a05040203090703051e1905030313 72
    0x20b54204d01c17011091900c0c400ca48001e4025404007000451040c645400024084000f203a03841c120390300700302d5010019440c8dd50019000d00c1c045c5070f01c0c045c04810710081a064035004a400e55000b5590100f0580740120728001d001c10078010142c6010003040c240c0400003c4011440d41c0c11505035090455040c0900c85019a50b0513017414100b00305170280c0a00f01c280301e002c254031409011910107a450b8151115501c9840e8403820802d030001c15446807900e015948100002c1152004c91780c00010500c00503401041034444c075820544603244c444645000999040c003814030b92880c122104603c40742c21003c200d840300e405209101c8411000700c0c9064041d2400d1003050003454844042e142014132026004400c5a5804c282c00903007131070616040364550061000105160f00184507041503480c18007040041d61004100e003041d4095a0740002c000f07402000741060400306016401d030f1080801540c540ba084107118051240c001856050010403001700c02c480e04840c403007085002c070184a08182 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 988099640 1250 988098390 988098403
    0xc070213051503061003140a0803010b16150b0a062307060b03060a060e0606031e040203031608040e0916140f0a0e06040c23070f0c030b040501060506160b0405 70
    0x841d0540108403c2040c0b030300300c5c81700441c207891007000c2104000e822044032598410082c0f40040c20900b081006101c1c0401090183c26030101e155a80c50141120b940c5c0c5185008805c00c028007240c0e01d81c80252010b00d040082540038107038601e85a61140e07a018a070101c0002914809100083d00040e008280140b54110409240d8061f088032940d040014911006107594801c0441c004e02c1c0002040e41c500d407a00071039003c0c9904c950540c950142071358016000020141c000c0381d140c407003001020f0303d90440c0f1801000302801111415120303803a00c0e2954501150003410300b800c50b08030004c0440c4018200c04490180e8024030140c0041000d15000303e400043c0c0112440e0740107104040c0020b03000400281c0510a1001390707014004168a140141c0d51004030748060355200c03030f8a00036812081003c0000d048002e000d01e100100c901500e0302c501600010342c0c0c100b503884a140d041004280442405014010802914001d00c0d0403110b07055110401d1030300b00010200d4560a0110b0244001000103 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 988100890 1250 988099640 988099681
    0x130b040902150a090b1315020c1513090e1c0302041a032502340e0414070e0708130c0b030604140c0f1c0507090303080c07021305 57
    0x468204072801004810f0700410941c400184030002c01103648084481941c5200740d10000e600480703070a006c00c070980540d030500f0a07400c51080395046c03020380d501e0070b40c0350030301b05c100c6400300c0c0d60780c1154900105100883c1c1c000380d05082c204030307511010340c40000c0d48024240300910118824031580c28118082d01c00c0368004c00305100d45506142400c040310b402507029041e441400450035000103c0503c90000d06810000941c00c500414070680780744508141ca100800062036100060502c44600d102a41c0c0c0c020b42d844401e43c0081008002006410381c2c0d8000c28038005002940c40c00c064426204002000c11041020401c00308128403221030345806041d900c00e82040c50a078a4103800030540c0c1044403174030720483c102080340d060319903615209802402c5441c203681ca007400c04a141c000307960001c0403142c02c4001c2040d0810702000b551050600035880f9640380303a4031525604000309601d030050008000b280e010801c103001070351840310b00c0341502e40c0841c010425656148100c0f03c8004030480 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 988102140 1250 988100890 988100899
    0xc300a02120a030b0f1c060c030e0f0a1b0f0b0a050d0509010902091005010e0904020319110102102d1118132d150605070c06030506130b040902 63
    0x5003941c0564058009207401142170b1003001d440c2d9854820801c640f03180700d04601080b20248405408035106800c0395081105030305010516000f0070f1072a034603154114950507425040120800c0c01c0010051551752001070f86201003034854240b88101e100c0c1314180c49402032001c000107060040318011000d850304c19031086410003840c070705480214080c00550604034818140c003400920003581c08a0350b5800e945042e0b440c0560f2600040900c4044000604103903894482c16404200c0782d060800c000d81014820b00f10181d01a1009002a1070111103d0a218009052034101d005440d04d807034030618540c143d15810100c0d0140400c400004010822040c00c0c01d40c00000d4a41c00b041d01d40300200c4040b0401da130705228017007015910750308030303680c040144003c1d219950465407a00034146404d0709580720070000103020700700b898080c502c03000b141d445440841c40106418040c402c2003003000c1c00501140c20180002d2821500141c0e20004e2000c0c8019655950b055075111502d459102c0300c1213607070280 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 988103390 1250 988102140 988102147
    0x1f060c21020d02070b0c03040918060507020703050c010e0f010e01120509030a0207050f0306240d060b010e01020a050d11030f030c1b07050d14030903060c0c300a0212 73
    0x140e009440d01000704001d40540b1030f40c10001442c2031150708450b0940900406541810304020108014000000021081c06140740540005c503002d8490240282d1660700202005031a40c6069070034900c00d842c0c01170500002c5580d0b10801c1e203904011010880c424079242e080504078000580e0f580810b10701201c5014541001c020b040880080240700d950341c1c54084a50403a654410803409140c610649030b01070b00054041291500000c0b01502444082c0000080000080020428070ba00c140c001b80c407102e440742c008003c0c5503000078152401c61828409001d04880c00d4907070ba9602d42d82031002208000e41e4100d81c04c40c06409000f074910200c900990300307035039007442d15100c2d0850300107442c0c02d0004101c407501d0202d010000a29601242c0f00541040404c01503601c0d968449d002855800c4418003081100c41c0e001d40e020f0010510176000c090045d520352150340c503440d00c3c0c040c2c1c17503030b03c9050206001d91085118111402d95080304e08000841d540d1103003603420032410801060304c80b81c3c80750f0020 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 988104640 1250 988103390 988103453
    0x813060912050a4116080c010c0c03080a050406092c1302040615031d0619140703060311030a150c0306030c12030315150f0302130308030f1f060c 64
    0xa010700800c50001c600721003201c4103c0d80e0303905d40e0074030621450581303900c158141059940a10301c45001c19028403404007800713540761280b401f1a0700103800302d800a00000740c03d200c0c0d10b4021718204043e0564440f081c021010394003590388045014201c10000001a000140c0b840b188109a0032020398003a10030f0140940d06c9280441e48625492041c01007424618855414030110008400ea503024000505e82d40e203e25140c0d000000d1903000d00c5800c1900e034040c5110b5448003206141c043c601c56680007908514509020007070244c10084240b0070f0704510400310101b8200017a10300c0c80c1c0080307000001e10102244058004114a901c0240f0240d140c07000040c580318443e4040f14114040d40701032040a41c41984c0842c00c5045020700000304420011501c04d4900c9940003200c04a09810010b28200d04810600c81c11101580100c0303551000104001800d46150000c03500b0a4207590316030a0040c5005ca00303880e00b0454000c0800f0400466540d42c10301203100300c4107000a40c00d00d003030b90003104034 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 988105890 1250 988104640 988104743
    0xa0f050c0c1906061a040e090a0c1404020f0301123e041508030d1b0903060203070210052d010b032a070c050301051006091701090813060912050a 64
    0x640302c2d00c031301c0034421f0000996401001c11407a80d2a0341c02040d500c4040c3c28003070b854005102040b0100e400541c04c2c00414100450b00f4011030181c01c0301048031140d40601d203880740c1c51082e040c00341000360414800b40e0481c46600c40300f444280d402030804030964070a940200f001030299100c42c2c10308415014000543e240044014506900700005c00c0c041150b200c1d00490189200d41d000c000005c40c5d407641000400c0d440d601554101070a84160342c1c580c03a0011a42041c2c07541501c6000031110590000800c080309800030720141882c154403410300350b141600a98403070000408280034800081c0d40114000903003002e0028007142030030380f181c60360b00034140034203030114902074940690320300310224942c044206200030440b4419941c02154500b08100300784d200390181071443c060740d25051154005000314000d001045802080001e032a8903000d00100366000c03540c0412124290800054007150340422064000ca1300540038034001001c0070b00702000d00d1003007907152901d46150a0002e009418 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 988107140 1250 988105890 988105897
    0xc07050d09170d0e040f090b040c180504030206180a060501172404060b0a08030f04180218040c0201090503030c07123b090a0606110f0318011103030a0f050c0c1906061a 74
    0x50bc4d000188240c03d54a4405049403000e460150160340a6000101060385503800d803089a55006c080e01c40030241c55480c0d4054803402c0e00070800307417441140c90802c03c040400215500d0900c03e840d00b9055036152100400168000d00050300840d03e0303006428080d00e98000c1c0e90000c15107001141d550b44a4020340d81c84681250241075040c80c007084000d201d0400c0750080c1c0d4500321060314010070404c141020800103010030003031242595298464000452801c0c80510721421420550796603c1910380340206103098403503840c1051020400780640c00e8010105032508000f40c001080d00c00f80c100010f1480703880348100c0170607032042c0424200001e84070316801820458003192200340080c114050307000d44802010800b00901e40c002d0000e20300c44540c000e5240304114042c100000300703c0c070035010a400c1d0343c8200c8400c00a640c55001c13284a4150174425964000b110501d50780c00c0802018049885191480c10301003100241a142d40a000b5294052001020001e00c2c20341284024028140c2e20780 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 988108390 1250 988107140 988107149
    0x6030912191b05060a0b2b0507060f05040b0a031508030d050a020f0f13080a030c110603011212120f0e0705091005090c07050d09170d0e040f090b040c 66
    0x1803050920350042d007400800480d4655001d400380090f0782e18104110005c00050702e18a0740050740011130403815211400842660117428000f800b600c4550501070b01c1c0c070549603c50410014481c11a100d4613a011054030143d401020445a079000303200c80c11406001c0c650003902d080ca4030703908000b4031420000010300141c006210140000c2d0784292050040b401440384550600004102d851031121a580040c0741f440c8100c04c140483c5526029810b181100d1408120080b034a030060401c1800307201d031081d03c0c0d0344408554407840c5606000c1d60841140c1c3d0103000501d0613510bc801003c06070700a20b50b1480100100400b04000490441b0300000b92071207443c40c982e14050b0501c04509418a01282c510403202e03211007103241403501080c03144840009004451041007032240c000010410700c1b4100300c1340c6a641c0c0c1d04000900300805021800d004410030380847c0d1044007100390180d01b0650030f81c0d41c0c01045400061840529040c44054041e04000801081c1f1800c208002c104142d10401c0964 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 988109640 1250 988108390 988108397
    0x50a0504080115090f11040501030207050327181506160210030c110601031a092a040b0613170c03060c0d0b0a080c090a02040302060a031d19020603091219 68
    0x651500903294211b406100a49090601c100030031302c000d50180d0001c03c68948140100ca16103404104411085ca107000c070701d901c09110808800360f540c0380000200c2e0341441107407514841c9050204101d03141c140c072100800d01648020859040092807604800c1b03010781c01405107000a88817240003002051100c0302400071403190b40914102c8540020203038141c942c0804007025410440000c20b8404500418004403846842110000c41d41010801042c1d0706007445540e0600551408000542c0c440540c0580140c500340142c0540d11602d91841e01140c421107803686c0c007031905851542c28508091080c540601c900c06c00d1205107040c440003400710f4140840d00708405c01e0143c0c00c204040030ba9108802e0240d2214003214090f00d01071100b01e1300142c141c4001484c0c0740d82ca90115941e41c004641314000719684001c07901d01450180010032145080e138019084d56031400243c000710030071102c00a0300801c00480014000042040202d03850401b090029440b60002d040110035860070060300c0c00003 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 988110890 1250 988109640 988109651
    0x519091a0406060906050d05091e15070302250204060515030a05070203040b18010c15090515091e0c0405010312020f060c0a03051005060d090606150906050a050408011509 75
    0x30300c0c2c4101a00c0051754030302d940c0c280c0745c0a4002103800203404064000f085a01545c0d502c0e0303503140a0a4030341281c0642d02c9010307050045015070140c540c40e100502c0c600c141401000341410300c9041840074060306215039451a000017050001c24010022504026001a440ca00100c08500004047c520800c0e81100600450381c0340002242c813030043d8071400c2c04404d014007031440c0000c0c158064003003010040c50a8105020140c50b200840d02810140c84580307590f40302c07118188581840800c1401e0540708801046090080000e0341d81c041c0b4812264014040c01e14024036040181321116016800410a220558407401d0684034894002050b50151080020320003c24001140c41481107101220441c1014240c01081d0060700b00103041c222110300d001c0c0003140c15541c0c0f1029040100301170f00c0000c4d54040c24541102281c09541000103582c24a0025a14843e804001a4207948041c034010b626110104020f0b81d0340c0c029604250708950030101100d03140c002418110080f0740c0700b480107010 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 988112140 1250 988110890 988110899
    0xa02101d03070e0c16050a06061e08030a120603020d050f210403020103090f06060b0406020d0903050c061b0a0b072007050f0a081504021906090519091a0406 69
    0x54802d403603c26070040041c40780000343c5250402c4003800e041d82265204000c3d210890383e03078034145a840034044800e0790351b4400034171444a000c1050561702807040141c1900b83d00f031a00052352401004c0c010400c01000040c403140c05101a0017260080d540500000c2e18041c6ca4540f15441d014003004482d0300e446810000d100540f01a110425600c001054075031801c0e0454004402500c180b550990350501c4110600e070016503540b20b6400109490000f00c0d854906118000742004000030310181048a030050602c0400c00208a0f40c440f880115810717691040303003880415451a40b00301201c443d000d2000c040007444000031301c580c0b1074541c6640310111001d5041c40701c986021611003040c981d40c40900280b000e0705000840c4185010020310400c1e0056a40301110b240040303401011071181200c0051104600b070602a0844040403200d1440b8258103042004104c10214410307103104034400507003208108030f00034146010f0314200d24140440e0b58400c0c280e184025081c0b41030790045160030000507 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 988113390 1250 988112140 988112143
    0x11251a07140d0e060412140705070905061210020a080609160e0f0307030f11060a0824060708030402090a0509030d0e16120b16050901110a02101d03 65
    0x9119080341e44400d00300e00c001000c0d4000c10303040300c82e4500120307035a4100461101000c00c50789124038891a1030500c3c8081e000001800e40c0c881f0003400e40320030024003248002030804a50f60060b2201070030001810b030344e08400a059068280c00707043c007a00543c0480001d1651a400500018009403190319164682c03000b40071086c102200e100e40c0c032041c9802000152442844daa10601c0c0004240d070820401c80c100007070030084d040c1e10880c0c1d0020001c055004104050311102d100c080100c3d0464104400a00d004d003400300010003a141e8524400728010310508480310f8600d5008000e84640d4540c4109e21b04107032540c1c82503500343c3c80b035622040011a2070425001e21481f940c0c521340610309005d50080e8a8020b4001c00c4000d070000c2c000c60160032545441c43c02c040c070041420710360041040501d8200550500c030301400000c140503100760b08139201900003007140c0744094280303808516102d00368045130420500c658005c0d070040b51402d042410b00d42c804a0440c0f11015201d245402e10300c0e00303003050f = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 988114640 1250 988113390 988113443
    0xa060f090f050d09081b0d0303110f040e01080303041a1803180f1203040b0f120a050412030b0904030804020622150804020d06021309051e09010c02101125 68
    0x181b240005482012070418201c0154190301c242404142001d5030f010501094001d41d03022002c1d0b840201b030401800e1510210640148444000f8624600b46030712120360218407980340348540e03441400883e144000008102d10040314840a81e9212000c01503006042080d6049580c412140901041c81524040710101403805881008500d450300e8590042da240d0400c051041503400e0500400310070b0200c15000c02c1c070401e480040000d82e4645886d2003446e00484008100401d8505803044d0b00c0e0f61101c802050b00150541000c1100303503107034030000701a803107100e50b5550701814400b4506104000d0807050b50130743d04070a5207094918200b50007145c045e9400c881c042c1d0301080503440c04022600c42e41c000c00318502e94019040c071258503244c40700e0a40b007007650f460340d420180e14443c004111210700799941080d48003000744060018244001e54071906150b001d41690750364912440c00ea0381d1001155405890345685003480009001c1c0141d18641c1e0b100c042e10011000010f49044803a40b0300320 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 988115890 1250 988114640 988114663
    0x80f01050a14070c06150320150403050622080a020a110111030d0207050f0a0f1703070c14010b150343020a0b0f0402040f0e0a060f090f050d0908 64
    0x2080d5042d035080c0c075000003821200381b8811004001010100200c1c03220800340c0c0254580c0b0701e08130480305000040c17000440320b01000b54400ea80c00d0005200080e4080b8016410040394080c2460b003d41f002d4a03030400001d11500142264400254241084d4000c030714803c00d01d00410f0303241500c06400d00107490042c4600c6c61800030f90010002d60900141c25405008100e00075001c40e04032101e842d058600d001042c8105071440d81c0c403030345081c00b0018903130700e0301a0303080b5040e050030f0650521441c040c0104565050040c200110000d408900e51804d500103507c9000041c07000700130602000c09969960f005a8601c5503034500b05500c1c0d0a5042e06402044156600900780075107017500c0c0c1e600e03000d500d46026a02046015680608002c650481b0400d030081300c4088903640941450300c1000220b420021600031a03a0400c0542d80c008800890400070164000802188000c40160000010844240001d0480d141c000a503004d2090004024002100f40c0d100c20f1419512240e10355034030034840c43c0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 988117140 1250 988115890 988115897
    0xe21031303231b06090a020d02090604090c0603020405090901051618081b0f010e0f0120060702030a1b021c0303150602030c0705060f03010e0c04080f01050a1407 71
    0x300040064810000c6510078000c507040c0840041e007064900c1010b078021022a4580800d241401e01006000d10815400440c014014000f601c540d03400308011a0701140d000c1c4c170070341d0443c00203082d9459a401c4501e185a10084404402d13490b039202500940213402050b000e0301c0040001a00150b0500c1980d0082800700c0c1c0c0c201c0f5001c041034046402640791200d00500e6811020005464001001080001040c842000d030b1410003000c00c1c00300308082c100109040081c62180c2e20000d4031f4804804044000c28a068014862076004070940040d0005c081d10803031140c41c2c1003100c419408800b40c60505001e5544200170103240c3c442c1c001c10b12182034042c2d803202e120805684280002182d0342d10340c5101c2d0401140410302d030035070f040f404085a441032001d40c000084100000704140401f5000d0030013100d07403604000c0000100d0706203000500035800c200b800c5d0030114502c0702d9840301307940080c413a2401322440300c8214030465000c0c2005540e03190040b4100140c620702e403610200034500c50070090340c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 988118390 1250 988117140 988117171
    0x90206030c09061908070e0402030403080a0f11070c170607021c0c02030f16090612110a0b210a09032f0a050a1511040b030c0405040e2103 61
    0x101c4140d0b10015042d81d1011013007040c0000e0421502a44400441c240c480781042d10301203002501c00c41409103258842e9104100b0440005d4001034040d03081030b0140340c00521055003001040051624549000907600701207403200410101c40385078000d8540140f844e000f210300058801e6070307403e421385103800580c01c080e00440140095a0592100c144103140c10202060113402081c00d250b038980001100360400b0004820074001c220600000780b413580300403c0442d2400400d140c04160f4504014079551240702c03a03600550fa4681035102601110003000da0f00c03100740c210707440603905c0c01071705c1000d01107040001036503044988126001d046d01500c9070303c014100c295451160221030a140c1c0800201d081e140602d00c03030100050000c00c0d10603001400c030f03800305092418000130316142600c3c440d41003c404090041c40708050b074080f11040c035045c079100d845000140d0544d00a036040144c02c0780c50543c1038100e001001490b1510340341176040d109200b50220b07d0300500d074481214200006107401 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 988119640 1250 988118390 988118401
    0xa0c03030c0206070b0c07032a0312090602030906010311010f050f16060e0a0312050702120706020d11270127121109070809070608150a03080c010f09020603 69
    0x7100300d6985948010f0650385400c01a503102c581e891410344031480729070000f1030700b10109500203403010b001d5000054041106000818641880044048010100076168820503011029500310340c03c0250b001c0d0080d500c0c0e1400c500025614007003440259982d030b40740c0d0008a01540101100310a1103441d0340c806103044a072028000c8035a2120025411101c1900240000b20701c051041788414a01e0300b018000c0c1c580f10382002403150007a0130f40c50b01450f2503e41030014494000035040e00040001c08030340e40303130289800c101c0300902683d0740e90744640341031205044050b0b03006001002c1007001301c3d0407401c01c184580c00d544129042e91a45130701003184945042c0910b500b114110030661074034003c800907140c907950314a00801003940c0465254040310409032407440c00d4071904d6400f09803440c1c085110300c1c01209c4555500541c2c46400103105940c400305025001c00890984050300181004143d0307179030391a2109844c3d008848040c07044d40780141c0801c0d40706050142c900055001840c9a0564590 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 988120890 1250 988119640 988119647
    0x20a020c1903053403110f270903130e0115080609240303130503010507020604150b04140907060f020f0a12020a150b0301050a0507170709080f0f0f0a0c0303 69
    0x2062022600c0c05a0684c00c1c000780b40c00910030502552183c8003c80302d0044003401d02010400d00c401c0305120703421546c5591008031230242845031498518603040c40c01c0e203c400c491815440f8041c0c1141580038600700114841364001d441c4c5048402e4500d00003111140044111251081592055404005840811001c0c280c1c2d41c25101400b440e0020060040060300001c2c5c0b46278001c4103058040120000200100e103800c0c4102584500180068492885d103541e070510049070006032641d01b1581c4218400c5151210390050b41500c02d040c0d5481810f08140c01840d940c1c1c005441441c0011b140184240207042c400315000740b001441e8001030913006910350313a580e24082c40700c5003c0110b104420140d4046521040d400640707881d0500d0004280c0682420b15081d02c2e4000e20002d00f280c02d001c01d003c1c0c2568001c3c51610381b03040e001c1c1c4405860b00d40d9082100c241d9075a42c0501c1c0c0078429503003a40c50031403010a041400f528210110b5801c5001c803291180c07a03481116003d800720300c0103101000868003 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 988122140 1250 988120890 988120933
    0x1008011a070210120615030e01110a05031911030403031509060605040608091009210c0b0a0b0111010f1401050f101209060f02210c0a0c05010f020a020c190305 70
    0x5081c0100d030385d9480e4110140400701040c1d440303000a8030f4000c40740f00c0318020701c2a00a0308c5868040149010748c420005000f6200261040903003840c0c503408050b80200382d0b800020801c01c0c0d1511990760782402c0c1402406001d01c200e000502e0076400d0700014144e44548249401c86149131a4a81064609002a1030090004004082c50700503a203840000d0750b01440b4212407548203000703113880c1c1c0080c0e090701101107501100a03401c0c80280881c0f5070100341d07c07140c102d52081c106032000c030b21191b4031001250040022225201139608002c4518a1591103402083c40c2c3c1c030960b24103a40c90307aa00e200f005544214030000540100e4240c0c45c1c034410f076204000302c00803151400d2005c184220503030740d42c008980c0ba503904400081d50206040c0210518160b104004e0603110b41c90f10854248003800300c0883c8210361054080c071018003541e0302006001e420482e106c10031400d04540b1201c81620103525100c3c0400000e108100703c0c81400c400082c81180142a01e400c000248580c0d8440041d032800c000 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 988123390 1250 988122140 988122167
    0x5070204020c0f210f040b0c0a051005160e06090105131a040311100914040915020909010e0717040201050c010c090e0105010e03060c070804051008011a070210 70
    0x29002c2140ba50416010821602c00d500c207800109503400100b940d0900c1001c4520300360f0345000080188020202c0160107950a940162071701039525801503490600d0b051849500038110b00820030111240c6440d07500c81445080b00603810b13460300030414403c60310000498051076000d8014045c010f4903500c42c0d009001120742c0100c03000c240e961103c01c01c44040f01020034004041c000082c080c0200f001400070503005640c1a601001560900b500c0a00300c1851406080c00420506010003141e5076142c0007035030165003081c03251000910521102c0e003c0d6102a6180d030080c0202400020144000c0342c04900c1740c0382035036410740c031446207085030444a03401500507070401c00184400300398600c0a05c101c41034480a512140e4109203000c0c405004801d059100c181406100c074000c5091f6100401c20381d0703201c0303917000b11107a494581d89000301850096400103504110900c8012015907048a92141a1001204000c6c070120f2010820589442440c20094000248058440d4424003c40c080c0c00c011 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 988124640 1250 988123390 988123399
    0x7142a01170c040e0a090c0504060305030714010204150e0f010215180336030d051b0304030501060f030c0902090f0402091519200d080403020c0a230906010906050702 73
    0xd030b403258008004c640c251180d0b50003079a10300403181089030600f01000104000d950a10501d443c5855076a103078000c640b0050a4081c3e00b41c491484100300798112806013003000120001001000c0d00205428202c280b03450107007001c2c0031b1501243d0300000b0b000060203001c000703d04081da101c0d180400603800d00e0100ea0103511003440700c45151a01c04046030340700c6414005d542c01681840144040c920900382110740a0f0300001c07071808000c0c0c0d008c0216041c2e0256060301c40c441c90010803196140d44190f90024003070317529102010510724988001c55007124000d90601034025202c0718041e04074411801c43d0340d48621315000c0c049050030650062b04134440010007500c09401d850404100715407200c8a60040c8103842c00200e0401070700501c0c1c00486e080703e03140f2169007d201c0c4007290780d03907a40c910103c1d00b0300400c04002400c00d8801c1081d110250304c0901410b070019641d81c8000c0d101020001001001810500304203102d05194a030720307108840c142d42d0f00c0f184620b80302056500d03074084102642c01 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 988125890 1250 988124640 988124647
    0x901051e04090e01180b151507050a1709030c0904061e050601030c03050f0117030c1506010e010f1215051e090606180f010507142a01170c 61
    0x18000e0009400100882e000c0440d80c52a5040c84508640b031020310403030350000250160011130807895070554030107894407840c1180d24400c1e0004250017070000c8805198280059508104000458400c41e042c0c07080548040b40c44021681d800e080c040c6103415034240c2d108000f20b15841c0362810100e6000b5001c1e0f900019200103010460100c0030032002d00b044082c1c3c130b613000d101c000d591510a43c07200d007055290070030540c100b20540c402040410b10514125100c103d1345100303281024001c0b507440300200303030071500307442052009150641c0c000c90310345003c0340205c003030040194001d40d290740011a1554440000315030204910380280300e1228004000c2e9052080840d140c0c0b5104400c0c20392610100c112081070324141e0411929040042c034140c041c1d1b000b4002c803d04402189800300140c2800c4503d01c10400036040103c810380194040a01200625240f103042c21201290800d501e441841048081051000061100000708564140080c00a06002c903a11015580ba65003001034492100d14 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 988127140 1250 988125890 988125937
    0x120201080a18030306050f0d0804030f0c12050c01021207050604061e0c020f010b1801090216060f0e120f041412030c03040e0105030d05160501060e0106170a0e03090105 74
    0x602d81c2c2e8880086010a9458100740401d140002106243c0042201c1c0079550850325038a1401a01031803000a05245540c0d190500700200070603400c0103850512030300c41e2100c0702800c210383d0b210000341d24140075000b112040481810300004442206070400c0040200d07489aa07103140c0284004601c0110f002d03000725203403281800600802c00b0300c4566034001d01d2201210910682111004d902d0944217890354010b202c0c0c005000a020742c11103039413140040c1c4030045454103071075000043c2c0000702150310b4841065182e400581c00a64144441d10803691990724491810742c083c400d1040e184616002071104111608040305142881030001e0240c06000c0080c035116840c0d034004a1400d00399030000b18041c010328500c00301d981c3c01013600318000e00c3c400c07405140c060030390f00c241400c0701c54940e0008031000511800b50440d0004050101401c001980d460200400085041880406d125103d03804138112100a00448050400c1240a14681110003005591039400704141d6400c08018045108 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 988128390 1250 988127140 988127171
    0x9012609030d0b0901050d0201081b0304080406080f2202010905060403060608060c040f0b0a05210702010e01021207050a110105160e09070c150612140c0901120201080a 74
    0x14003489034400290780790780100c004201514120782e1594015034186004000f9030b59400d03504860181c083c01d2034845a01d87e0450400520081600c126140b03400200348010028000010320450315541d1310384000780c48005260641480641e00c01604045110186040441282e4407030f880c03d105040101c18180e464010481c1038001e644103407041991010b04100419060014030b80c4108503440b540e1905081003414100603c00c1c1c060f0000700302011514002560040003242c0c03d03200307142c0500104c0c003500c0d1654905084c08442a40045d400c003080110803840c140213407040d20a418410b100c8075076518200b245d4942150b103c0c40100034405440c4044624203200710340c003614200480706040360a03050040c00340512814a90f0041442d0420452503c0e4015004011703581c3c003281c0d0b0f0340940c055403180c90243c030003230300a1840720f6406000e1004010800580403606007185003910095020070040002c0d50b5001d100b900c00042c240345540300150b10a0003001e0b48100c3c4e1620000c0c40b4101080e156 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 988129496 1106 988128390 988128467
    0x60309150f16090305030426010f0b041802060313051615020601230415080f07090f06030b0703050a140f040212030319090512160c0801110901 63
    0xb14041c8c6070000454252a0301c800081c0041c94858800400516a45110364480e030320300f01c92184c150204111f603d40542d001880b490660751500d010000c8000ba00d201110076010380d068150414140064490107440f45107003112510001040c042d15020313040e00312800340031060b851110032032035008041075070101c140c801190041860301c69504070185500a04628046e600300304159100025030341d012280310f100c040c0613030040e64088400322806804040c0044c03112000003140c0d18003d8025540150710100c0000c1c00c68040c3c0c00030f4602c5001602d07450b4421281c6002c0c807042d0b00e0101d584c01d00411b03254000e14610708081c0694001084d054542505240d21801204280541448610070402c03248031403654501c1101710036200a082768008a900c2c0c141d116001c41c2d0744005101c3e8900c4901c80307407030071890030305580010354101c5145080c80c80710001a00c03002103200e0301c40030407 = true := by decide +kernel

theorem cover : BRFrame.Cov 987949640 988129496 := by
  have h0 := BRFrame.cov_init 987949640
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987949640 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987949640 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987949640 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987949640 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987949640 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987949640 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987949640 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987949640 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987949640 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987949640 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987949640 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987949640 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987949640 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987949640 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987949640 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987949640 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987949640 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987949640 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987949640 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987949640 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987949640 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987949640 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987949640 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987949640 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987949640 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987949640 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987949640 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987949640 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987949640 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987949640 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987949640 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987949640 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987949640 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987949640 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987949640 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987949640 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987949640 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987949640 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987949640 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987949640 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987949640 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987949640 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987949640 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987949640 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987949640 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987949640 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987949640 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987949640 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987949640 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987949640 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987949640 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987949640 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987949640 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987949640 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987949640 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987949640 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987949640 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987949640 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987949640 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987949640 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987949640 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987949640 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987949640 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987949640 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987949640 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987949640 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987949640 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987949640 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987949640 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987949640 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987949640 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987949640 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987949640 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987949640 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987949640 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987949640 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987949640 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987949640 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987949640 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987949640 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987949640 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987949640 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987949640 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987949640 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987949640 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987949640 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987949640 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987949640 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987949640 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987949640 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987949640 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987949640 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987949640 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987949640 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987949640 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987949640 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987949640 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987949640 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987949640 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987949640 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987949640 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987949640 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987949640 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987949640 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987949640 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987949640 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987949640 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987949640 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987949640 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987949640 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987949640 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987949640 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987949640 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987949640 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987949640 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987949640 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987949640 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987949640 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987949640 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987949640 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987949640 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987949640 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987949640 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987949640 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987949640 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987949640 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987949640 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987949640 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987949640 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987949640 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987949640 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987949640 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987949640 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987949640 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987949640 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987949640 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987949640 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987949640 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987949640 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987949640 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987949640 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987949640 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987949640 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987949640 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 987949640 ≤ n) (h2 : n < 988129496) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
