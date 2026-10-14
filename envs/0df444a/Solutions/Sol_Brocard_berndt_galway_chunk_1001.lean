-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1001
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T00:45:03.528235+00:00
-- url     : https://prove2.me/submissions/402dcef3-f9ac-42d3-bd26-3c2f21bc96fe

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 179856115 ≤ n < 180035971 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 179857365 1250 179856115 179856133
    0xa0c020106080a06092d1b0b040b0c01110d021c0c0206010512070815150f0319060216261303020d051006080303091504020d032006041104050106080702 67
    0xc5035400500d4101d00c103041c21550f1841980c1036422031030468000880114180800303800340040005000c4503d82c0000710706406600c0e0000f030804a215030710807034800742c0f070114207051121000e50188120f08dc0c00075040365901c000d0004e0700000d512003980301c15241c40c11010601c0340c1400e4801c1012100a58008100913400c01c0c08010030380d80801902c09032881041c1c000725800714103001c80128603040b01b1501c8900e04000d4a04085010201034a501508400521249641d000a4500310380c000520b01580d82c50803a061100c040e01c5010400b0480800b0100901e04000300044814201da81c4080700701b119801103140744800e0303c038000f400180c4043d800014805442d10002c22140e07148590700300c40e0780c0080080d400c000d075501e60f813007000d140d000441040311007170050000e10500500b10703d0400d52407904d54001401044118000b6040142c03448140310390050162100903000381800032200300d40340c545010304103c61344101c0346005074104000002c203603000b4126180a140b454011f440068 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 179858615 1250 179857365 179857373
    0x10f0c18120f14100e06070c030f020109140d0e0607050705040507030209040c03151502030f0a0212030c04030c050d030c02090c0d11040801060b03190e0a1a0a0c020106080a 76
    0x50786140c054078041610b240500c0011800002d156226083c90050300d1003096a9040c0011034007081c5030400140c1000c420060000d43c0000000422985401c08110609004000724018803d10070020404c800d81e5500055609001492151410150340c903e1001c1c485403003030094a01840c50000c10340e6101ca8010702c65407802d600701944c03013000c42c0750050605c4081300006054610390780c000c1000c6540c4196039280614002c1e4490043c0a0301d04a8250b11008040020750300c0c400e082002000100124010401500c24800c008040c40c5004140d6200d04142100015a5115100c1100c00482920b80010f00341094100c040b4111340503224140f0717030b0b16030740c00b4000154002016040c50f45410020011601000e1180c01001a490902c840d1100c0c20800c5442c00c480140d04601000780d4180b04101c0c401c000403401c80302c0000003220120b12601c0c450301680c0b6200034a03000a2010744010000b4500c2d2190700c008030703c82d08100d00140800300c1aa01c061303080760460300800c2c8207908040c100c50041 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 179859865 1250 179858615 179858639
    0x16030509011b060f0605090601020c0f0a050910170c18040c030206030c070203010b2b15050f0613151e080609010516090b0304140f0f010f0c18 63
    0x306406060200301803448207000110400d801504690959544145050b802018490714001d40701c01d8903d5503060030301000103590b480e8240706107841802d070810440d01c0e13030b141c00c1d419800401018180c0004d5041803012a41d0103141e07130103481810031400c2140b003e03002c0c000800c044454006042c559521502102c00c04100c20010006ea48580030030b0070000c0140ca85000551003200301400c0240c44510910402d82501c21045009106242c00c046039102420359221003070110064001d803603525503d074500885030310318024440360301c546003208005901211000440c80350030220341041e11100d500c042101122502ca0034180c3c040c0e880b503814007840a096030f031100131000c0d0100b05142c095660390321524002c0115002d0741c299440b24188040790f0300ca100c003407540906c24207065484030f04019944499000013480a13104a5000c803201080c054248102080d03840c1d40750a81d07001c00449078200f800703001c80101c099007a620f0b100050408038492034014540c451002405045149000506104 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 179861115 1250 179859865 179859877
    0x3060b030109020a0312020c0103050c04050108280902010e1819150f05090c07030806090601120e0d1d01020c060703180f080d03060303020a03080405120c061b160305 73
    0x5590781d4203800015944c0d00050701c00942c41480016a1012400b0f8001d0400c010010614145814641804045100482030b07800352842880c14000b60340e642d00074100c03040c4000b0040c0e180600c0440b5001d4140780c0700e800071004076000783c8440107101e90f60000c6c4001004800f890180d40c402003c00300d8045210108a0140241c00e03150101d0240809014101803040e44c0c0c2c441840104103200410160410414555202d82080b543c1414120540c802a1128600510943c411441c00c0001a5141c1c051000d81c94041c0e0f5001e420010003a0008220381d44c0e60204800c28041008035044518002c141d4544204154043e4040c0481410b03403c01c0c0f04d5035400040048043c020700e0030003c02c3c002c0c4010041e8009082080c00c40811921300402c640c2020740c0481e01ca410181041b4040c13010070380001c0c80c2c52120741d1502d096a029070713542c24003074144040741580d0092a000092540442640015884c1c0076501c800b00e00140b64081c2d8045003914031600c2c4405020000c04030790200428024405415 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 179862365 1250 179861115 179861119
    0x70e010e090d18051801050307050109031a0c0d020a120516021e07150c0c06020a080412050703151410030c0b0a0207080a0c06020c0109060e040207230105090609060c0403060b 77
    0xf0b070300c0c0c407803001522080030501480450805070004009519003005400001d040a08001400d81e003152a800040011161600091562403010581c0041e421003281c0245a901008548850704020002d000310741c43c0c2e1070350204a040c000403e80e44005420110700c00150b64005043c00a0048100a500401d28601e440c042c041c00354009040c0d400a05408100e401980c0c0744185105e4903d01141c0482070b9402070011503100d030000d034001a104030101c2e000d80304192421404004140343c810300c0e001c00d540004003014800c50308c0e4180c925081c2c03c8000c00f903041c071269111596030300d00080c0400d421840042c0180100e54420440342d0011401000c20840d240305a4540325100c50189142c03c8480b00101c681901c003403002c020080c0e0502409128420902e411301c1c02914100700100300b0710ba07a03070a4031720495000502c2d01c1041919122500400c4e40044840300c1150700c0c1d4603ca009200844103e1301c1801201d000900c15100400c0251081030004030b1756080c40d00719202c1c00014808041c2042d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 179863615 1250 179862365 179862407
    0x90f04090506011706010b0c0303190b0a14150903060c0307050d06080d121406120102071e02030c0616151d011d07030302030702130914070e010e090d 66
    0x24000c50410b200c014041c0004c15100000003003c0c2c1c3d465441c01c241640f058411090507c0030291146c0c000c421a50000d0140c400749450fa104d17883c0b010010641011205c0d4401c0d000500024100300d01740c6070841005045a0034200b407001080c0c184560721401c91981d41c5500880000b40460591401868021200d890040d040c03980aa881c20300300d60f4190040e410590000d00a000700d0b59104442840c0940345000a000305264044207404215002d00f01900c01c0d410303d00020700035442581940c10168100c440b260032a200c1ca0841626004141d105a000f8001c115504c100b0f814100119200c80c80101100c0400300041c2e2a0032800ba8903e0006101142e105d8040140c2118402d100c080702001e04000011242180140f10800c00d40005545003250444281040400e4001c001d0710700007a0181c40c1040001a6110068003c0013042c6d401000c510080d9412180c1c2800003c072002038440c1e0011071010340c0d0302c0754116109410102d541e4041544036058035200d0300c0c490440d003029160404129 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 179864865 1250 179863615 179863631
    0x501120c1e02010609110a080708040620030a110705030409090c0314010e0d020718050a020d090f120504030b1602070e07050a020601050d0201090b0f0903010c0504150311090f04 78
    0xc0c10386210308408001070303444d002d0070702881d0303d03c1c0324034100641281c030014502400280040c041c0d21000b41150f05200b000d01c0001e0500266411440540581c141031458221b0150b807091084c0c0c0050300d0440110782342441c0c402e240d050030421103031140d400c01c0040d428540303481072880107800491003c6031300c1d070292007001001504110b13089644a500b08000705050a80c100d4030b43c54140d03000d00301d9045600001f02000000102003000409001c1a10007140990722520040040d225107100c0f1104640f92600040501c80e0f10100c3d40e0b0040e21800040c03081740d0442e04200c825001310300002e8400c0f0024000310f2900e101d50000030800e40f0141c0161002247c1d105151500a48110b8901021486c001803442e20b059061010f14003410040707455500d850201c0d00001c1c6428030720700800718001c03000103014003102d00943c25a0403010004000340106460041d0007032003030300a486a40e43c82c2c0901c1c815502103e000c0e00811800c0320480582d20f081560440030002c0c00c80c103080a640d00a0754030840 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 179866115 1250 179864865 179864897
    0x30f190212130b0a110d090c0e07050301081212070f020a0203010f020d06060302030c0a0f1403011212020616030513060204030804151416020609040509010f0e070501120c 75
    0x612032182c0c00d003104416129480e401e002d6807495000341080e82807458965940c0042c030440050350300c2804c00d02000a194000c500e442448511981c000840d440c01140c100030074035511000450503112098181d0310b42a500700e110b20f40500403041100c9214401000040020744520880041400c451045a00a00164000c00c0c00c459030b14120459040e00042c807410b0702c0002c2e00803200100b40c546005c601d545440c40440005010b603100000c1005013a06603011402c0c41900340c00380321443c520f0030380d6030f950b0354400c5030140403d40c0c0c3e070803510060740da0305c01c0344ca03980045031a91042040c1e10042d5410b440001044004020040c09551603028074010003001c1210362016002462060701c11036a15414054410210a8425038500170400303404448450000c810f0243c510342e441e01c2c140801c0001b00d6100080050251151503a000b918007401c12140b400d05411031340100c00040001c110000d21240714075241d1205000d0580850709980e488004180243d1103605031a83c64601038440403000d2417 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 179867365 1250 179866115 179866147
    0xe0d0602030a0603110d02031002030603010608120d060603050c09091f0602010b1305040804031e0b090c1008010501050a080a09060612030306140d08070302121303031103030f1902 79
    0x10580d040c00d0365114184200b080c0e42c0b9030180802d45c22504003004030900d0740041d50b02e045c85061104c1d006c0e0003101280e07481d1800d410940103004000b007623170f4484444401e14652a082a80c2840d4190300b04500055000e020340700703540c0034441149500c0c3c41c00115805000400c80060301042400e41d01d0740d50f03004441100d900400142403182e0010a0003001030080001c150003000c0b0410f040d03441e05060200041c03146017181c0423aa40581a4005602c040e070b100d050550103000c01400041c0b030001040b00c01440860b401494080c00c50b120801207a003014100d8203008240100c502280081181c010118014400107600008020700415049820ba403041d056850a40c045081c0c40404400902015003502801c4007411340c054403a00341200c83c800040101c00784040203000a040000c50100780740c820301c401e03d1002c03208401c0d9a5240001620010440c0e51440150001400021000e030850390110480e40215100d0740700c40c8030307601c4040001e09006100000b40415681c00c001460014980710 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 179868615 1250 179867365 179867371
    0xd06030b04034b1e2304050901150e040c110f0d0f03090507031502120c0c1011070b041104110702060403020114120106030501090e030903120a03020408010204150f0207060804030e0d060203 83
    0xe550a201d141540f0880c40451880b5180e8171000c01c0184020300c803980f500381490f0b04441c7c101040001407100d54005403403c1c00c80b44952070704182014030f03403040c1035040500740d44444055400c492014161040990310f5043d1884c005000030f9414000a034201d10903004400d030030340142c055981d0544c0e01d036155107400e00f4005640310b0690f0003090710b803604410700f40710a91001d10740b0031903880d11828403203940c0c0360f604000d0140700c030f1603403040f00100307503512403040d20402944244008c51900f040e0500c907401030306031110b151240f8100503100b644500d04200781ca4199502404460400f8259030041d1400544580311510341c0d00280300c020044030f0045003036402400c00d510000b5a65041615070400d03201c01c00075000d40c03548200407680090700c0000d41e14a808400c9040d190f180d05805200710013034811070b40314000075800854041440307101040c1c182a001042d8580c03c0d461041d01c00182e84501562007070502084803000000d000c00e0141900e551010401003a080c420512035031a5000c90b0010307 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 179869865 1250 179868615 179868617
    0x20309130b18060310180308090f030304020d2d0507050303040b1228050601031508030712210e0c09010b0f0a0c1e0c05010201020316050d06030b04034b1e 68
    0x100c6c40d00141a00000d016811401d41d902034403606400c41400c0c1d43c3c900c800b0b8802401081250600300a0100340c8003400c2e00426560f54840c2340020740340b02c4071020201050f0559107401020302c0095140f400200321400c07122149005820030448480b5416051382c010840d103c01882180b103021080d440e030725188058030740f801c400a01c0f81882e80004088032a51910301e5400d00900c4801d0003040000401c0e110441d5200040c1c0522200306102203444002d00383c20700454030340600d6944105506030300854000b4101108480c0310001d24820840300400a20466100c4a010848030f404d116040c4020802400b841c1803d0041061aa50300490304841442d03540200500d10443ca04000151840b4001810b00740300035415800c2c490f0f030151a0556101c1107a0611800040207401d84006400000c02540c00580e03108a0340f03032a0a0243c45910500380100c1c2d00301c1c0c880e000400107200d00e280026600403030034010a44010b0348030205032504111855005000c5082c090406001c20100812145051 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 179871115 1250 179869865 179869901
    0x130902340c0e04110402220906180504020117042604091b02060105120a0b010603020910020a0c05132d0c0305010806062707020309130b18060310 64
    0x601c0c204091032241c690040300c09240103409000c0410190401c0520428044400681d186144d1900d14080900c41e075040d5100882c0c42c10000b10310403a43c0c00309085403244250000c24400d6a042030048030f40846009001c1482200484144624040300ba988148202e00c64045a09058410000d8101d07040d4584031010002078284030042d860f00403254038032980d8100c44e8105007101400381d12090140105802805400c2c02410031400420100920980001c1550701c1541c699500034080e6101030800e074000c1c010b10181c28000c0e440042c4101d9800d8101c100b20b0a0703542083d0402009103103091103004c0700c0b6107441000c56044400c0c03a003500c110300c4041c2c0d41e048546040148100341c6205840403001d2601c0c2c1b80042024060120302c2650044080394613038002d44103800325050102480d0071480301401c0580030400030b15000130042a2907003045030f54400004e0046180c0068488c1501d81030307080103100040e40f030310300350705505c881d0031100c000c0503030f01c0784500300204200f241c40a5025141c8000 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 179872365 1250 179871115 179871217
    0xc0b07080409060504091122050f0109140f07140c030c0709060506040f0323071d0c0a0509011812050703020414090a0f06060509010b12010605130902 66
    0x140b034402c0340d004180c02e944c24820044070740c446010000b00c44646900031000d086682c1c0c0ea82c0130918030140d1030f0100c07030b00c07c00003410041c0b00d1100d417403030034010311103002d00e0210000725400410081d03d100750509a82e04003240d0725402c1c00c4030a60384116840a9000c818001d641c07600310706001404082c0307000c5000b440d6040c504403501e0162501907110501401e0100018810f40f898922250141ca400000d4140071b01d40d15602c40d00d08101100062080d4054a8008610759200140d419418505544e005045403520061354680b4800c85065001080b8104078402c0300b5401a440303461012241241c4040081ea50303140d20003814035a420031601500000b1007401189400d12417800940340081440c8002d1800c101500e13610503540c3c8025150f0760f407041c0da0b24104100d9410a00107014041c22640240d6500d11800c06250407400c50b50b031044a4500010828604c142c0650724044404907001e4559490094100000d42c1b0140d20510690b805c4d1031070040c3c0d07182680400000c4a001440d000c0500d03 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 179873615 1250 179872365 179872379
    0x71a010608040c090b060a0305060604090504050a030e150714070806010603020406201513020303120103060b090f010612090501020c0a02210d0302030603011404050c030c010309080f070c0b070804 86
    0x2503c80d000500140e00d04160a8010f440d00c00503507c0c010101d0400160395129900041ca0b903000751361110a900e4104004c11040181c04284007000314401d40701c50f020038080d0b43c2000b10317042c0f2a51141c10200824064038000c1000d040c4000303410000f240c04c0e81d220580382c02d034160030510241c10800100790001010040c9030303400203c41c18007a4044001c01a85ca403d0b410641e12400d1841c608240f0740592404114221400054092030708c0e4000e04483e40c1d81c1c03503084007407143e078424442580c001c0d142000d4803916061102c00c0e40d02c282c4c070750041c03000d55a080c007100351864100b000d03e204c0c5565a400304440060400d200034440702c001c1700010840d0a04500c1002880c540c00d040074401c0000002d01c03161000b800088230848211070381405601c1c4e42d86c5801090041402e034001c4080055a80148000d20401280b400081340c01581520058040903005509540b039001f0300a01f1040700304581001210350101902006201364a0f10740e0455071003a41400c1030700014810f841c01900010700300882 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 179874865 1250 179873615 179873633
    0xf0209041e11010e1914130e07030b1302090106120e06010905040209180d050d090227090f03070807020f180a0c140712140f030108070e1b071a01060804 67
    0x885002c8440c0761502d04540c03050030035004548a483d81b410b0300c0084010b156942d01c0c8a245220382d1203d0104079601405e840142d803000c080c44140d6040b201440440c940040c0e0611030310130190040c00110031139291036412903000164a200001ca42ea90b814a801c03641000e0010500a141980700070941e4101070040040488001c2c0845032411103019080d4001580852200c0d660b00d44c90904075128440c0450400152800860003580000e07141c86550070b13042c44044507071921401d10700c0c88210385da0386901d0a03507400104020020702e84c0240040c03000a4510380007000581e00c050302566252554038085117204548980350f60032a031600003008400110707440703002400c050b603260160040503440c0400c481441035050150540e40c1002c1c01000c11400303404a8203242c2c540c1c100312641c4180722041080315030000c3c055062180030318100005c13800307110b00c034040c003510404160783c100840f9a80e5200180e40318002c00c44804c10419420680001018038041c0240358940700c428483c40c0a280c01508 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 179876115 1250 179874865 179874887
    0x1b0b130302090901020304030c030806130c0f08090706091419080303151c0b040f1401060305070e01060813050708070b09030c0406030b010501051312030302071b030f0209041e1101 79
    0x95a84140100800f103940292718400c6e1640500301080d0546512010448083d048010100c0103030402c036200c1140d550144a0031b441e101c0d07941d00c110702c03074668504c0191980f04511419000442d44401840907401d072070825415040d006200c05241001e1010f2013074000f400b85e02094640d00f01004010366002005101c2c200c14004541c0590821036625540d107120280c4a005088215448000703030801401c0f440c00c44440340c000030391040030360314180414082d114900048489000d0580000703044180c4104c0903041c3c0c0d1645e01c44070417a03034072110702840790000c000d4107032840d21458100080844040c440f050251041101d001e50310901c05052614221912400034040e92a10804101003031400415505407042441c000ba0384000d45443c034854401541c1091a403880c80301c01c82d000301905540180341d01442040f03584220100c081c0708400302c072001d21004e0440d81140710300070018980425581d40c0207100d244012406000e40d00228900c1000581c111800c10041481001030b61304983c00050b = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 179877365 1250 179876115 179876131
    0x20712030e210d020a1205090d020f03072001090f08010207020a08030a140c0c150a020607080108030306040f0e0a0b1b0717090a03080d14010b0307020a1b0b13030209 73
    0x2503007004890424485100f003115400b22550b000c141000924450b5010224007080d0a00a00c982d09011401c0340e01c6507070403a0300b40c0251146003d5281c2d00c4a01005440066030000010381c1d481521100402c0c80e502040511810801001c001050b000c4200303500c240034142e0b1800043e01c9100510500003048003070340040c0d62680c4144030a520403640841e025005200102515455404540c030ba41e180002110701c103a4040141504140c00c0114000074284504c242c1d030031a000c82d20b40f0041a40c405c42c081c0604519234000f003000460606007504881010003011400013006030080341c206040485e003c0f81180c1c405842d409211005000341207114203001d64140444c5800b8880d0399989a030318045c83c400713030340c00404541d2280a95a6801c404000d54006840c41e41e21030f0740721696001040b100c61a003098114010010401c0072104d000d80c0d1040600341c00420720f008140e00c0f0140d0608180e41090000c513845074011994400c0d40340900419490300015250080c00c510403c800e401c40145130030 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 179878615 1250 179877365 179877403
    0x80a0905030403120228080a2304031a0a0603050a0318150c020102070501030b0a0608060402040504020c0a060f050c0d0f0605040f06080f1b06070507120f11010c051b04020712030e 79
    0x10010a00e407034101c8d18240307968140100914a00c80b049160300b03000c06000308040350301213400000d20808031848002c48500d00040c4400d5515402000c08417100e0703001c0a095070307000f502414002030080400e4000301103d41b01160f2013a5680d4001100c0146003072071040015850000c1a086503010480d40c80500300034203080c81000500ca01042c0410403500c035030002c00000e1408181640c41d95070403100500750180080d903a544120b031401c1d981c2d0001e480215030305403130818820780c5442a803049500030601000c0c01e510302a80040341c80c1c06414406070103900240c3d1003200180540d00d901c03501c8800c0c1c10f62500404d0403880c01c01e401d0f043c100c50581c0a005900b040c052a420112102c00300500c02808503801ca03203500c410704096181100d10340005000c0d0103070030109818011816004840c41d80300d0003140c040403815400441d60007492640040c01903010050810f16003561014208490700060001820b0441c0c640301d8501d043d0581080d0004281c0e140d0700740c03515080c2807003a2484841142c4101c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 179879865 1250 179878615 179878693
    0x507031101021e060a24030302010903090e0606030705090f0a060f030f020309032a011a120c090c0d090209040602070308090601030c140f0d1a01080d080a09050304031202 75
    0x10700c0d259600103058009031680c4150702120f00d01290080755842402d2281c2c198407e03100c0c900a4000d058154003034005c0740340d40c4400100a02403010f0f848c46000060f01c480e0071368880c00c005071501e1304072200007544001c0520301556a42c030340c0c80c0c050004094690700d03030b01d414074200c0000d03049584030341d41202e20078010020044141d00000440c0c24540c1e0411404910318005030111006840f05c01044100d9401c0908040d40c26000c4001112007080441d0b00b600182c02c1e4000d0965a8200001c40c190410070520001c0c8200c10240043c080415482101140ea000c06500141c41c0807004c0b075007280e29503800320b426005c0c1980680010b81c001800f4005140315411612090340381c2000d0b02c11081070004d0303103071020419111705e0000303224900050310680022469150070840440003103044442c40080c080006440040000c8009488030141c890740c0040e00d801c40b0304009416036070016990380c0b004010002c00240c1c400c206c40e1801f1900d41c0175210105043c00305403079082d5424100c0c206000c4000c1b82c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 179881115 1250 179879865 179879923
    0x30e0703021c06020c060106030614061206090a0f1805060703061a0a14040b1b030313080c0703021008090601080d09060e041b09090510030b13050a050703110102 71
    0x90044401944202c0d000340300c80c5032800c0a0b100d00b000b40506401600300018110b03416400000c140c03064a030010030420b00c2101440743c0c0380034607081c0c00d40d52148080422114145100c0817074000011803800f00d004019048002d05803081d031a114680e1030000c15400381070000c24442c00d500308246190a0001030700d0000715101c20007a66050010503400020010b0304180109007501c02c5000e809240340d25a40e0380c18a07100150803000031480c0b0007280b4004c3d000104030210840340706204041c100440c203419601c510126400c5561190014811264080003507683c0060344d003070b440c2d240c0ea43c451041c541044041e0405106901000e0941e01003200d18400607042540c02c420382e4010b182185c810001c03600003a0203004481c1d0000c00300c001e45c2d0102c19045500c242448196410f50209220903114418035441910311840042c15203026100400d010110003c819520306000b44e0440c0c50300c081c42d440f40c9040900c254401c0780d44007140d2211480a507014000000507540203669003882d2544048 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 179882365 1250 179881115 179881129
    0x9330203070c0209092401050103050f1b1e1612030b090c0c1606020706020c010c1a07050d0e03030411040c0906030b01020307050303011d0c0403080f18030102070b07030e070302 78
    0x40000d108829810010320300300801c2003006d21403200030385409800c1c80f840460030f0070402c0c2070140900280c00d002c001080d01d40d20f080300c2d9001c0c110380803541844501d150320740c0d070700c030380041b901c0c503500354400d00046215003801c0028240d42c5000c5401d050b500021071a02e841e02c0000e08004106040c1403c030401d41650390308000303d0740141c0d074101c540e03580e40d450503040e0309003a840000c0c1014600450b80119495500081c5042540c92640031205028141c500540d039a0454000041c40040740d1300d00b0070f0300c0e007111801180e00300000d4202241000446241002a50701e89201c911541e400442000140409019200910a4191410071407802914002000c1351018011041450788458010010742d01c204101d40d0f8082c1c201040d60f40f2561100100301003543d42d001060824814800802d1a0b590700c84111012039501103450b5107048802c14604002d07403c0551001c620320684e030308141c17a68900780000c203c0540b0542e890070f002d01d8006805022a103aa040f507802d0356008a00900068890407 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 179883615 1250 179882365 179882387
    0xf03060c070605041104091a07140403060207080c030c0109030201060b121602070503010c11011104060909050702010605120c0907081b0306031207050706020f0a03080105040905010933020307 84
    0xb50041425a07450030803981030602d030717000741d50850f140c0014903042c0001020080840405e0081c84625900c0b41c80046070b5a0820756900c01d0fa20300d04110030400a15660700030004544220003447c10169504020390454101058140c42c59444101c800e041560a105400241004204450a0207003220322003c50b200000c2503078020412480b10152034500802c41c00001308002002404801c103110310040405001c0308182c01c694ac20070403814002c0707030500e05a41c00c3d41d2144e038440074500d143c1413021002c1c0c500500000199580e403030010507a91510918854203a40c0100149501c2c1c017000107100c10480010855010054001c0030b03c40b0809408201c0040314400b01400ca44070b80340c1c0c10010b8180041c170703001c035845644009010410040c01003800c008660340c07034080d038188030070b10b4104603100c20a0342d00040006c1c00600050100346132650125014500903000042d1641c5140d0320101602049030310609144100854400708070440c0d4040100d81c854018250b095003400071020348042000 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 179884865 1250 179883615 179883623
    0xf050a080105130f021c050c03131b08161401020a170703090506040807050a060309030c0b040812010b2502030d031107060c0309060b090601020d14040816050f03060c07 74
    0xc1c41c0b1040040c004d4000400c1d480325100300710b6075610b03c107009644081405000c19141400c01e030000e06420302400c11b5911540e10700141090300320302c030b503a18080010054505485010aa240411903400802ca44120591003c00c501429400c0c81201c1c00714401c1c0c1d84140d411540080310510000b90007001c50f0740065010800c0540718170030707854181c500b61440e4224581094012400140001000401404480003a10511509034440e00200e0a540f5080340250100308014210310000d2184c00540d070303100c0d000c1c8040c42d0601d49103c10b85c00c0090800e0b44040c49011012035030505801480c02c2140e0030182140c001407040c10300e980401d4451a0701e80c821002d00da940d05024800410384000c03104103d034840c10070804c40d1010030b4050010a5201800d0344c042c1d14103480500303c0d0515400681c010a0f0580080c4403101744504c0403036010440030030402c10100c05000005910b60300300306022200c440e2003e40c9014600f850140041020390425040c820741c4140284045aa0a0300403180c45e42c0d00 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 179886115 1250 179884865 179884879
    0x31715010f11030f07030e0a120807240b010305090f06040b100f030804080c013e070311090f220204021b0303040b1501020712020f0d0b01060f050a080105 68
    0x400000d9640882c02d0092030098000000c3c0701040300c080344002e0084074401d440f4401000c2040042c4019600f0b9405402540c4a4440100b00810b0304840509055445282c0b19440f0340b68145d555507204132400510822030751922105011580c042c0259584551050014440152030810381c036034840010b400509070807040e002107404550120b0785180038244059141c408556030b03182030441c42d41701d449240300701d001c0d002001d2450f600c120010404600501500c0c0704800c0c0c12300117024400f01c00c64a403141007040e0513092400342800d0080200641c01050031a20100c030200600c002104024040000e0b0390826042102558420540c100c48491010b1000707100807403440424000d101d001104070019065440f00380a00c00004011840340b071045c0c0261159031649490300c0da000c00d5000178a405600b0104090142900080e01c030240d03039000510307450300c0c5404880031075090705141c0010b03100c03248484014044260460405856102103180642c030701100440002e05619042c0101c41c85100 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 179887365 1250 179886115 179886137
    0x60815040510030b04081b010209060409020c072304050f0c07030804030c1506060e01031407030f0b0405040303060e0c03100e06060c070602010b0f0109033906050703171501 76
    0x22a00050750b0700c62240c00383c81c2043e00341008103403c503441f042c03410040342818621304d1606000352800b4107c0070b04980c0c10607081c16007110203500030b81205042442168030005200d02010080754a00e000301809040c5890b03040c05010550390004c018201110304502888141c075200000c030b03855541c1614091036180c5075032408840740a403000000e0600241d5040c21902c801041c0d00120841e6400c0e2a09842d181c0309070015416504071034580c010064981000a00c014029080500314400419000610440c07a800050866400349ca054001954030b0302c00b804095104030340c00350010b55035040c0d103007185003046003881098098081c2060110865011441c25104d140580d042c0c40301c0d00055500c601c2d202c0314028020460400d1042c030074100c41c42c3c1b8544a500481c20481940d400031440700401c0c02c0a50640080071745230525880802e504115450740701005041c0801600f13403551602d5860420b41802030442d665a9034042401c00000705101e0301110220004c407080c80b0070b00381010402 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 179888615 1250 179887365 179887381
    0x90c090904030c080c070905090a0b011e05150a08070503040c2102062b02070309151806050403020f0402030121020a1205030403060e0c06071b03080d0e01060608150405 74
    0x107076550b0f00081c000b00001c00c0004800c500483c800b8259910f0402c100324a540c0e400307403199920803021000d03010030b1441006000c5248aa01100260000364410a0301c0350340d10004101740694104940520040c04110004403a42c811042c9401007810b1030814210304054841003440001c82c403c00c0c0115840d07031646c0c070900d40e1600103003d8150700103022644030489150400310526503c10741d020f421052000d84640e000080c400c3e1001141c03d40d888241040c00d1810349003210413400cac1001d040c080850000c04407030b09e51480202c064844c50381c3e07a6440f10f14510522903a4a4910000c0d480381e80140014844410104688007a85403da15400108107207030010646986954000c0a000040c1711980c2e020f00c800000148200ca01c5070300e0400050b1600030741a41c68015080e401c0707602020801c41203001c0b13007004c4e0141e00d961014a4820702110b5603561109415400400c2e0060182d4440c0c40d5034100c1e40081c42440d00a0246003001521450321241c06581007180c1c207110b80c0300326070310300201d0904 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 179889865 1250 179888615 179888627
    0xa030f080a0f090b070908032106060702040914280b070c060501080d080c04030210080a02040e190b030c03030307050c070801020403060b03100b010504050409050f010510050a05090c09090403 84
    0x5200303402c8100700500b12400d1100c20707503108842c8500412806040000c108600108684454001640c0c0c20080190401603c00d01207020340a11b41c0b000e41803010101596584c072644001600c50005024459a280c8100342050654080c5c01c42030040c601a11b14101444100c0d80303405540115000303001c0d900c05030107a0301070108290240ca80c070307e09000400e0310320000900f1604c0100d140c80300b620f01c2d0b48101174685944594007009400c089a5022408000d000d905a56001881d003c0054213042e21001210b183e04c06c222102c80c01d2020a40c1040c0c401903841c4101000081c003034018114440c403180100f40e586c48080c0018040080c0007403180070081041c020710014040c2c0e0002035650b5652420210003900e540805117109000700b0308240c0400c80d040c8280c04a40034181c4a442c18146001d08020080070020b4080d1020f000d800c04e41440340c003003072040303510440c0440c0b0080703001424401400b02940b42c45d00705034043e2204400f03100720808588143e031002c4100300da84108550b140c0c6011210 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 179891115 1250 179889865 179889881
    0x6090b1606060816050a18090203031b0c01080c121503030403050102031003030905090f04060b121f110913090602090303122a0a0807030608150f06030a030f080a 71
    0x3800c0c602000070643c42d4002c214812541146030003601d49546030020820195807a1003050000780040150b00300c41d0703d103500b0260400d4002000e40307043c50810130a0703150f007044121720743d82c0a1700040182400b41d03030880181074110b0228041c0ca4100480c509001d1221031000d0002c0f1f00c80401c15a2060075650204101c07006036a1003130095441c1e08142000d07000b21400f50100301c000c1541081e003c907090030440e43d602d2180e00c001d242c180840e102c03a1181001407654004041c0c01c1104125000c0b904901004a0141c84007212001341038180c14421003012a102001d03240300e1000101716100d0076903250b807181e0035284010413000075503018520b000d01c000e120704481d03260107020101e008100544850071103442003070001400300c801d400d942d251400503000d112340c0610a202c1400402040791041800507804034603420b0000341a41c43d04101454a040f000f045081900e00710104104d12445440355034116805a00038041d4000c1507901511100c0071440e04420401ca1000241e0303200440d80282038 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 179892365 1250 179891115 179891123
    0xf1503060a0e190302030414061e09010c02040504030f14090102151e010b0a02070801060b0f09130509030c10110a0c0602190c0204141b0705030c0f01020703140406090b16 75
    0x6200056450701075242c1d0828481c0e0511000320041108c41400d00310103c07140030100c01c0401240144640408000d0b81100498a0402000c0c0b880c020040c2c40e584940e41c007682c00b0b5251070507925586039000307000c2c079050b0742d40b00a4001c040c0100040c59800148a80808090108001165496000c0c54804041c142903400141e0031035400003d10107a1071000f0084180305d54240c407030395a100c0220509031030a5100d8180240c41c2004081103110f01702e4081d060840d001840980400e8001522100781d84007540d084c43e00e500005528140c00d0301c204080c0d20203d94010090000f0008a0b000340380901556840c2c405009003e501e1381c081100316412100c0100c01803500c080400c080101c010f00d810110f840c124001c074a0100300004107401d001c803a9100700700c2d0f4030850381822089610340703102d0b40011208803001d00c41070000b424020010b015014807c00140c000503142c80d2239042c0107014030b10310b0b41d14404a0b9010042404410703840a802000d44080c2c5040944e80c0d800d061400240000841c0f000d0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 179893615 1250 179892365 179892403
    0x62407080d0504110924090a0207060f0b010315030f0303020708040914330f06070b0103082a030703030213120b040606050604062012030f0f1503060a0e 67
    0x20041240c03400414422100503201840729540e00345103400c060300c1c0c9207000650802203131b0710310b141481c1440001c3d900400340d12025080c11a1581d0300710070740b03d40b44c1c5113501a513200e680500c0346503030512a4514101046610b544801d01c1e5071210300c03559804c03450113003c0680002e080c00a10540d44100c80c01170500443c200181c43c80c07403240900d10070003500c2d1a902e115120b5031907080404200b2100400089003100c0da0384400d0b90b001000b04034106112480d41000c020300030b81d0041003507020704600070340c002c2850710395460381c280d01c4001180006038a0b9202c120b000c940c641103680c0002c191401141d15060050f44ca8030f00c078809800da51070651142208070400c1c03203a102000800184a4002d5204460034032165460302c08001180c0036030f000786400241401901c60954140e0504900030b940030380182d4441d0400000707050b0180c0c1c4111030f607158400c690f4090054104500c002980e005401c0f0307030275448600c40000003030344402e005801581d446c0d80f41d8090081d1480140450104100540292 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 179894865 1250 179893615 179893621
    0xc05031f0b0f2101030b06010c06060801060602010609060b07031b05010219020102090f010306050f04050a0209090c0406020d0302031314011407030b010207120b04151b090806062407080d05 83
    0x1005168000c0d01074849500c0849800c0200b0310a100c4050b041c4d90780850a2010340e95100d0044503271884040c804d8848a40311071000560000a101d101d019003090b80c000702d940c90800140105840705c0e54860100c00300c0c20061741010a034490218200b21109841900700c182060501501900801c1031000e1600300451090b200e45405600820030f480e401c0d0f9041c55a05032440055003182c0c1103108060308030700c00072111a03441c50300758851350b40704810b00c0d030050030408101d020481c5004100c03040403030310034005401d12100d5010861335a5901c10741c9025803552a1190540d42d486100a000a0405d1903010000040410a4101e20703200b40c802441010540744c035030001400340240301c0080c4c1c098050030328045800700310320410108041e00501c01c0500d6858541e19481c1340045414000e824555418246806101c01c190303048101510703564940202c0e09015645040c0760010b0f041c6803041c80390810a4800410081080100d00c0d079034282c030707070700c5170f03460f00300340c1300c54070a16030080d09442c540020 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 179896115 1250 179894865 179894887
    0x303070302032208031f0f08071d06010903060b060d090605061002011404030804020d1a1603020313020f010302090409080d0b030f19140a1101030506040c05031f0b 72
    0x1452103030500040c0c03083c00e01c0601107100d03100004100c0140861004100140902d00e0a4800007003041951600440041c0e03200c48050300140c2c6c03a0003650450f002680c00300f21000740c0402c0e1010010802200b40e5081c2002000601030f125030f440000c0c802a181e80305c3c0b00e803a0ba80c0e841982c0007400b000030300744060001441e201c0010102103d0483c410300040030001c810b2031052140712400c0c8081501c07000d4030349a49c1c60589407802c00070401ca0740140301c0d18221000607045140403c030741c201c10680700c4d4a41417020f008c0d41c1580c0d450004400b007510610421001100340c048203200580c066900e1040c00c0b11010040700680724070004036401505003910f0000308440400104000301c003561301004103070510003c0544484503141e40f01003035880f540c50300c044840c0030400c0304034251107101075500074284800c1c45c41c10a0000c1c80107484005d1000200e10003942c060190540c0402e0407102080310415488000d40030340405044c1012003c80c0d05d4220071803034a143c24160280c200c1c560415202d04290304 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 179897365 1250 179896115 179896117
    0x31b0e100302130c09050609030c0a06030c0207051f080702210418050c0316091203080703050c0c0d08060d0501060b030103200a05090402130204060207080601170601180e0303070302 80
    0x80124040c41c82031204903da50807a01c1400d40010340c5654007001c0a00c0d01003000708540107403501d40c1d0b00d4041c20b58041460f503106904400200656100491001ca07403801c0a406c0413501d030300c00da00804020000c0c407074103800000c6040c10b00e206410310240c0307070300c07046000c03840c2840840130719400c10305420b44c280000004902820032907a0440c0d0828140480551103002e0360b10583e94402ca014051000c038002c0480b580c64088c14201510b844e125896a483c03114415848d0400f05a000c29601810f02c4103050f414003030a940900004002ea1820b003401040927501c4201d100080208860400840c620b55590400b02c0f46094010000380718840d2500000209903002b880102e0f030364280f15030260400c0c0290a100c48c2c1c2902c0052111003ca441c01080c0f200101d4010400c903031206104108820780f06ca2440274001514965001384030160418000d246000010303084a000c0d80004500c80d84079406c001030700d0741501c0105489a4074a00103001d0200540303e07109200321140004020092501e034158 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 179898615 1250 179897365 179897369
    0x1101090b0106020f0f0d0f0c03110304030804140901080d031a190807080105041a04150e0102030610032c1203040302150612070e1506131502060907031b0e10 69
    0x402174030440500340d011030380c1e1007003410603246c041141080003d901902800304400000e010b41850442c0d4180c0783c96481c11980250012208044081420f000000c0d034540941e590b40010741e00300d0f00b1541019612942c911b0300d240c203c020140c40d1421035070301c0e160102028103034400c06069009000700c19a066914004e0900415000744038101000a040405004550069811408190581c03420150100030400002c04c02c1d24031900c0741c2001d21030341e04507110307085e9101d0400000684908055040200d6901c0702d1620030201418104c43c0600400102d2100003210351045107924840d103051080c905040c1148404031050402104001c141a0041036035121030342c0c1c0c2c0c01441034030340d60b500070440e49440f040000b0300d060703211603000d1040241c45560f06411440d903200886180c6e00d44d500280da40d03404404c2e404048207258200b00b00071203004c00f80001880c0036002031300c40c03032500040559541d8214800a0107007007e170140071180e1191010200041c2200301827050072845d0104500d4501d0201b4 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 179899865 1250 179898615 179898643
    0xf040f1d07030803010303200a230a0201080f070905091008011409060403030c050d0e100f0902060a050d1805010902190f120c09090506011a09010509011101090b010602 74
    0x960306403024001c205202543e0f0b00803041400c5900350384040714801071140c00d01603240c8105101148400d808c00100c880c66110383c02035146403080086845031100100e46c2041e0680c0101a002d005130380000a09600110581c0b400c00386a54030740c000c0301d07140710552009401599810034032104031054002c540540314964000d011030408032902007888902200d0350030040c2c000707401140c0005c0c07090300900d5110f010341c078019042003080798104e030458026500034401a1b00c000440c0015103103900545100b02901c140070041044a80c020800354403030b105180040010009040611a000760320205a140390740310320b9440b00b50319142060082000c8202a1710410002d8060001c0c0c05907103814805179411200c003802c10514018043ea001c0071105400c554001e54000040380c80d150500c17034001c68070f000e40300030042940f41814a40b060a903070345000c1c5035840c0400c5282d0007a42c221040f1120b08200303103440d4903401d00c61500e4500514051000400e05a0540d00020b0740560010302d0600b03581030 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 179901115 1250 179899865 179899901
    0xa0828020d0e061308070f0f08030405010504060c03090b0304080309060f10060e030a0503030c0901110d05041401050702040e0c0f01110a080705150a051b07020306010905060f040f 79
    0x4541090307a90300c280240200c00180307015402000d5080c03590180c003080d0840003400340c1e11500c40c0c88030750801619400030300d00810310100400296806104503002015040040c51815061000027415841035000d200240000f0203018401c16108102d500010300011480a031030341071520305a00703250700c150748900152254a001c12001c24281031440c0c001d40347c2c0000e02800c0d915056060b10b403010b41d6400344e41c0c90302507650900301050060009502c112802581e031690349119000150240d52007900502d0542d204900c0f000801760000c0c2110241c0301c5660a00f01c1803120308004036454442c11300001d420a04000462046050015801d121034004440380b090624441004441510140803904000c0d80001d405c4030203d58200010300314107010b50182c0d400140d051111031550602640c81e0391544d95a4020030169403040080c0c40e0301c00860120552070249a0b0700000c0d518401805424012175584020035185e503201c09201c1c00d456005802400324284140e035160040504450280d10115 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 179902365 1250 179901115 179901187
    0xc010c1101021809180a210903050607030506060f1602040b120a151d060f0601171807080a0606051201061a0f1213021216030f050a08 59
    0xa06009407038120310511004540325070f240d02040303503900e0050b001c0054503d281e00280d4580c00280800c0301c403c0e0140400c40c075812014544504825501400300040103031400042c0b0001e14003041050700b0a040740340c04105a2a0200003030300300e100740c2000a12003c4001050740000070550914100d941c021101003180003038500501c1000064210000180d411981c10400060512918940d003081d54081c00035010007003603100201a120340c95040e00e1075006c48200b003540c81c1020302d480da0001081c60150900800c40c800c0c41e000b014040d03c0031008100316041411802010410701c0b00401485007240c810012500741803000701030134010075015000402801e11a00b8050203250201c40c0c106016903080c4030450040801908010340b490000c40e0204001c2c80341420103035805000300700569261114131618810001c1c881801001504c4a80083c0414405810030201102c1140d402c0800c092390b0f0b417828170300f0508110780301c00c0c0101f808a010820401001c80601c2036440340c01000010034041d1 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 179903615 1250 179902365 179902397
    0x10507020d02030f0f070b011e090b090a1d0115050f0a0608010e040303140a0e0105071805150f0f13090203162706020d030c090509040b18030c010c 65
    0x9405480000075903c1000514140c03440700c80180340400080c2103040c20001543d032943c10801d801c0c0e001121741140d00b00203102d0a1144000c0354020040040204802c6910344040381c01c0c90401041c5200036642d03646130010fa1100d9911210606000c0300003000b80070007040340240d84480c01d0042038041c110141410246052420851060303030780070b4440074041e078070301a40d16848180c000d1084041540b0b030310441d030108040740c2c0b1460080300501004a03910746084410750844070020400c1c801c21034541c45c551030b103010b01522070060354401ea441e486800c1141403070400c07602c076a038410414010001103410303d444000c405416180c01c41940030200350b5540c01103800307901050300c26201d1074924900358445140102c1c0354048980d880c41000c1d4a00c4401d010325407940410341d000d400035070820340300c4039411603051084120000d0a070805c82051424035022860b000c6000304020000007050001c16820307140c4468441c03614513000c040300ea40310319550b012406040e034121980c021070260039481043c1 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 179904865 1250 179903615 179903623
    0xe1b060405030709020c191a13020d0305030601050c03040f060906080103031b0215130603051303020601050f0118031103010f020301060c0609030e060708090f0301052e050a03030c0501050702 84
    0x100c10040040c043c540c1880c030b0a00003940680350828562042c074030007115000541c1590704545006072500c00c03c401e80c500d04010301050003445455a04090480d090043e03940510f600801c94052410b0760300c960f40c0350010795551140c0400070445220214000135034054080740b0009982d6995103c0000ca40e0b00c41c01034501ca4005c0c00f0050120fa00c11848891410850136400e81d00c80c0001c0c101441da0341c2c001d5258482d5480b011a403c80e402e261300341030209540602903d5001540c9114441e2142400c0d10021b44840b0180940d030300c29180110050340603841060b08603040401d80000d80c50641e52454220791107032600659034041d509003800b0b030f8600c5001d0300c02c0d40d0403681d1a449040581490f950768100400ca209030480034082c1a1a0046850b160075000e40080c0d485100c0c40c079513581e004003c1113100d190b0540c401d0b00c643c1c1030900300844c3d84600c6926203d545241c2d0b1245c00d48082080038a090010250090703604880e160100106042d440121855120b00030300080200703803141c600481e12 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 179906115 1250 179904865 179904869
    0x50a090b0a0b030c07170714060a06080d1403040f0614190c080f0402041113030212010506010c140a05030a21050103030818030904020d0212091b1e03010e1b0604 71
    0x108505102c1c207804105201c4000c001c406c542c0032510f2a01006a840300c14200b14400003c42c00d42c4010f0801900100c684203020180803008010700d010201034900401190501e0341444446502001040400501416440c035043e8001d6040c003205803a47c41c4010b202c0740494021003d00386000149642e0011481081c00001d0350b40d9901040c1d50b0380d40340307482c1c42c004083d2007281c221b580e0f029612160f00050700038250001c01410440c811900e03500411a01c00c0842c80d03101e4280e450724090040503a081101303982c8060b402140b800084060040c041c0c200110444041c019001c0050b128a0700795111070045e00c05030030480c00d150240d840c003204d202100c81c2400010003140145011502040320384562a006d025503d00f16494078040c0d1000c581683c0090000d1944680c000ca00b030729044540d45040360f401034008e00140340d0100440180c40c4003582303c4510a00409107150346222030483c40794001d1209901500a205c64202081000c1d601c00d91b40342041e54240c0e040c24005100c1c40c054003141c0c2 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 179907365 1250 179906115 179906131
    0x50405030904020307261501030e030406080916060f0801080c0d03050d06120809101b02011202040e13020306060411120702150106120501060e060a0c0309050a090b0a0b03 75
    0x4282003a40742400001d5102610302d605205558480700382500c07000711009011454818482c10906040d072860f01880d1010741054141403d02128030304400c40001900e0841f0010301e4007081c640ca69024040c28100030042145142c450140041080e641000900c1d400d0240360343e03903e080d6a0386006540e00d95401c104469808104100044c002c2480b81000d0211007856000000f41c03e561008801b201100e03014044401590108062265140803c035105000b060341c10245165a4040c855864041c00008020305200780f410300703a0740703401190b81650041d10b40400f4044072414412030307a102405112900300c1c0b003807140400149440c02d20380103007501c00807000a07a82c184501340c0c202e01c02c001c0000300301b44114800e81d50398000319100c65411500900d100d482e40d10225485000d01026203d058010a0500020b980d12405a48484044540744000c9141100400d0b4240c5012904907032540d01c8182e019480c46400300750b010f1540d00480c88280c0031100002a680c0d0ba1004001c0741c0400c8070000 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 179908615 1250 179907365 179907367
    0x30902060901080604153f0b070309120201050612010218041e0501030b160201050606070f03020c0306070e010810030b011512050411121c0f0e0402071407060305040503 74
    0x603042d40654070281c1c01480041c00800d00244c540d8030320300079a00035070100c41104510610700506005d0705181154807000303100520f011031900114101404900c0ca4000c080c00303c5580003c110b14880d44c8150007480e440103070b40e11040c0804000074044c0c1825201d4902c0380794a23004400c4031003014030844d00908c0481c20543d0301d2104400401c00141a100003002154416044038504a5501d105450180d8445c40f8031844074103082c0c031111a2403181e01c2d4000203583c90700080c13100a80d80c50042d030f0242d43c1d10201a00000308507160480c14940c054070580c2c2c25100311002d01130560f80081294840600aa82c0c10b280c66460000c040c084003007511014140009c10340c0180301e0340003135280c803542031040c40c20b04a1a541c0440045800c503001190160f64a013a050300d00c032610310304101c07101170110f000f2000784040c03d100060400c0088280b0144400c0c0241500c1e8480c0700c40c003c014580d6203c0d0003e00c11500d0b16000e00f08040405544070a0440501842d140803031503038000e1003014003a5170040300031 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 179909865 1250 179908615 179908627
    0x5190603030e0f27040c0e0106170618040302061905190e1603150c020a020906011b0803090a0303060608040512130315090c0503031602091806040302060609010603090206 75
    0x1014007890120991600300f04a0101070f07401c03a241300d601c00f44c42c2840d40d0b000062131820741046000502203820140401c50404010009144d0221026034000b00700b400900c025120380c400140382da0070020001c0a0072003601c040006158000c80c10a10403d12a0940102a0004154041100c0d1b044400031004281c04110b10008802a0b0000782807800c400201c566070f492110301e180d503190319640225004052000e40e17031100030403806401c4a900c82d0b4001498002031641c005444810002e255a0400084a02102d02c1480301410024050b801608259480c01c001c00000c2c0c544607009400d5022a0505100041c143d109680d2680310b03c4d0081c0103803440300d03c1c000000c24103a0141ca10800c0b410340d404004000700340940040e8850000d656000120b80505140402508074240e0046201c0d42041c041003044010385007501d000325a041790710f0722955441c07541038444d840b8404002003907441079804200400d5000138100380104011a08031000380e0b81c40130202c05a84030506c00075082403080c808 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 179911115 1250 179909865 179909869
    0x406030b0c0304060e0f0d092408060f040c020615010c020102030a080a0605060414101b020906030f03160b1b12090703120315210803090f010f05190603030e 69
    0x41c5801c0f500c1800c010803108030100700340d89802150342d800c40d05600039481c116800c03500031246800609500390300b2149071180d0080b44000751250004082401084400250550345041004100038401002000b44e5000c01e4002942d074442151440c3d2500707210000c0d2042580150408244664143c4c001d52904004210441c0c0108014142c00307812611500d0101c0c0750781e6580b0142004d085250300b01507804840078104a0b4101804c0002801d1013595440705100d40e400c080c2100489405480880e801e403a15000b0074a03196a01c0c040d0281c2d03000115101c00d105400c09840903060f8000d0915031819207408070304200307605205505240c42d603000c0084155001801040e00d0f4001c4400702075038500f60741c1c3d40350156401d140303084400c0040c0d07890328900b040480403444c040182c04400e10501990600202500702200801c001034401840070001544489040140200742d4600000a1100d81410284075025042c2036514082c0800c901402c0800d280c01071080301c00f12a01a40c403200c41c150b001c01 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 179912365 1250 179911115 179911117
    0x40501081c0504050301091212050f06010c020d081308060c1204031d0306011509090207050706051c09060903140901090323071701050709080a03050f12100501020c0406030b0c 77
    0x707000c80921205000c005281c1c4d0703082c86541000c078000da04800305081442401010029880c081c011985c0c0f07801d041c05528162003000c254060710070309050b4603402d02d82c0006094248500401030115400280c1510300c10443c009600c00c40d01e40078101e03442d0762104039808d925402483c549120100400c8009000701c1e1241c0e00b6008101c08000102c0d08000d4140003013400d1074800d0300408105601c00140c200c1c49644500004005c3c0b1000808505211283c1e0300d41e40c83c3c425500c2003c1c03c01c18081110121084190141c0380d02c031000100030802c1203185d00e001c00c05030031707640f40a03408180f1400b050b05c00b90b0040011100b0400050f03450805c502c1c04e41d076800f28080402d100c072448034003286249130710740b03e810807408015080c2210b03840c01c080001408a0b00303441009000d0800c1011401c401c0108400c001a410903055050800301d88990302c841131668580101c07042c0c1500151800300340202050440098019110b0a034260348c11301403403600303000654280c3c2c88000d004400036000180c50b011084 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 179913615 1250 179912365 179912413
    0xf060801080a171c0b031c2106050d03020d03050f01030b0a050a1808070c0803040302060d050705090604180c03180605090c032505011409010302070510020c03130504050108 76
    0x3c07021810160030004003203c600828109a4106640f031789207650a2404202440f0b5814840403d003001d0300000c80300030058001d40002c0103040800240ca141d26984c0c940214000e08009041007165204c2c5080096903003909001d04000301346002e01007503290b089030201905990b00b1030784007040390329003c1c01c1c0300003414014030502038160340311010040b40c14030b00750701d0054a005902700754940c5107500b8000107041030b5a00140869104201c10001a00c1e443c007038940c6101181000203c1ea0f5402005440d1813146281d060303408400040c0200e0740c0c0001c80c0c0c0101080203e02c0080180143c2102c0c00d074215500000980100c0802508220020350ce075008a07911031000811385002000302c4e80400c0c5442e242c800800d903000203080c0130071140c040010b8840b000386801d01c0c180f444000320240351051846020a80c0d03040680002d107071818407138200004603100200d000300b1552110081000c9460350020480a4401403004000150900c0c0074090305062301c1d01e02000e0b25091822078039101e03a18441c8 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 179914865 1250 179913615 179913653
    0x6060f01050702030a0203161802041413090c0b040905130302071505090a090603030809031c090807020a08030a030b010e030303070305100902280c030f050d060f09060f060801080a 79
    0xc4880f0401a00c040c80303a01c03c8e042c0f0f60754807405002c1c1055100c0301c012401180701000380d44184400c06c10201c000461518004d01520155040e0f00122440000f81c001040c014002c540008000907200d18001c00034012110500010440c0342c4071480c1c2010000d202e404040c00590007814180404036900a20b40490500350802078544004100410103010040c0c0c090781441b03a13a000304009041e04000b116900c080040051031416408603c00c58000c001d00d5150086159111400c0e0100400c0324102c5101079001030287c0c10700f595540f80345680703a000c00301d928002828008080b8955019142031200c01400401640c10750340c0c0d0750030071801080d0003809042c0780701402c03030700045070350551000b041001100611002070481000b0600c152403003141000c3c08111400030008086503008001e07010584151600a564508140d8442c0103054603800c000c0c00e944160304001404401e5520007011180804890060b803541c4500c04d4803540c0b02482803081c0c941007040c1007070016280c003403120404400c03 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 179916115 1250 179914865 179914873
    0xc12090503060a0f050705070c1511060f090f07030c150504050a030510230f041103070f0e0f070f030c022a0a091505040b03030417030d0e06060f0105070203 69
    0x14850010340b81c080180c0b81c6010141e6035501c404408482401444e500c403800303061651510313001d0745c0c2c3c1c800c00f58818424180301c01850800340002384e1040b0711450020000d40e089481904182ea079a41e00e410094401c502944a2a140c03050100000320741001220341040c030005031685042c05144003a040e440700358003003040400022505584412020000d1405034004100c03c80b501a0364104840100c0c41a02c4100222a052003d0300c080c0700c0c410780c1c04040e41280030380c261524545048425061032130542d25004508003ca0082d20412181c01207410001450b1a6a140c2d01c50320008440103450560016081c44c0320010000e0194000b030f42c00ca101c40c81110340441c520607601440070400000004a0004410055170a00e0314458040c06041000410050b10100305441604070144e841001d00441e1a83c401100980d0184165002807904855195120b0b0160031159166800320700301510fa07915101026042d800000380003882030802404500d50340c60200e005646a821041d0120385c5031013 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 179917365 1250 179916115 179916119
    0x80c0906040b0a0e04060c0302310b0309102003060d05071a0c100e060a0c0309080309030a0f11191b0f080c030102030411041d12030a0b030606010c1209 67
    0xb80c845201005008144130460141003a180c04010344000d0f401d000d04240c0140005a410b07100702910780b031070003d9194203200c400f02c0b444d41c0c0283d20b406030380305420000d000f204214001c0000b00e50b64501d1810384008000380250300400c985008009601c0007080d81060000904504009250201c0203001d58102d548095495160403080a40f1a9908030208400306035003821403003c10000d500d050105070244009a12080a036a036100c0c020401e111403502c035085a540e29019074070041d03003560002d00d11992460501c1c0321a43c0c0780c1c0300c401e4403400182c00001641c0018440d260f0880440c03a03a002510740006e03110303260f0401c1e41c1e054800380c40c103a80b500806411000d0740c810010050a041d88100c3c0d11a203054885814038030304905040c000c0c2d004208101c0016040a0002c00c3c0013001c4400281050039502841e5110703110003420b02883c070904811001c0c160400c00598814000c6400600190f10101c0616484990a8030344502003010060b000e00020858404c0155031041d910f04262566 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 179918615 1250 179917365 179917369
    0x3150d170a030212010e16300902010e090c04030807060219090608061203030f040507030203120421020105090f030c041103060a0b0a2001020409060e090f07080c0906040b 75
    0x1e407200c00c1500100303900080c031603d1599051116401010440b01c21122481c01901660b41220600c0307440c404c202c203403035004100304050045040b21601843c0300c8101c220306116514000d1a100c0001c4c0e010a05141d2058a41d02e401000c2c1031080488801c4513007001d155544907240d941045404840664007848212185020200a5254800d0b1561a1802035141c044058540312018150070300983c0e1610402c9005480001240d41200d00340b10f2410603940c0d03504050b800d194040c1c100940c103000c1e0f09203804401504030058002c0e42d00b40c400c454a14440714100304070582e40c0f014007d02040040c050066145001d00a001030f1040142c06e03580c011300e04500050031100c0d91803c542c1800c101005125050400c4c82030b001c00703806444412443d00006c3d0001612016145035881420200320100d460340c0c050a405850050044010520205031281482c043e0764500b101c80800b41e1280030080c510382d95001501c0400c8031540c0010303045421303a4400340146d01c0c10003409540c1050f00c80000013030706d03 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 179919865 1250 179918615 179918617
    0x303091a0906100e060a050123040803030f0a0b010f1d0616030210020408070b0d09050102030c07060c0212030a020702210105040507060c0305040603050405151f05030303150d17 78
    0x2050781901411080c900381c404000480740542080040d0110030080000e030b0348136682d42601360740090a254103800c0120742d840d982d038a45940791815000c4086000945400000701843c003c00101001540d1903031054540c00c1118001c07a6060b0004a010303903a0201c05001d031018100880141e00b000c212103001385d01207201d6511141605641d0a42120014241503040c010f01e002c480d011882945060b290046c8280d64040c140596030300303c140000d00d00301d60340041d030001a0850313108000750744034509103018481031703000020b01744c500398208241701c4d41c01840030412101e0a28080c080c1410742d16102002c03c000d400c4200c040782c2010403040c0c1550804e00c4039a46000100000307001250a20740b030303c1c109040c851250710040512020f4509803002035084425501500c02e207140018040d91075013001c6162540d50702d400503400b02c00000f070110403001040c0b124449841c0c8001000c9040e541e105040c0e80f480119418400c029003084aa5000d10749117140032132480c010240311110f140040703200710003 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 179921115 1250 179919865 179919871
    0xc010203030121050f0601060906110a0b130b070915080906070e0109030501090803011e030b010e1e07020d020115140f0f2d040203160309050106120f0b060f010c0303091a 75
    0x21581b01c00010041c2a41c01031500016216501c0d181c1203088803000515680c01c411000181603504880010b01c0c1c48000409a002c1650031485600060030308040c081d084000314042d40d85907940c2c00501082c9140610001070003240131100505080c0c1d14250106d0320303642444691810083e15031400004a807090041ca074510f0f015101003942ca515118a40c42454880800c0d8401c8001e0944c0c2000812000c15091741103a40d1a0b40c041400d03512160400c01d03110744840b010840284460511424650019030007126892603002000340b008074081c400d2035407880344500a2003100281100b07010307040c03110120401803006401e1290b034844d032a0014480e50101c80c0c0c0c14880008030401d0140134022048030712500e80741928110300c0c50500180c007402c0c03200d100e00c204041c141c41c0c0f914181048000d5110000404407040a8004054a45080340c542092943c0a88090f45c20401040051900e42d0b040066017205071250308103404240d5041d4043c1c000f506080d1a0114421803040e46c3c401c0805102d44 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 179922365 1250 179921115 179921143
    0xc0c210f0703080a1506020d08150603010303020a170301080703080c011119031a100507110a060c030915050a0c140109060b1309020f04110405060d0c110c01020303012105 75
    0x180b80c03c44e058070440e00343c011030410102c03074281d081000c0394000c00d000c2a82c1c035441c03402c5581503540c05d034140c404038042607501e03400c800b0000000042c19808100d12103598481e8a070702510308460680b0310054002800f41820540145404200280d42ca2008090810301c0e14000b00e089040b9400c500c800381c1114801544d442000c803c000d403280d0b0f06105e2541201408007450044584107800b164485508402c9207041c4440020414281300c1509145440c4850081c181880070307440f050010300c001c2000900b20049491079001094046001615502c3c002c45a07452a05001241004807084a401042655001a03c41c00802030800a0003501c50081c02203102144c0c4002090500002803420030341284541e12341160407005035141810b0940300041290013051030014200440014403039075000d02e500c030400180c5042142681d40000c11786503800e0f110800302d610007815547c0c403000401c2046006030000c100500c0b11604812000601060412800341154030658070382d40350010202c140a = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 179923615 1250 179922365 179922377
    0x8120c12070c031505040b06010c0f0c0305011e05060603070c030903050f0d0f050a120c0201020d1d07050303040b0f0315061308060c2505120403110102060c0c210f0703 74
    0x88180000c408504404c81a003c00820203440c003a222480040c2024007003d0400c00007016002c24001c035495181d510300d8000c00b800488980c0c03454510300070071002c240203000303044003000120b01c05442e1055520403031000c0c02284c5950760b040c108941000c1260002c501340b00074560040301164040100020303146410000300a00f84190310040c0c81300d00e2104c119130411070b0820680c078000e039225400e00d1032010300030f0b0042800d81d0002c1080c0e0180c01345641000085203801444e0820855010150303801c05400c1c815108003a07150001c0c5502c070701c101c1c011000c03241d500b00002c441340c0303000400440c0d01032481d0a41d100000340f0400015842e6029525201d002e41c2a18821300c900701040c0316140e004004510500d161019050002840ba8684005803000b250305070840818040107120411203103002d0401d41da9115120f00c1d02c41140b00d17081c1607035030040c4030340400550600018001c40b0501c1d074141c2c0007004d56a0181c000e10030f80116603100303424904401c0c400c807071394040000e0260800c24400d4581c2 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 179924865 1250 179923615 179923619
    0xe0a02040e011202011d0d0b0604110c03090a0e04030c03050304051005010602240118091103030a05040e090a20010e21010b15030c0313051002210108120c12070c 71
    0x14101c00031350b5071b86015108600400c03091941c518044280316580103030801116034810002400504800e41c070082002c000040610f01110080700078081036030101e4500c0d8455494055141e11100b084030001c0c00724041340342020200e40204050341c5d120740304604460a0180200c889020b0722800ea21103400340e0301ca035401c016001d40402e000482071010710b04407055580341214044110946840c141d1150b603a4070b4080003445038081c030003042404068112665950036620003091540a1301c1840316045091001c28100c010204001840c1e60b0030100d80c035950202c000b070305e809070b000307070082681480b0455401c3c003490349500340041e070b81a145080520300c0c264216512030a45040001803441544000d950403540d20280e000c5d20340000103030600c0e603160382e9450742c0c0300015140c402c805845803203800400c403500400f607001091b0200f42c09607000088183c41003502c400c04028040c0c2c2c0c03e660031031900101514065405414820030300403c540c012030019802d00c0103903000a0095945981c01181 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 179926115 1250 179924865 179924867
    0x110319080a09150b130b0603070e0402070b10030203071a0a03020a030b130e0106050303041a0a020a05030705010203190b0127261c0806090601050405030f151e010e0a02040e01120201 80
    0x4001e0000d80071000900c0107a0203400061254440203090405100e2400ac0241054641d50706480020382d1240d00c0c0c402ca42031440300168480041d1000324440c1c4a01540480c084400f803200110704070401441e00c1c14910b01c2d200030f6010350414000c203810143c1d580e248000665500e0702c0700d04940c20703a501c0010070a00f0700c0001400d4a003c4c0d0030042c02a4401c020410686c0c162940e01950b0079074002e205512588003a100b213003400807040c0050600d02c004038950007440b01c10340c0214000d50300b0140381d100081001a585050307504003045107010078500a1a68400043d68250242c50340c1c912007220b040c252100c552000c00146c501c0e0202c00b00c444805500c801c60000c01c0321a0790781411404501c211404444020001d0200504144c01407403c2c0011178803c0e4064002da070051f0a004094503810000046490380d207030031008941003040c43c0b00000c1803540f0001c100c16074005209001c40710850b801e200100394500d41c00b07480450380075401c02000a24120034254240039001a032012003d80d00b00e400 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 179927365 1250 179926115 179926129
    0x1c2301110903070902071b0803030901150503060a05090102040503070b190c020616051002030a1415030a0b060307260d05042102010309020406080a0201110319080a09150b 75
    0x2080c01044a030410900596aa0009188045404102001da503403c0c6d5071600c190503e51200070b1800354428081c01203100d00b804000346208101e00b00c02040111940d800c4001d00c0c1d8258400c00740c06820440201d03881e60100d400541c2c4c03000e070f01c0c00003518003683e55003ca072034640c03158030006000d0004941944240854100090b0350170191814082c0702440780c002a03801d00c60081c40011517001c9001903410441d082c08880c8480c4000c010445d16480e010351072202804180d1031110215040100240c00880c1201d21107030198405030042c2418040e03580c5001c00e00501070071155052184030700009845603050f0744611307404660175410166800c440c0080d49003400081c46001801414001841009080c0003000c0d0022040300c00083c00c500302d400182c000304012200690010b0030000003007076641c3d0010744035403850f01c01c2e0703147c1c803c2d103542d9409071740c0360b0180001480070031102103a84e001a5104041058102051002c0010010302e2030340d42c038500400d6408079860303c0791600035281a40c50214 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 179928615 1250 179927365 179927381
    0xe0106050c0a050d05210c0906070510181103011109040209010c0f060615020105060d0b1306090606051c0807030c02120609010c0306090c02070302240c0102071e03020c1c2301 77
    0x180b00c2e030550700381007c2c245204d000d15469103002c1e8001041120a104042140701c00000c2e40100c108101404020041c944042640c800e44813004100800040750805208510f80100d00081050400040c102080007a5000c0b00242c1d0401040c040e000cac3c082101a130a06510034801c010005c0c1d85480c0841201100e103180c40d001c0300396450300c0104841034940070904a405507000c84441401c0c2c0d00c42c14103050300140d494000e480b01c0d140c031500c50100310155200d41c082c0c800881e810350303152413200080e03861014900790003408001c09118020019019000320720090384020711645010501182c401d2500c1400c0717410400701c3c0c0d15401d5001c40541c15216000c0031b1f0410030018403d481d00f52074065681d0740070340300003070085402480e800e51240055003080c91805903483e02c156507c4203400c0d01e5001c1e402201e0207542d0303451544402000d42040664503502c4941c113070064948042450200400005020280020180c4803448040058a52940b5011030a280351444c0180a070200303405d42190b00f00 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 179929865 1250 179928615 179928667
    0x60309100b120d030f0212130201080a020f04030b0901060308130306060e060d030f0e040204030c1d06130504050109021003090b36010f0c080703150e0106050c0a050d05 74
    0x4041c003281c0000b40496150350b001842d090104801c0c2001a941380203100b00401551000d43d00c80034004d0298000ca01d0b012564001d036201c58091300e03095030320f000700c1c850b6640c407149044d000c110400003e046c03a200107034083e4102c0000101240e90780c84001c001d82c000c0c0181000704914a03014010451a48502c40141103030ba00c0034107043c500500420f8244503035440c050700b03000703a41d05024410340c80361040b0f8a030b410f006802952582e0303403403501803005951801070074410440900005070000704100d185e8415000188a120022240e8000e4002400050000e48055407112942800b686031811300c403402610b80da500003034a49481c00c01301ca100078050041c03480b4022aa0170718981e54003916005c22900090050b2240c0320045108050040455621314401641800c0740d100c0100d40010050784510701d40d403810700c000041c40c0d00c00d80389081c15000f407200c400200d100510103d403107140a4138000c0c982030126450a4000e4807040c0c54030608070910000540c0000303074400c50b90203601480307822101e0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 179931115 1250 179929865 179929879
    0x20a17070605120a0207231605240d0b060f09030d0206040201020606041a090c04060807020106030305071502070501060e0114060909011a0f0d020301090e0a1a0a0209060309100b 78
    0x400c05210f28500310241000034001e4001c201803052104080c5104890b03181340c02c00700b0b50b120313460030703059154070b00c210590b100c1d01c00e500000030301410100c400c442d42c01d4904030b4080c405e107a41b08070f4554a41020740743c07001083c1d0301c1c0a1011180c4850700180512505421101e8a814000c030815150252070941c41003150042c005200050341c001400c5504110101d502044440b1526206450341c441440c1c0c041e4003051000030712181c0e003140b80c028002e542540c1d41c1c10300c4691b9640c1080e4240c2da001d00c4001c1c0002c404021080101e14000703812420341c032108902600d01102c03500c4003405e540d01500200d55200f0000010030440c2010400f101c0892020307207219041024590004881e002e05111306070511001a522940c0301c1c080d0343c00c0700d03140803031500030584881c00c16080d800207405c02d01a101c02c00345004104121000c3c00520118607940c00584c50501c801c032640c006403d844081c142d00d545c03a80034002e0504946d10032001e540704e4074465008104001039220120156040d914a850140c03078 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 179932365 1250 179931115 179931127
    0x204110a09090c230408060906010e0127020706050a0f06350303100618080d030e0f030a05120c03060a0303031802041a041406010c1b03020a17070605 66
    0xd00045200102c4070101400912000c2c02d02081d54400d4540c940c581c03001e41d100991440c84c142000c041c1c819204402c040390040d5580740700181d40c400307084c0100d03075195040a0040200681c0708445400380c1c802c003048841e1101041c071422080c0d0300820400c4404a0311038040207690442031041e0b4850b0300e40ca0b0300c00d002c024a08094145120741000807114000e0190141c04007940c240101441c503c0070501c02c503035881c6482c4040d0b081040950040300d00044610280381008001020b8180a1340c400502918980094081c160010040d140240c2d0300c902030b1031056005200705202138141341e4819280d041d030704d1f84d20184071016800002d01c249040e10b03060081c0040d81e21050340034010f99900d0704001408184080310314100686800000b580b0a08001000203001d45032441c10031544070603101400301d2020304c031400c000d1480880d19a4006400850079402091101000302c0c400307000302c449414841d031a500801c07040d148a41000f0b4205145000189000804026042c000c0145107003840c2001 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 179933615 1250 179932365 179932367
    0x40311060903190521090703150c1d031203010f2606190b060a05070308060a051c03090e070c050d05030f04020402090f0306070f02010b0d020607081b01060b04030204110a 75
    0x1000b802e0360b201c100000441c00000d041c0325130002c1c6401c3ca02840d000301d114031b012190580d817000a030200311080034a84080c0d070070450703c0d4050610061020784440920b00f501e01c071400004a040e80b9956414802c0e0b01d032441e4020b44982c029406081d103126000a00f1b030070805500e416010401124480c0440040c110441007400300d0041e40003880208120041c3c001c0302c401c6009032110b6003040d9440000068203807211500300001304811440b130380741d10301142c1e80c81d020807003448054402d135500540000580328090100044852900703110742029444a5121541c500301d29604565240101c2c0c2c0b0245800c1c10300404210038400c0440038900a455490b212020003949040604002c3c00703a5004030f2031403119654080140b103c60700160460f106850010001042c1c0d00c85900755002651070101c81455606001e91107070401600904094905049581c500303503642d000b83c07541100820302104c940074204c000e004210041c40c002c5051500da0741580100f004944011880392580002041900703001 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 179934865 1250 179933615 179933647
    0xa05100e04120e030708010609050609130f11040f0603110f030d0f1209050607081b07050c0603070c020306010e16111b010e0a120c0509062214040311060903 69
    0x9030003602e044891951810082031500c05e0310b0304007103215420907a002c0341e00c80c910751180b840783c4400c0316104495110040414811441d00a018011110307010249012a14030510003180342c1c0042c0000460000520b205412500150001c5454400e01d540c54000c80c81c0c00c40c84182303074180840150209005401002c1c1c00d850306030784600140203a030025011448a181e00028205401030180c6080d4034181c2002880b207031007103a94000c2c1d401071090305955800c0810940d4030440d400300042000440c842d040041c2600300811248c10440401e401500607242408160300030010f481c07040d216030801300b500089000403141218200800c0780c0040204036400188014507080042d2030142901e40000100d440a00c0401d030645c104004480020f8207413028a41d41c2e036500d020780b0540301415194010089079050503142103610a40d40410400d59200071104100f200840d4540080c0c4022642103280110108580981c0814a05680351060010510615901400380c0c0003942c40d01708264540c01e15 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 179936115 1250 179934865 179934893
    0x1090603202a0111070b060d02040905070e0906040b070c0c0e0108030a09050f0d02010813150507080901050405070603241e0902090906100e04050a05100e04 69
    0x42503120703944515090007034240090a01050014980c0e01c03400056441c66003082c203100000b910060307a40082d000b001c1881444040e0300d1521030380d03107000450340301da1004040113002140e000d4007080708480141d4507403188400c1c01d0712640140003550319007010b0b41d40004000b0302a2013039410100400001440c03070040183d0100050410000030101400d201101c0b8003980c10a00b070000480c000422604c400002501010b1860794031500002c3d280c0b81400034a81c065000c60742c10802204440c0010340c000c925140e4448014000d6040d007424940300c00e2038a01c010418004500da03036000707015403644e029203d154400c00200083c0500c2c101542e44c1079075070441d48940800c1583e10100d0030788026050b2080c00040101e40c5034801d40c1d94450b0341c2015245164006240301e4600c83c070f4000b03566416402604d0324200000c3c03000c1c00c15542d0506001080b0341d58540c540070070060601610f0340d59a00d20956001300c001c04c00001e82441c0035441d405000d000ca400841141d05128100300010f161107e500d10 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 179937365 1250 179936115 179936117
    0x1203100303030f0e060a05011701061a280c060e160902030604150810060614030705130509180c0a0302030307060b1c1b0510020a0b0403020c0d0501020d0509010506010906 75
    0xe61050b0070f160307003401030141c20101d00083c000e0130700f885440c80c21a00068141c4041ca90302a0300c50000e00d01480c00ca403000d2080e01e142155803186560203007610741c0900300c10380700c85080090b8000d030b1b8001c0040802c1c001403c0c801046086503070ae010700a0f00d1040c414035000c1a4010b04d800c1c041034940e0148900c0c3d40c0b2880500780c0e000030014105482d140c00c560118150741709045507080e103510101d5180ca500c400010a40740c034003100082c1c0039101d85140e08080d119842c14a20359191004103c0c0d4607840350070326000101601c5000595616042c48051041d003105a21100d86050b00d4030050420b540e2140b4907200f42102081480503a50100884904c95070080000521200020115841195103a83c010504840e910b03003c0c240481c14041d82c0e080b0a030310b030383c03002240e4580c02080000c650f07401c0000c00607072000080d9400255010744e4035030004d00900484900199031070019a8016420350101c5059402107a244201f03601c500a0325085540b02c002031002d0318140000030101e950a100d814 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 179938615 1250 179937365 179937371
    0x8031210060e1509040c030605090a0c0c0b0717070518010806060f1305060c060a060e100521060705040602060105040501053a06090317010f1401020c04060611120310030303 76
    0xc0f070056514000c94145000181c410300c60b041d4205005070080c05944078050242d4025400260f10344140e00ca440369142c000d80303070b038604010180c540508404006044206110580e84601d0100283c0d800080c851440c90f52103070b03503a1808102c100c40c141003034a1210f05001d07250044c00b00d15582c400a0f2103650744003954103a2508045020842d50600717550003260041c0002442c042100030114000c0d2041030b03070080c1800304554070341d00c00a500904441000b04004070007030501640c5880001810300300350154825001c1d04d4248000fa00b050b20558807000461300014040187c1c40c0c045c0720003801480221402c02884d803406001c02c03034010700018a107440e0803401c0103a0803081e0043c0080c20106111210345107020b11145041c900910003500c0c141c1c003069641c80c290074050300e60090241030b00d28a27684c244003d86030165100100403401d1281c1e065004405402d0826122440307080010059955840c0c42c05a03407184c004c0c100f80d42003c011100c0d240800400c065000454090b80c00c4070340c0b41c5000 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 179939865 1250 179938615 179938639
    0x6020c0318120d121e0204060206100b071e06020903120d0e1f110403060c08040611160303020d11030f160903051f02040e13050c0d020a090506030a0c08031210060e 72
    0xe080f003240e4185070345e003200e2001c01c0108150381c0c0021030501c5000d00c8ac001d480701136100c81d02c0c40c403140180c82c8002c01071241c41108442c1c3c0038103126104011885030002504000c9608002070a0410301d248102000c4030101e0f031030043e00c00f00d0203070382c520703c0e07107180540394444885440c102c140c2c16404921140c2d030340300d240b41c001c0e20179800b04590040d034201d581013100c01143d000c02811140d094034291121424421803040c80d121150403540840c00d8042c01c51210172084c4e5040d0040d4021a059a440716640c00c400c0094401e801c004521600034081100d81600d8400719145070141c00c1031840040014200d02800090f200056810003010b11f404a01880f10169140801030b01c40c0d80c211416084610090148008403043d80404d8148500c041d215041c0c1401c051156481c902e20002e540504c81110030000100b807a404260003402c060203440051240380c844020480507940b020280d45d0000a0123604465140c0c000c60300050300790f050310340062510030018082c894040845206246080c01 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 179941115 1250 179939865 179939891
    0x210e0d05031c09060b09071205090705060f0d060e0c030c03040c1206140130060612030f11030a0c060e0a020a0b04061206080a03050706020c0318120d12 67
    0x265428801c41c40c198203882c40c8240c0e1607402904031610222219404c2080f54151131401c01c244501c5002a80e60360412038613401812400703404041d1070861706000302280812103807a58401806000819036420755a08254603801007100d0386680300d940d1001865050052948200044a03000010802d03041d403642c50390705000d102a2030a17404010250541807107102000fa40b0740040b200d4590900b1003a00607a6281c0c6000b060341c0540401890700c502500b0950700203640c1d0303102c0040c240e0051000080349602e4001c44a40804454002d0340450201d543c14080180d00041c6000000c08400c055410014007640c05403002c40c003000001e100e0380d26a8a1582c8001c0200031090752950020189602c10384da504a40103158041d0060700005a95211120b840040034012502190103844c003c294011490324211515000b5910031204203808000d5040e00503001c1022b850141070740d480070440c80e02e504080142840180814544540010659550312504500102c234031403090007000c1612841d89036 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 179942365 1250 179941115 179941117
    0x120303020d1509050f01060f030c020304180204081006080d050c150115020d08010506090603070504030f0819020a0b160504030602071b0f030f0320010e0a210e0d0503 73
    0x180207a969450030402c40c20204a19100341c0032034080050401c015120b48400b0b14226809000300e03004940403000020307030944664098519400e06205490400d40c403088034100303402d62664500b1190785c001c00d040c01540310500080100141d00034040241c2c520b48820303152510112031018040c0074001c585a002c3c01014044900c0d484481c50f0744403519a1038008500140100e40f44020040c40354400d544c007440c0c0240304403030507208020401810107540400300314056100400f40401c1081c140000400a0325001000c4510b034400c04245480d650030300c1c101c02081e08100c0c800c408660184c400e85011030308004030360b6048034555102c2949032282c0c1c801a0745503c21a4002010144000b807010103111403c15540000c1d00070710080e452040e40c444c16548007844501002e070001000c5100040080d0140710f030b0400400e540c0ce00040c3c2d80011030f08a03070071140c1c00301e03816030b99030496101e0360204840d00c0100c2803102d202c8482141c045601c040028a030780340c003840c00c50081d0b140b402040c0034404104 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 179943615 1250 179942365 179942377
    0x3030a020d0c02040b0913030207060f080a020d0b0a0609050301151202090a020c1002070203010e0a12050306190305030903060c160b0408070f0f0b0c120601210c020115050f010912030302 82
    0x60245204da08100720f902c0c02d0f50307d041c8010780040c0500703000402c0240c403812004202050507580c00781c05854059248000703621032540b041100c0c4d505c50042d1415111800641d00500e1103071100c0e138550f4640002c3c1403e440c003844519292507200001842507410b11039038200c1c01d40c1c041d1284031113680d54803d50340083c0b08559070511944216100703c4040207842d0000c009842c402e0b00240300d07010030f800c036042ea82c207600000141990030000d11a91021301c200059980244014902c00c40c12441030003e60740841250401d803265000001c4901c2181000c010322030708465070102582c980010b040300c5040d10740104400502507000100030906005499040c5c40c64141c100c0c1c1141c1ca40d00c0d042c07400314030050850381e040761040c000c0d0780090031903d664002d0303445046028000321a2030b5585401115000321051600035505450f040c1003410710101e11031040f10103400e1700001224258504110551141070f4000d074400d60500403a4840c60742d00845000c1201d1115040c110102e501d40340940207400b500f = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 179944865 1250 179943615 179943619
    0x50115050d18050610031a01060206160e06030f1f05010e040f1103090d111603060b0d0c0305010b0112060807090902270a140f04080901020a06110a020c03030a020d0c02040b 76
    0x50000c1c841c8907140150605c00b124424220215581107200400003050000d00c10b0382c000d608901c1c00120f12520404201c044510f46107004150403928100048a581047c0c8111050180900810100040a01400306000d01c101c0d031000401d03240c1800200742c0c8985050b502d005030781b95802003600d00720f250403c440151690300c6580d180d00d45143d030341d590f800003012141e00140043c10306000c401d01c041401e00381516007502e60b9112a0454032010081c0456401d12500414001c0d1940b0100d0b0395414510091440784001050007401c05000406050b038003803408948070300e05003040000b0303800001c0c1501214540140407031078032030900005040d60501c104030602c1816031000007052142c0403102502c00c91411a0401002080034181d0301501e5084441001ca510000049808114044040d240b4050144110340d407c025581c0c400342900d56404019042801c0418202c882a4040c0800080b009040c0e00560400c00300a40082d600c8440841001c20f100f101d00507502951100c0d004225a0300c80 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 179946115 1250 179944865 179944873
    0x10612060f0b070b06221107140a0204060f180b0d0c08100507030203151e030d021c050307140904060906151409010e1203040504060602060406050115050d1805 70
    0x7035001da0b180c0c10381c001c01d0300715020902100004d029250440307252203002c3c0100c100081c04141d0019850003490000c00080e040107041c4060800940c0d5a4015109410340070b028004403001c0380b060100360740712a00f00c091650a01c030300c1840a000b0300281c0482e03400c001705020500c50081408950252003445c0054040380310310300c0120380910002040d190701440480d0400403070340ca880003242240016a00c202451914658045051900c44110205003207070b03915840660b044040000c0c0341503600d502580160300240c440e0031a44000f24040180340c1600d0509500c0e501e0210002000c0001118070820360250200d01d500088c0c5480d48100050074403c0030802c415600d0306c0c40400c4060206012600107641405c0301c0c0c2d00d0692480c1910011041030315960b40c0040202b00b0444806040040580c01d444140000155543e0f9400b40c5d400801c05900540740c5401c3c203040c450b0680b4030581000403082c0d662014055002c0e4070070112083c3d11f0b1003040003e05101014880c440c00015003070050402d1007 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 179947365 1250 179946115 179946119
    0x9090318141f050d0f0e060103140d03110702010c060f1b0806030f060112050c13021b01060303090b070f0c0e070f050c070e040f050607031d06010f0e040f0f08070c0914010612060f 79
    0x1400c00700402b00002e002c1c1c01c50b102e840c0a09011020798100e01c21a80b050302e0240314400044d4050005100360901c41c0201140c08650041d20300216800480c65454904454045048168200c54000c1d00072405401420701e8a4841c124241d48541c103100b4030078000f590700d06800a009050100f54840f48d030040c03120800784070f05107014020350000364050411108014400c501d01005208641c02c490b850f4030b40e0707911585408510b0380a504461000d803507105210000c080024007900044014000000c0c1e204160b00f03019070001e00020702002d10200340201006078801152000680500f1210410922801641c65180c0540c94800604000b0020321030481808145070705900700e0140c180e00d10740c40040780c0d20030300700e025602c401c21b2150a4450b414100d0500c012010201d10550050140e444440411282c0d641c00c000c406043da015520003101180d0304003008042800140100120070080c0305e02d0cc02241300130300d21981071081d0018031030074046070020920503401a00c010310480b020318555907 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 179948615 1250 179947365 179947373
    0xa0206010302040501140d0809031002070b07090506040807090b0607140106061103040f05043305011202030c31140306010801020c060109090318141f050d0f0e060103 73
    0x848280022407040c0c1c1004008200740d500c2c500e01c030403400300c004e20341860014a034940d081c007076100304c4803e5014004c0840310f580340740f400c0c002403400610031401c1000301e150040c001801da03000d9400040c4100d10800c410881d1490009006058404840b0001040039950000641d03500c50044014070605284c2c403041443c81d03043d404407086548580f01e903150014041211034991059005003145007440200030f01441c00d2550128003815000105000c12074544017944040d145001d04c21401c24071300e03410900c55540e1040301d0303035960840758038194210300b0301c0e4000580714040d05007a15020900b80c041903907441c14401e005841d000c40341c1c1030124400e032109184401410100e9006010b48240800000d04000510854102240840c045e02c62031b420180100003400094200307504000303040c80c0e21101d0340303a0003800380c00a040b11501d6608000301310301440507802656145504400078401000000e5803c4000c98052a4951600184c1402181c4000d001800c007100b03946202d00c07800c00080100 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 179949865 1250 179948615 179948623
    0xe0d0c0b09010905040b10081017070807050d0f030503100306020d020d050c07050c100315090c0f02011a06160506040305221a032a1b030f1204031101020a02 69
    0x4000c20b0340d03103c05150712442848107882c0304c0419581c2100081500c0300303945114884450f0090250604c050883e582e03060010002800c2a00030705258120740c004000700102084800020031099603542c1e030340e02c00343e1610310200841c05400f50501c4000800508228035042a61018613408202107443d00314058007a0003c1d001000761204062901020580340c07041c4409864a0f2035000c07004040710300c540403c0c0701c408805079034a6003c0c9a210f0840348446c1800c200001c000d015404000501d0b4005000000d0000115154840940e45003205088007079400d5105261031103401c2c1c1c3c42d2991180c2c050805c1218111008028103140036550500c01010381c000c0c020700d10600a030742c1c11401c03034100c4c080c0c40c000c0313107990b202d85842c40042d4158100f000d80ca01000c1c6510040004490404101001c01050040b18070580300c0b0348224001248005003500744400170794120110025828400c3d60220140e061044d070301e500050f00407000c006030406128514070100c40031840d00942d19580c1002000e0342e1 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 179951115 1250 179949865 179949877
    0x9021f020c12060121050105011d0a021e03060f0402040e070917070509221406010b12150d021305061c03020d0c210815030a0c060e0d0c0b 61
    0x18020081000c1075480d01c48020414000b2100141110764646101c4154030380d032900302007004842a811040c00300700288603490007480a042d2107004500d4103188500f64044c0100681041b61050040d089c40c0c101e4403480075000c040850b491907a0740c90b075000040c103294a50041662150000501282030f245074100c2e240603481a4441c460040c0d11a00c211414103502910032034a613004044c1000249400190030b82c00c030711000010040840001c0c840c171032000030100c0548500c00500018464008100822401468207413003460030701c2c9180c0d0f000801c1480103040e0301801c110610b25111640d0311a0029208141d00405000c14007590204600107040d0490303070b45108071410391582c0700e22042100415803441d815030141000e000480c0c41541d000158030029558041d200280c1c2501c1d24000d04442110403880d10760000614104540d485000c3c0b0040c08140603402204107000056502c040c0001544c0c21070600040c0c445c0c1c82404110050001100a061000800300c00984090b03050300a0007 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 179952365 1250 179951115 179951117
    0x1211041e0305030f070602190815010e10080910150303030605010302070803180f030c10050912070f05100510050f091b0f04170d0914090406020d09021f 67
    0x6803101181024000c0401a4440078202d078000300084c2496418080082c03403400c0c440d100041c2414000580c1d040c0d600e0280c0c0165011074500d03801d001c042511503040c039a0480091804003c0e050078440450148103220381c40790700303100c21070005c00e40c403800078402004466190314081180c001008108501d0b90200c0c80180c0c0400e00d0820045091b5209000702d5042c1904a8252860b580340d82c0822154079280c030100c0401800380c2c413011303000380e00180001c0c60202c05110040024002d4100080c0032100e01030207589007907101c08042d1480d140400181c4d030b05036403c40a04844001d242c146a030400010304c0c0d4840800345800100321180a0b8001c0000c251001665402ea140b0740c840c0c14401c0142041d54410006140c82d10b801d0078030615403004207407220b03054540e541842d40e56682c8070800c024100001e0820303040b0754a038105441d0b1090b82c0800178004000c13400007000c020404940040000340000d449260002a030281c0010290401e9444581c090011410b100c121005c0444520031251620 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 179953615 1250 179952365 179952389
    0x9190c0c060e061b03070806060306030c09070203092b02040506010207081c0f020d1d03070801020418051006050306101103070516060e0f0d020103060e0f07020111070f02040c121104 80
    0x44c400071429002d0301e103e425a9100d00c502e9813602002c20005030001000c81340c2c107108104c116040791301e8010718070f4040c8010f500195124018201001181c4159013406221652072501d0200c014000341810030100707406407000141d1780c0300c5600403801c062041c0c01c2840786101700300700595205034096400c0c100010a5a40340d902c0440000c00700d84440740c40d0394840c00a800803000300032914107000d03542c1d05940024100d4094654a0507080e00fa41c1155000c510041c29035184010040c50300e01030303141d21040c071303922071601c160138000c003d40030b07000c00381c07207035000d1304007400d003084044d008480c0700301c103100c0c04401c076174440c80f1500c0c015581d00701e0001180c11001001c00001229409444016030700c44004096800301ca076000c05000d0660001501641007589481e0002810000c15212a000351040280c14141d481e1003038002c2c1c251a41c0c0004071803101c43c00c01040001c91a05050164803a50458000c150340b58011411641855038034003036030b1011300e05030b80c5a0b100e0681000602c02c50b600d459041c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 179954865 1250 179953615 179953651
    0x20307061505100f05040807120c15020703060911131a15091e04051611070e0a0c11030c0f0615090c0309010603061a040b09190c0c060e06 61
    0xd0300403020588910b503004690480708124560055850820282da140740907410039959000c1d46103444019400b248000088901000c144404002c2000103030843c00304041c2600c0c07004400960fa14417612002d0039440d990b820036400c0000240d1003c0145900800700c0d41c801d210601d5040091800308000d04034552070304041761403400d0042034006242000307e14641400c418009001801800009100f00d00106410002ca1503441c2e1113080d0241c15042c0c1d030414846100a0302811900001e40b210000368001c0b1000c00c03401c602c144905512080f408404584d108035941c0549950440103e4140365010124540c01c80b02400241c605181a0034411120580c444064442007601d26078081500154030800140d00d020760417004542015500000041203a5030b51505403c031041c1e140b0900c100f02100c90300341c840b8642170159102c0e0b074104a070f901c0903d01780401207024869081c0304084405444001003004540a10754400440c1e400c40400e0200180c05000c0e6601d807441102d800000d03400e000a1 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 179956115 1250 179954865 179954891
    0x306021804060e0a0f29121c03090f06060e060a0e0c090d050f030708031602060925050910090c02030703050901030506120a0614010602010218062802030706 69
    0x610080f1a03802c420042d403034503a000e51101a004908103040c0d62038443c440544125803401a122506540390500c4041d591084100701c0107503502c1000003c2c42e40503481c1c903503c038400824041126003a906000a110100e480d021000d28180070b1b0180ca06440c1c400001a0320f074800382c07103610444040b2055042c6caa01d40302021849082031351108003030441804105500d080c800142d81d00140910708641c0845040e40400f880e40d40400c2080740d00301000b006016040751a0761844e6050b821034000380006143c02ca4020790780c0e01c0b202090210604070790b0742a129511300410300714060480a024821545015041f400301c4145900c20400c1c664903001004006510100644207400d41c9940d91916003110302c4011030181002030540740d480315103d07802c840f00324070411074218113034820309001c10940481d4010200c0f40c0016171002d029640100080e4444101d05840e11040a000f2202c3c541c4030740001c2e10400c101e942680185405504e11071622043e244c001000c0c1000c1441004180b0000d072070000 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 179957365 1250 179956115 179956121
    0x6040c0f06022107022d0f031f15061d0105040e15011b060c090e010b0d0e010e0307050307150207080f0304020d0c0f0e0a0e060c180a0306021804 64
    0x81204010b03002103644802c3d01c5601c01c001000801103640490409500d60002558841c40307110028941600c40c0c09000d02c06007000c40184080780c100c4480c06201da003031010035101c2d0250003440b008031000092089541c1110b51010b44170444a06040c066203480b030801814019500d401c000f21492824000c2603558410402c48080c0e4800b204049125111444440005064003104905110601070000400610303c10344140041c010304022810359401c03a0058012102c6812120013007040d031005100007043c80c4200c41c10600020400180e80d541c203a58540105211110401c01c0d000028160040c0400003014201280c0203031401401c00f0740c2c03081c030030040348a2000000c01c1c4c03250074007000c20703401503c2c0c0286a0190000d4441d0004281554410080c2c1a0b641c00c00c0c540740340400030900075515104200c179840092050100a88810000700c541e40300b0006080e1900340800240c0482002d4040c0107041d140c002c0038001015840d201e00d0315101a4011030460101d0280d19521600d040c42c040c0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 179958615 1250 179957365 179957369
    0x80901051003080d090203060705090f0306010806220c030501140109020a0f080c1c061d040809090402120d08060f030d0c060f02071707031103040f05060304031e0206040c0f 76
    0x6140d480c1d030107203540e40300c0c407071504952180e00c0031a503a0100c65016840078440c052007102d15035a070b1969803000c0701c1007241c0c0c4011011001d0007a40594018480141300044294000805201076001c40304442240d0400c420f02c0b2000810502c3e401e140003041280541090f0740d040d0003040034581d40c0c0c1e21001064124040d4201100004001c0355119107828026015079400140b844001e901c0c0c10480e41c14800440010001035203a16601c0f842040318401c82d900c0c500c4c0c560101c81500380e081c103180c1c41d030368498002c00640701d100307400203c080340440d510412211210f12144042c0c1c5c091900081010301554012190940224650814601217107070100d044c0c42429059191180300070216100e000c002c21030f41c00d56105469003004400301160400100381c8668034090040350b6142c2132843c006155050103051100c01e64010320040c0011050520f50b43c042c0c0761b06903101c81d1656141c1c201290659210403c1d100740c410358500e02c3e04a03660100b03245100d40c1c06001032510040d5070741036080e0744040f14 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 179959865 1250 179958615 179958631
    0x20309010c0215161419081b09040b01051204050606010f0f0807080a150f0312090b07170706020301030615062a0501152c01050a031101110f0d08090105 67
    0x1c0000240c0c41018401500ca1013001460042d1885040380c0d41800325a000542d07407020151403007200b03000142c1c80750300b140c2d0044c504a9415500b61003040581d100d8000c04407900d00c41e64070751010301242d1f440341040d83d40b4190401f0344070f0740ca03083ca03042680d2201015101e0794001116602201640b50051102d2102107160341e50300c00544d5140407084403010310180800101c0358881568400c2040d507040001d010381440700c00741c5000d07461407418807260104940c42e801400219007003004440745040544640540011681d2115254801140e01d18454540001d040510120000c8144100741d80180c0000511592080d181610f4010540b007210b08d0214005403480088121800718072805650f4a80030701c81d0b4008150241d60703203481d0403805003e4000c904a80009200d00310700c10160b8481a2058155500224041d418803010504460250001a000b50a003050f601c06903481780b0402c107103482695040e9001410b09182d2039845041c5c412072a40001c0d0200c011494049040c41142e00031a030f4 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 179961115 1250 179959865 179959903
    0xf0c120209120d03060e01080601060c03052b09061d03030a09050c2e110c010e01050c060408030915060d02090907031a010f0b07111302090a09020309010c02 69
    0x840040040a07510640d2800e4010351032242018807200c0801001203107204a44000c030f95141003009129521005031710040460b84020700421a40d908460803038041ea404d03260590f5240d0160381d0380c10910b00c40b940c020a84084903c40e100010b00c1560140501c148914428005201080321090101440708500e4500750030410108158100030707071280703044a20910030f5030041601c0100140040b042400a040c030048006c0640c100310700d00c0554049040401d06090220640d54000c0c140d5079100c0050076070500107442c5080d02030381e010701c0545581100c050211601840d0500e4011203c6d04266200102481007100c481e42484034a030403584298005040684410381c3c42c4c081040b03100c005031010784240a0700c00c0c040301281016044060b140c60041086400c0e5141110240403804a070780f00d0340c0400e40c10701803440003c89401d40f1401e0000111400000b201d2481c0c0e411009210300c01c134443e80301a01d180c1c0002da50781c290b0051407085400304020050000d4800c020380e100c56204000346c1814075 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 179962365 1250 179961115 179961137
    0x8070b0a080a02090f121203040c1a070f120927050a0608100507030b030f0601053a060f140105120307030507081c0c021614030c0103020c0111070f060f0c 68
    0x2000d400c0800d014514a0841e21414000d00c81e081c500d40c01900d06484c1c0c000c01c0d04ac10305c45900950150303402e91500c20804c2e4600606600e60005803500001c000303015501c120b540002640c800d4800901501c508580e00700b4800310501c01d02c1c00d50100d50b0644459606007000207101c0042803043c40101c4400700c014000600d80301c8030081c001c0c0f030028002c505040e034a4910a206072000c001050040313a4200090515504140070444d070001d08500f400386600621981c10256626404800402055a48290300d50324403441c0c402c0c042e000e03820b6100361403071a201c6840064140408918100c0e2000c0e901e095903005103600c000e849104141004e0b012980401640e00000e242e1802401158100801c0311500e8052505010942d807602107144e0060f0300c0002200103660000007543d000f415282c2c41a0800c00303102c004203403961080c052582c14140c0c0407a0820202e075080d00044d0f9000106100a5580d04480c50400b8844840d01c1064a8917460300001d8043c2601c5403084558803840782d203450303203511 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 179963615 1250 179962365 179962369
    0x1140c13060e0301060e010b040602071a0a0e0109030510020a0801090218130209090a05010503010c020f06070c050f1e0d08010506180f030109050309010e0103051003021908070b0a080a02090f 84
    0xb51180390494040d96111400104403501c60300040c0640441c400751a529840c3c0030009107018440c0d000b821502030315403280e8609400b810101c441700400c81c241740365140e00510040e11001b1050b40040c1082c0101d1a201444038426801800c0d400701584a07070400c0d9032104104400c07801104003400c0481d2500d4101151440c101010710344d2118000030140c03514502c0d00101e5003240c029680900322907150310040c440c030b10b000e000e50112140350744014910001010400c60f5107440180119085c440321f00313003880c14010103020801c0808404421604508580340c40c07101d8120020b045c0d038041c7d008442c021500c0c14400c8039824100c0d14018000e90034040e03203100980250b82d10303149042d071043c201c42c000041628207000ba0030025000700051903c80501b10f00140c5030900f892411410036103007030200441c1115070300084065a405a0300848480d100c041007003054070361070700194202d104c0d011001030481c3c0d40100410b00400c60703903a07800e0540c035002c02c2c01040c0d004190302542c1c004443c450040c0a4 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 179964865 1250 179963615 179963627
    0x130602030c0a032109032613030e0f120a03020c0a080309090601051b0601050112060501050d020306030712050304090c0e1e0303040b0a030509060112020102030d020705070b0c01140c1306 82
    0x2160004202c2014606071004e110304850165204a010402005030b64208203441d00603081d030911440c04501c168a02003041d00301c202e40c40b81008080c00401490500300b6202c0c0d840070300c00614058904003030310b0f009005003966064081c1c01100148034408903102c203400c260710044121000f410055080c0004282000320060000b01000e04001c800d0160a281181e0f0f400c43c0c00d620200301e4050072055051000041110070030f058484095401c04e00300700604c2e40c0c0715007210540380421400588070b44403003002030304280301c0d07900c00d00040d1031200303600c0280803012009104464180c0810091080c081e881038405500d046486648074000b120a52200040400400c50700305009081e0b0349071540340e41101c0d0b445d8000f21071007000039550308200910f09500300459400352020701040114911141c0c0002e50360712940c401c54a0b5540c010a2000c10000104110b402070121804c0050310b54105500031030007042445c7c50702541032001800700303c541c00441c0858044428003007110742031508000003a984 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 179966115 1250 179964865 179964887
    0xa0f02070f0f1a070809010605040608030405010309080408061806070305130308040201030f0c030f06050a0806220203071205060f060a091104090507170f060d0204090204020c1002130602030c0a03 86
    0x1400c0c01e4501c0c14040c500310420120700c6034110703460301d901c1741c10a4080c503402c40c0c0e0b49030420b42c0960f01e44075090001b03000001c141c41c200d1b94240790125070b400103858440141c4c05554450038851180000307002440700c99014540f11480c54030111034183e601c01c0011415a0f405641400f01e15010171461004a0312400c05c0a40c0705006060100c1c1140c8041501c0c000c4900f00080d940001c1d0b074130010010032040e2405810000c02040b55604c90303850410400580f0b440000d0306500140310101003000b40e26800440910003190011f007a2205c1566440c00c08400e400c107030301d049171140140000034110508110f081070083c0c030058039040c00c09040444810050020400300480c401c0140000a4200064044c491040300e0700d0351144507081244010b5a004100035140386120303d503900412246454004503100000c0c0c044601140d55401030020030000e101c2d5648908950048040c18140e854650300108a90094410049003290382c42000b2a20b0b801101c11a103031540010084101086c4600c0714202 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 179967365 1250 179966115 179966123
    0x11b0f0611070c0801230c03072001090602030a050a091208100504110a0221030a020d020412200d020102030d05091c020706020d03020c1f180b0a0f02070f0f 69
    0x4904102e586518548090561081131140c1d1608071054130903001e40100000e52141004205e1181403600000c0c030140030044c00c840070003860064808061010039020700c800404100208070200050505031301950007112030360034081c10900480c03c1084c19104d103403d96a0480008200d40e00c2c0700c9011158160040d2810450700c0d01d500010405d503441c0c2c401d95207510007481c4695550011400c0c00ba003442042000e03201c3d9841003e6008000501c42d1040300e5000103c0c032401a13a03034412000300030003400b65410045d4448030003018003040128585e0340350454450b50a0300701d191080502041940061802d0090040e00140700d103c1003100300360001604245404180d03844105127000d4a160100c480741d008005a000c0e40007000f060350144000e2500701c5081c50309610f00103548203125611041c0303180071810b6402c03480700d2941008a5600401d20300c84140e1048011080c5402c04080c4044180c1da460300352450030b0070070300c071b06c02040c821508115400140c0101c1d822403911001e1207100c088074192 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 179968615 1250 179967365 179967367
    0xf060e0d140102120103060507181404150602030702040e030405010e0f030c04021c06080105010f030803090c030706030c1b0f14030904150e09070e1503010e01060902030402011b0f0611 81
    0x10280010070f001070104a0741d00140042c0540c5181041e80c281c41c0c0180c03007081440110000c598500ca00d1201c0030041d00c04003038060700500d03100c0d00400c004001d00e040800202d0280309000c00c1c031a074048000c02940303000311410301c910b00d0f807443c000f40c4078481d034883c260104602c00049100781c03c0c00e420848031a800102a620b0215101011070b09a07406101d001254009034981030110392207500c2590050310340c900c0200001d604000d008101600395000c042d052030004000114242d108001ca5055580082c041d00c5650340d55030005400f0748890080301010861008035010402d481e41c843d0001142c210300804580b81c1d443e140c00b00c2400101d03d10984c54003040100d454140c0703560040d090f200d03000800c44040703240b0300818814503600180c0f04a44c2500010030400440440260260f08095025220786031080c0b4140082c1c01854001d103119004d500300000001e101c085a40a14400c034000c0c0c0361600c04020701d6121203980741743c01c44000e26130707100d6204001c0071804543c800070100c07184042e41 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 179969865 1250 179968615 179968643
    0x2203030905030d0c12060305060402010309062003071215030f02030a0f1a0609091506010207051c0b10180f0b09180d020f15100b070311070f060e0d 65
    0x1c2d0840d808100e2480045131a04002500d49610071040c51520070b050704108040e50855903020b071076850103440a0304058403818881700788500c685c02501150080ca00038501c0c41710494031405282c02c203c3c0c0034400f0810162020b030004070a80160720b04440c0c01d41d0340043c0c072811503652141c02000c0307071030a0741c15102d0b2070700e40400550740040a81400c1e01613000911454203101040240c3c10700144014024540c0006001001c2d10010705001c0b11141d1002da0329440d034421004034505440c503881298400301452400313000511803131407046c0301401403204c000641e80c0e040c03d592018440d07201701110f0b28102001c02030b00b2030147e4000d08031a42000e1003c500b007800c541c005154248251112035005c60001c8031503a03181410098400c1c01c00c05400075240300c09001c120952240c100c41c5003e000501601d00090f00071107140d00c4440644034002314a0348501c02410004c0c5030160351755442c150b41c03058420100700c1665444042040b01c03559500d40c80464407850901c20041503080301100c03c443e100f480 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 179971115 1250 179969865 179969873
    0x81602030403080d051f06020d080a021312061a010c0b0a06170d080f0c0405060304060e0f10050c070f061e020c0a020a0e040b0c03040f0503030f01031101020622030309 74
    0x40180c401140380100e0300d400d2a8482c1b54000fa1070301004207684001580030480d9613000b01d030000c242845400c000300b460342c514408001078490f140c0a44503c0240002c0802c0c0c40808000f44400240034007000c000d01d2012650b0000f19884820149001c01c0c65151060002410162036030ba000a2411000c51740650350700018401041484c080001130700300b0900e1206144e440501c6a81c0680005a281c0c06c600b400783c0b040d5000c4c031035409424081c00c0000001024840143c1020b441c02d821502240d0841e94040030042d21180120809001107081c9004101665000c40070350314515000589100d81240c10b42d01ca4000b08a00d903d00e1200d40c6003d005280d000e0780c28405068040c40341401340c2800300c07452040050746841900b0030181c0040d58800d101c01b16600c02110b55026140141c102e84c1ea840e84d0a0081842c41000300041507480000200200409040140c5049074490841418521802c0380166119001100c4409440a400e01d280d68483d07142114840024028240000c0808440e11 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 179972365 1250 179971115 179971117
    0x50304150207090501030b010305010c14040b0d1104060305061504031a07110703060c030b040204031e0519110103050a0905061501050c0601080f0d2c06090402030a0b010f0302040608160203040308 86
    0x1001f603546084c04801002030203404cbc00340c202442c00c02d140402036090900885001d9024a01400001030408940420008007980c8400c190288146d5829100d075035820f801000f4110460382d41e070107410341051540e4800c09820a443c1540d0740207c0f60070488440e01c1103070031300010085c030348010482c1803603c290385940c3c140a000c020718050100880c11040301e07140035040c0ca13500c90b051030041b881080108042003410000343d02d070b2900c100c03040c03400d04181d05040b4a8a01e000607210400c01c2c0b01c5100c04200049801241705a88081c0c806104075030314141100100e8648030800b90450700100009500313001050801007403044141081420880741c0502c580c50310b41d00b41c0060030301d40e008010500001c01c00b0480c40307120310b0b224074113440f164405002544004000d8404014402c001d549000101ea40784819100f907108003500441d204c1c607055494030080c01100410300e01145c6c0900c002c0e1200d07880307030084a007582c0c00790321488141c2c3c60b090341080e0303440d244010410440c0014080800000e03e20300c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 179973615 1250 179972365 179972369
    0x20c0607060209180906071416031709011a06030712110d18051b0a090b0a05060c031215030d05030604110a0f0e0303120f0403020a0209130618050304150207090501 72
    0x10a00c0c1d440c0c600117038050700d0000040c20030414030030603840c3c040d60303541b2401c1110803443c2620f08035860a101391400350b458041300f41d040c86030340702044208060500154001c0819061600480320803405041c1800418801925031500081800550010611007504002c00c1c0300304c201ca68510300018910301c1c81c1159040240b43c0b10292f0380003034140034004104003d90081821280300d440703502c000400180708180038428041c40c1d90b1140149030081d510082800010000581603d954903607000996859034094082c01c800c00a9a20109540c0601542c00c46402e403000340040540d5030800006a0382070b000181803139030094580e5034241c00420304c04041d211004450316140c1101c0c4400801518070101d02500c0340c020381c4140800d503240e0b008034100d50b400a0050004e103407191284d0504900340410040003a401604003410b00148113080a982c101150203900100240100310540e1a00243d0040700540550300502c41404558003008460005040728012285c0003580d98498806030340b0b0076 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 179974865 1250 179973615 179973649
    0x1081c051206010c020d0c1205060603070b0a080702070f150f1e12020f040b04080613050d111e1606020304030203060c030709030f050309010813020d0803060a03080309061005010807020c0607060209 87
    0x108d000c2d0781001001c01c01a50420011006030001700d0a0448181140c0035055005003040380000110304001e000780541805002d280c051a480551190b0cd45980356450700c02c1000001ca1146220074464131504a0548141c0000e060a00b9106168070031101c41c2440c00f000010aa42006402841c0b02d2900040004100d4455907030b44480c9044096801c280008011409400c1306d1807071000010307070100c0c4d90300880b0303040d0030008201584554003520b000140550314002c94100210703c9840c1d4000900d01c1d9180d80c4090b070b402030071501c0340c00c00c03a01c9028612000b07415901c10000300340d1028403031001c0e41e031013001480c15001d0380750799448000a24010000c140d8040e04006400300983d68003014069004d8001035041040c44400d5003c00d801c1845440c000e000e130400440410b01d00d40e50002a00300643c5c001003020384900b41000540e0725080140d41c2c51066a8a240001611354024a01148a60700301d80241080350000020b01c000c3e90300c000f108642107076003003040106c1699221032201c141411 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 179976115 1250 179974865 179974889
    0x10e03070c0e010503210f07080a03091209081b010509030d0c170304020f1e0406060306080f0604030f0f05091002030d0609060b070204180b01081c051206010c020d0c 73
    0x50b003500400d0110041c1c201c9406504031031148268624041440d464481114185550b941a2206004d07a41c4c02000401000b04a0015900d448154140c2000c24414080c2c504a44901e040e0901520414264840c20806030822045c00300204410258020281e5060610504d4210045d00107418005c1200c1040c0c0842c0d43c0d031003d4802d000302113000ca480c1960300004d003032560400d600006e8005019028440c8500c1d1506410304441e150b024405c4e40500d0081d10900a0540324900600a0700250080040b54452085d80c031101c40710005825004a4058403406e60b4940000b50448182c909500008140401003080c4504c5440344101d4400301c0c100c55002d0f680740c0d100319555006640c4154080e071041414100248140643d0104484859a046034001440414030f00601502030002c140074042483c1e10000044104000c5a003420402c0c074074002c1081030100010588650195451145140e038a081c0003590741e5000b0405017080b24001031003005500740b00c1d41c8540681c8807170b400c42d00080b16 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 179977365 1250 179976115 179976119
    0x60603010c0c1b03050d0903170405060d1e0203090a0204050603010b01051e070206040902031807030c050f0a0e13050d03060e060d03032901031a0906040213030b040f021e030601090509010e03070c 86
    0xc08500d927010580254903d5030702c0c1500d824005a21402030a0140114035550007145c1d01c61a00d0302c01c0880c0001a80c201951640b42500090340c4503030507110241e000d94105070004000707140610500d1104c8074142c640500701070261014202071a81d2440011800740c0401444000d0b0751014003030401440078000c0969607141840b29041062030002d10185c0c0c40d40200d00500c000b40f09450b07044107654007a103401103100c00c1c0304002952000030390321844000700760701c052208004400c06140341c043d00440c100c03900824040c0d01103080743e4880c070070540416655808104649003010f45c02c000e060080c40c0c0800c08460700301018003071a01107850000d1165a0782014005960980541240f03500101300c101074150078080411a841c0c0010240c0344203d60000745182c0d9501207140c00b00185810801091051406103040e0840100513882039100e4811780d80e020524940d00201d20307505c14006809881d259182025000152602030304004080d501c0c0c2d1030140720303003030f00f00301810700c29001e6445000307014 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 179978615 1250 179977365 179977373
    0x315040b070e01050304030f11160f030b011a03010302090604140f060108060a0308040902070501150905040605060405060315090c040e031b0d0f0f0207030b011403060603010c0c1b03050d0903 84
    0x1c01044150305101301803040101080d0024544802080e20f4240b82c060340045070581f60615a01d5102c1c400b0361944140080341ca050a030b00010207613449002c404403c3d0f40ca4001d1a0f54181d0b5041a0f10404a01000180010b0070b11024640d040790000c0d0001c82c0000309201c240b441e01f2400ca441246030f82c00d02007040169079004440581184041d02c080905500319250403860380b00307501800180580008910081003000d44c0410740021202c403a01b2419a01c4044041c0507080a90b0159000c5080c08045051483c2a108290003518010020612070303040c1c00302040d442d03100511210940c064140e15000944940c0600c00030340c150040910394460720b205614940c05020307080c880c01c40d808280202825500145122101042130910304407107440080b040340b4000140c3c00041896000100000f41d00b0000e0180040003403003101591415920f40b41410308072900ca4005100155800440c800400c0c0c61015280701181d0805200d41e520b916916100e2404100d0503040001400c2c10004000380 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 179979865 1250 179978615 179978627
    0x20417060703020a090e0c0f1308060108031303021003240302041a10210c0c03031a0906040b040213030b060112061511030c01060306020c0c0306010e0a0b0315040b07 73
    0x3107038060400f1404e01c84403902c010003540d620f01842d07040a441102184c5c2401508042c1c1e0440040041e840b0740d50406807000708071502c070b6441901402d00c100e90001c01c0c2e205c004001d50b06445207441e0705540852175a02000800210f800c0b1010906907512606064500f00c101d420240100c22001c40748600d145106210459802c40980200d002003485845c1c9156034078904030300d03090000d18100e0720b82e03541c4000c0e1100c409040c0c00c05602c010300d4000e103c03410540024170414028001e441c100023030b035014481070220301c40064446920000388000100c1d540f4040d40550806030006c1e10050800003000044510400c05402c1680c041400404000c103035a444880c08031181c0000780c09206c0f586c50b041202d074925098034000000c0c00364140b000a84010104240e81003100144028054296a8107011000351f2003c082c0c2105802003481e818140c0c1400218517040307039036840300c460140da140481100101000708843d64580503c00c130b8061041445090f55000318040c803551481030422080103005 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 179981115 1250 179979865 179979871
    0x606030c0103022106060c010501060903031704030e090c0c06040807020a17060c0901110a150f020a02120d020c0d0909060e040f060b010207050d0303020316020304080703030f020c0402041706 84
    0x1094010000b0004d10344e2075001600c60200c007a01c00d070303500b80c030342e9400106980600c04440a00c3d40c07800000003007140d8410318450480e8081e440d10740582c90a423507442c0a956049030007a0106841010002d46400e0003050306901a03012010707a82420104e41400c0d080200503034068810000100707000301545010441380008000002c8140510403030103508540f65180140022541c40004c40c0d03d01d1140d0041c0010959000080c0c1984c0050100b480c0080055400d02c0070228524a41049a140090305d03100b11101400107400411201540d0040b0a503d03911914000144540030f0182141c804030030400304510b400300b13846800e103442c18484400304894040c0d10240d12030017150148000700d0135046140c41d00540024021039900c41c0403005071300d40b80060b8025508400142c00d07a1040c540d042d40510300413590b1a804201d041d4035004201d942c0d000354015041c541d00030100801c0000d020f051004800703281801a5451020700e1000a0101c1c0c01030343c011001400c4c1c81c00c905400c514284580c80e4 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 179982365 1250 179981115 179981117
    0xd0303020c0705010f081302060910030903030e061302120304030c08030d0e15010605030a06030506090c031006031101121404060f05060a290403050a0317010803040302300a050606030c01 82
    0x141110b24100100004401f07131884050411b9640010155240d8078200c40d030f0104050b140780250750420030010001c110800c020360000e0b180105001d50090f020800c94002c4500b00742c80e05182249400300240042d0052064000788010800000020786841e0710b080100b1404003e0340d1641e880101d0102030b2240b90f0f0980e046078010b103140101d15a079804c910f5040d43e9081c5042d035202e9603840c000d1002490507410290007441400100196801e00050414511000703170140d130208810f8030400801d8070002e002c010040d410812525020754464500b8040c00c51540101254650ba10502d07541a070f44151810b44507251950b00d030401c0580c8900405030494801d85424190034609610000c0700300711800382c480800c116001d5100c50790307049410f541c0956046020360350000e200f45400b500f0000c01010118502603264000150f0200c04019101121703006001030840d04070400c12841c4aa101c00025103945241201003582c4c00c00401220b480c00740724600400b040c0c10700c441058604041d2190040c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 179983615 1250 179982365 179982377
    0xc100903020310020c190201111606090920070c0f060e12150106030b04060b16060c0f0e0f121005040308090c011403060f1302041404020a0c030c050c0d0303020c070501 74
    0x5c805a000000e005802401598100c1075030000303031004031022448151482e80c103125001c0050014850b5141420440b007a42c1c1725400080d0781da0405005980502000000c00703006250400140c400070720080005510445100710309a84850300c0d0112681c441c0c10030360005042114107241401d11103c4100500c0056004101566485031140ca503500c05008020401d51242c0304c0b15640c0c1c480e0f801803400342100200264450060005110490400700029a42c090410100e92812401842401803921165842c0c800f940411400c2c040c000890341501504104001402c02240780e040c132500128007854100480d0030b042c5402c0051004402170b192002d40d8109515802c0d45a07000800c4403001c9083c040ba098903a07503204009800002005d140380e4111040c07400301601022541e0082042d07402c00060b00d13082518900a01049015050280010070400100040400e0142440b0381c1c0d62803080382110003800606000c40d510704540841280801d8001c100174113070f140144504406000c0a00e041c6d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 179984865 1250 179983615 179983627
    0xd0801080613051c02010915050118090213020a0305040606090501081f02191e0302090d0219081c1b02030a170c0d050a0e01030605210c10090302031002 67
    0x950384414028100206008004100e00104207003130207084000d180511504804064159000c0d0181900d803a007102d00f0004402445840f050b140304184c140c031074202c808040c41400c0d82040c4024624001d0980c0c0c40345800301c9d1410000d4850000b0071042c490340e40d001c102801c0915000b001c1d41c01070380280011038140001401001c800286086000240d000e01e05521444900321400900c00d8100070146000400d0007d840990410075580c45417000c458041c50356086aa000c600300e0268414050b031080c40d00da601e401601e01100c509034400794960b146c070707001ca41c0c03003002c41c0c980564410302c9542c0c44441c02003280b0983e0032a94015205014a60340c004403200b46e070010391606c4040000801481c2c840498840f45140f42d8150b031404d414190480c0c21500e00d445010f8000d400410110b400900c01128031082c5501c2805083c0c201c60300a000c01d001ca0210003a6100862400302c0a03155510414490807190384e40c00b2181204207030680ca80c52101030850040c181040300c400b0008050500401070 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 179986115 1250 179984865 179984879
    0x909110a030201051e190e09011d04170903100e010b0307050d0f050a120909050105040e0d050307020a0b0a050f07020604050c100509030d031a0f030a060504030912080406020d0801 79
    0x890308400e44a40303285c044100e50301a010020b000b140d0f1400c901039806111412415003068048545e20b0080715405500d070b0740e85451104201680c00d117826410480404240000c801c4040ba100c0c068504c09501c0c01c0c500d40001091401c140c1711030a03803030180c0f12010101d03d07a4080c0300e01c181021007503002e0117205042c980490a0310744000d5004045100300d40c602000e0120600491410b5503001480c0b11300b00401c03450003007560f12580150b50046150000020701d0703180c81d10a400f07088a40700701030301c1d07000e42584055400f80c10003004802540107144441e0300040445021a204d4612074000181b41d0a01d6410112420320041c10202994000000e000c0814030000b403110b410715045480c8920b0411042d012203440c000e1303007102a098410f41119440164140c0c1001000914903020030307100420700c008000a080c0d41aa020340c054100c2c981e55404500c0c1900140d0b03016000b41030800360190b482d0f90000505111340000d441d601004102403242c5681032214124803802032034511070350750504d21 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 179987365 1250 179986115 179986117
    0x2403030711061612021605030a1202030d0e2a01120b18040f02010314330316081005040c060809100c0e090105030f07060807020c030303010909110a03020105 69
    0x190180c1c01510034040150380e442e08039a40045050040c100701200791410400c10704400c0c883d400035018006443d6011104c3c1d20451003100c00080c000c014a600135184d5850203071004009000f1400100800005601c01e40256a00e00840c43c0017031003801e00b0640515031400213400b20ba0f50480a402940348140c1c2c2c800b00c208944006568000303450000000003d22045062242e020040d0b5010108414002c042241c88207441c003c0e00c0c05d014200c80301c0d242100c030074070403901600d00282c1c8042d2140d007520800189550a20070500031402e0040010020f4a481d001d030415101c8401e031924144081c4006200482c80c174030b50040c00380000c0c1469501c42d10381a01c0d81c007800301000408800220707204410407145c1c0a00c1031603e01040540d41501000701000c0d06841c81c6030003403900e00e000043c00d02300007a05100540342000034001450034905c2c102c0350780768068a048118800ca81c1020b14954061000714000d007036044000582034018a055250161191030061246012071802c10140c1d801c84 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 179988615 1250 179987365 179987377
    0x60f050c2b05040c050306070f021b010903050a0b040c0603050415020f1c06140102030309060f0415110a030b0d030f080606040b0403050102120903030106020c061b010212240303 78
    0x10050724402803164254203a0900da04000700d40700d0b04010501052080e40302e007500550b80154141c0f02c2c20f68404409440c00044a1b02800059000e24811541320030400c0d407403101c1d004145800800b0942d00d0f124507160228500066482407100000d200820250429800003404141070901c190f03e41070304c80781680c1a86c420314110fa1600003d0028180d6048003c803015105004440c048210390a200a0001c1c110b0303020b103198002066981080075030002080c2c904c00e07034002c001080c9581c1d40b1814000d000e0000750003205c0b40c487c3c01000311001842405100c9940180d40380141c2c5807040307404020240c500100b02c4501603980100e822010a6010000b4200040f0038205001640c40d1200130808600c07555000140101c8080f40110420006400074076541e0440d1000030b10a03104c0c020450788a102c203201d101c000da400001c481e40720307041100c081d015402200030325407112118200f446003641e00000404004503031102c01c01c4811100502464075400c95401101074611980010941d130384110 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 179989865 1250 179988615 179988637
    0x8090a0f030f02041a060d0605090a09020f060a14070f030206070c03020a240f09110f0d060e120a030b090a0606020d0e0d05030406020703030e190314070e1003060f050c 74
    0xc0310701c560891402d41d85c0820030310018204c29520715107440c0d00c034020b02c254020144211030400c082040024039014010310190024002c202c042c1181082010350340c030a01d10482400140801011210780c450040d0140a02910a00302c441150386002030500c08010041800c1c09107419501c2c0110f580090140c4645500c00062980e0180901010b401e26502001110310320781458480e035000740c62038101c5d1079100d105102c0011170400000401008050030488290800d100301c5003003012444a80001c031101221005646012292080c0b103240350788000611004a07072150107090407400c00c28030151340800700c06800c20003d418694000d4880c1c1c91061000104400c610651034669101049500010340c00002c0740c1d41c0d030b583d44078040d40314a400d00c015004104c2c21034914480341444540c03112400303581c0d14000d814a09641e00d0590030180301d480c0100501c80c04c00c0118050421701c41480c007403458000028807852562401a090720790401d251030050f818102449130001c0c211003525021009 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 179991115 1250 179989865 179989871
    0x270306230c040303051c09080c031c11121003150207052b032703030b03070f050904030507061805071701020c1905030705060f150102030a020a03030f02040803040308090a0f030f0204 80
    0x804186c1101920b65000040c28401000400503e51031000000344405c80707503650521107921040b03440e0307011590500c0309480c6401c2c003002248640c05100e0346040d44024124140b40c220f41d02c0351203100c6c01c80c0c14040d05280d03603a40090014103101c0100114151034950800c0000d01c2080ca018000f206d203050226a0245500c406400420000c52000814a0040340d0b144009146242c240140a00010801c1038001d0061410104030341d4000780c0c0100035688058155503880d01c0d1680c00301c2c0c2c0c1360302102d029201c5503074900310008040844800c1145c000c1c0590000c2c14194200100005044046110415243c0c0304010500b13040340040740c0501848143d07004807444000500b0f08a00b980305100004116009840400c001100118007640c0128406160254031800400c01a0780c0c034403680c50101e02688c04950410300092098001404141d8590405414150b80ea02ca90b03217580c009400071601c070103003c9a40000c9040091544001745101c01d01800554996200d030003890741e480d800079000300d031 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 179992365 1250 179991115 179991157
    0x51807140c01060306051005040606050f0f1305030a0c05130e07150c020a0905040506060103020f030f060112020403080403060e1203070c03030b0d0b0402010f020c01270306230c04030305 82
    0x74203621000045070450001d00407440d00a00d130300b40031002801a14442e51924001040c943e01c01c00a483e120b051003511189001d40c2c4004031035407908100030b0404062000580409e40b500c0a00622401e85d200b0004805514140000c0088501a8441da000414038260008610300c40002310b5104a03504001440001c203034002c001c5990b0104030317402a410020a54000415009d5a4055849940900f041c1d0341161aa540114164072402140158016092010841c0310502040094000c0c105040c050040181c40000e407090b0380045c1e200791a441000b14080091190600840c0381d8111500c014004190380300f0044401408054111020402403c0d180010180039901060079007100402c0c810110308a03180c40207103843c00f124228000307222000712081e0180002021940400161129009107261417414140d032114061958825032150100001007815480358404201501c8040d81c0c804035841c40120003a070015122203110081000108007283d403201c180d0320704140f030348400d1403444 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 179993615 1250 179992365 179992387
    0x1051306020f090a231c1e121112040501050a0f03060306060e090d0305040b070c0c030b010807080d02030406020309011115090c040e0f030a03050711120405180714 72
    0x800307101e00d0f03260090740121000c501d0805590452603030040e111219041c810140e07040c001035002d55103c8070b101d101140400b100149810724400030000c0c2c50b0f0901c080b1008591513040c07580300c1159119021803201da508401040e400d0001c5114040c1c000f070518601441c0100082c400e00ca00000d000410482801d10301c0814441c0e0001401560000c81c10300845407152401d40c04100304ad590a410351040c0c1c59200b4495019002e40c0b8406d98015180c038440740c0d207080c4203540c2540002c90031564280069004000540c10441a50190a00500400c45141401c00c41464600c110810105643c410300003042040c0e40013080f6030350741d207081c80c14961511004801d5441e140a0151900201c0303805020009981070011340309000c200304a5052183c19000044543c035081c0303038045400d1070b81003080f0070341420b8000d8211075006011850a40300e50000f082d80c40e801c2c031595000100f46c10100003400c01091a08884a0814142c4402d003120b607410200301c044c0c03034880d4445014403042c4011a09004007 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 179994865 1250 179993615 179993617
    0xb010c0803220c1806060c020907031806020c0106080d02060f060d0c171f021602151b0309010906050415030e01020c070f080706030203040206030406050901060b0f0a090801051306020f 81
    0x500e0f8407000202c481d0303480b885452a1070004160b40102d1620b00540054154030804020390b03001e80280007080e0985401c2400c401900903c0311030720041619080c1c8000140391803001700705218803071000054075402c0c03508072400c045046140c181190b00440074480e0b098100d038241d5403c40000c4508024058251410510140c980d500c092140b84d40900c0c200800900494166042c228500d020007445403240810001c1b170065180c801c01c2c1c1d12900440c0170040c1070021600c00000541d0402c41d084ca8216442140c02a11080042c64070740c001081c1c0351030f256000000f000c0030708014144242003034102601c8a00c0c40d02c04409031000c05441d040800b01200c0c01798121580f1002e1071b81591001c50305d0f034a00f2207040010303208078180ea03ca018000a02a4844e00c01c0d680650f5006003d80e1440e20389850342c0c0c0207800041d05403d119582c0700000100303402410010001c1e8151400e01980313235500340d0720150101e5101c1c2c1c000040d03a414a01005420030180310407050060b4001001a20784503507801c44c1582e = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 179996115 1250 179994865 179994931
    0xa0905130606150e1f0e040207050a03050409141b030618010b0a14031b0d06090c031a090f1311040c0903050d05040506120403030212100503010b010c0803 68
    0xe02c0c40e007040840c0c80d1611441c807903600000c5481d5443c0c1c82024500f404085c5801071000d104001003c07104101d524030030840c00d040400300034005810320005486041c14000d040d6400c8000ca07400003410480c510b046c2c0505216106400c0c0e07a030400703150140442c2442400c000f1a442030308070000001d201e81c0e0711042c0b0b566000e001c0740b92448642d84c40701e1001849a1000c040354012070700c034005200c2c91b6040b00044034070481d0031a80c0d0b103c41d040d280d2140351003508040101007003552244004225504648500300d0081c5040c0d5001c03070782c07105020920f0f07554256091080d000e10200420000040c0e0a4030f15660440800420312103284417509060000a02c51071607594020706000440b5001075004903c001581d000744103960f00c00c802e400040e0b51318460b03441010381060040c010080084a0f03142502d602601a0401504e4031081c404001c21240040341d1016291270101c5003441a03050901c600200100d080c03c040c00c0c01c0e241c036241c034403031804001e185182e00c6500940c02c140701d603010110041e07 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 179997365 1250 179996115 179996123
    0x1404151e09051315140120060f0906090d08130212062d0c07020406080102121b0a020a0809030715030c0e0a0311040e160e0105030f0c0a090513 63
    0x44410030010300800500351881a1482443d241c4207030700c20a00b940c0320391204c07250b80d02c0c03030500e4007072030980301400c0481002000c03418011801a1000420350504d80c91711140160b20240c080d51030318005e4644580f0b0b02605800c1e1a5211500b0404a00b1000400c881402140d04280049560f1080900c01c01091202d00941200d19080243c902d403c000602c2c40c0220f00c02d2801c9480c514a90a95000c6984011502d0304004800c1c0042255003240c40c0c02026000e0003d0070115505407035040071030030f81e03000003a0441611101d004100035000c0010f0100288426104014130740108824002c1d503036440404050070b02c400c00251014903a400b004448001d2042c09800e90b401c0780c00c3c40c8003600404242140341c000c690444022001442c09070170f06010350340e01c1601340440010707003410720004088105440d003d51040c800030301d40444029203c04003e0082c0c0200f144558148801d050070101d00341b192a015074420200e04c038440d0781d00e41800b02612081c820004103544c2c0c503144ca228030115418058 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 179998615 1250 179997365 179997407
    0x50a0e0106060504140301090308220803091b010203041818020301110d3c0b030f0f0111130b03040503190309020933010315080601050907140415 64
    0x10302d02d90014094002c80f501101150000d080c0c2d0010306080c0e03440d04c54000c1c00a81d07000001001c140c175003036005410031031004421000002c80d54500b01c0c1d550042c0ea5401040c0c1c04841c1c24085800d1000302c4089003c03083c8080c0d03042a01d03188069a03002e00c0c52021800940e1140811b9000400d080b40e0400c246400900038020304080c841841c070507a00810310410310500f01600031440025070580c511200320721184541c03100040340c003042d1021030301200f046016038075000d10001541c0c1c01c002c5200c00007a40800f4107907009d8507180050859400f40912403110b24140000301c06400042942400c8900500d1100c0c1d89546170314cc0241140f00314072403078000268000041c00110707415030080305014401c0d104d165043c2c8800c00103c402210307080c020b5813030094424080c00c0401014100802d00305042c1000b00c0c1007a1403140201c070301d4442c0d401800351540000c0040001c0d10b0072034582500084981480039500341031041040903031040e03000e1070050303006461190961510603a04480c4e00d1182d11182 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 179999865 1250 179998615 179998619
    0x80403030c0b0907060206070819090b01290304120203041a032211040c030605030703142107110d020d06050f070e010206010509061206040602090a061d04050a0e0106 73
    0x2034480780105000741c1d03000300d65030700058207028009180f0044d5000764000301690380d01c5c0101110305580082c42140c03007041c080c040241d28003103801110700b41482540312120543c141103c4002e0241100100982c0f40700a03540b1104c2c0da4242c0c01201c0e0000e03042440c903900c2e8141150242c0c554402c82d8064901403600740d42805171590184050341c007854502c400d4400004802111a40c0d0401d2003001070040d4001c5007160303115290503031050681c86440c1c180410851b03940e500082c24885c07070741e009071070007200c4240040309000b041c06035502013400708c2410b1104004a1800e49082e0040200041450002c40a02002a0395900707516030301c00c4e402031031212810414900000506025903010186803112804218000d0003040d0011640e441a0b000748050703032810b000c01c040b040c03000d0030250b00000c1008580f03441d43c0d000e0240e54403403409000c01580e20600d200c14488101d4044c2e000c0c108001489202c3c14016041050100c040701c0215008582381e12800d030034100800c43c0c0030344091258606200 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 180001115 1250 179999865 179999867
    0x3133c03050c0d02060901180506121005090106020d1404050603010b07021906170a110703081e06060a03021b030a0e2b0b090a0c0e06100c05060a1808040303 69
    0x808003500c0c424030548808910350014000c0342400000029070244007444010038a5205000c2c1d00764400040c0409449660340380007161603980808141800308051700c040185009100c01c0c444003c110a55001166614150740251124101c0ca043c004020060032414503108010b800d40e009084d00070302c804c1e80d950751491440c100b2b9111001c00c07409514240381da400d02c10080d2004004403602034803850f01400360b02d0081c01c06808000e10341c1c100d041d52042a000c005543c03401801c26148261a0300400b03040440f048190307130807480c8090308281440801c204030b13a11036000ba100c24100705d05002d03840d1015024983d0094009821600d8607110104042040603445142e50341003030401c0d503100b030300100e50a0314500f0100c5107480356008050010010781c00a2554a08540c0c480c0740002a01c6a10045070389264084110b548000c5102a5000c2408503034a00a5001804ea03111030610102c860615901c080c0c42d050000d2035281c400359612400c03c48811a6040035402c00d0703000c0707500c668427510b80c68 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 180002365 1250 180001115 180001229
    0xd0807150e0d050a02100501080304050d03111207020901120312020c010e1606090501030504200105130b123d031506060807140f07060603021201060312020313 70
    0x1044c10300611465078014050090703481400c0c185c91425000c3c516040c00d04042c0070300c9443da040120100564444460480481408100c2030449038076a4190360f52000c3c01080000030040c1c0041c40048030304145000001d03085102840351440c1080d015032500707d1400e00500401081c158220300d4001c1404c071145142c5099120800d03101580c50b244015901e803401142100c10445000b00586804480069200c4200b01c0504d0403044c1450010718144010344510000010b036401824600400309800008403c0071030358a6005070581d04888801c2c80192080c403c0c0c080810030741070044151541e0341c803048550000840a150400c11018113030896540001c0144000d100314000182e07481c010802ea1481001d0004007020101109400c09001c20118400b075400382000b05c0c0d02e280d84c2d4400000613100e4219016030303a800d80c8000114103142d800c20005e6044010141c60464204121201c10f810242c007160003680c0314481d1080d4040c62a0144070240030f1166041d0701582d0b56900302d00030000080c1 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 180003615 1250 180002365 180002377
    0x313030e180702010e0f0f070b0708090a30030816030f0c050405120c0307090e0a021e0307090209060a08063d0906051603020c120d0801050d0807150e0d05 68
    0x200c80c0030001c406e21140d12038a52a50705800383e0000e40d01001545404409809030307134084c0341d40c240342144500000b80400c02c2c96128a40160024070801510580c502071030502c607c061a1044a604150380d00510801004001540c05a80d000040c9400c038070070303404102402d2103c002000700c611341c904007801a4115216440c4102080800b1808056011440d9280300402600030600781c0d00b000202d0001d440650704d07038412446046450340145c0d4803104040301800c07c0045e080149185901454109601d9812200c14a80104160845030320b40008403114141c0503d0b00740d032151906000030310303900095a20901030b2980c00d225901c08620756941580c0c80d11105000c0302426952003000e81d0411814480d07580419000c0c03002c42c203200141c00c20914000e1207841940e1352561030b1030018803541011164040d40c2d6000e0700c60b45440d25000344007680540002c644041c000750040d41c50070380900c00d003200108107009030682407804900d5904a00d00ca20145025a4160440110001c1c07480d0051 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 180004865 1250 180003615 180003641
    0x10309030e09012d0b070b090f100e0c09070f050d1e0501050a060c0302030d09030216030803090d050403050606040209060c10051e06100809030d020409090201090b0313030e18070201 80
    0x1602e0707001010201151013003c80b00ca4140a600f44111178681c1146110020503100d40c50041070300c2c1012009083c00040070741120740100113040764102028519051703c03140442e001303650000a0000076604a4500180a54145803042d501c249020407440a03041c44c00c560908100c44403051074a11a103600800c0c140e40054030b003201c0789a643c070800c945001d6000d4019000d60003c10002c4c03862802c50b00f00d80c400740d00900480b107a416503c002050000410f903c01d0325204000b000b4030002c00001d00100003111118a0711900745821a15650380306c210223044140300c2c580c001aa1300054403806c05840340a920341c0195006078011505060103000c0c1200c0c01945030709044488811095800107450143c0009414041241011a401e0342d0050003e01001440d110511184c0b80c140450b00082004d40102180807800082c0d5100160015880e1b41110f0007400c01401000000008450b00400c40ad0701442d106071281e5400300804c8401c1403001900300e0f01c0841504105a41e034054002004506078 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 180006115 1250 180004865 180004919
    0x2240c0a060507050313020d030509030a0c0f06053907140a170618010209060409090c06022802041401080102070b010b09010504090b0303090301090c06120b0609010309030e0901 78
    0x5450040f24188400c54140c40070b440c40c406d010026040841c2440a00313403103414668a000e0540d00017034500320795820704841c0c2032040f28003480350304a94100100144880d08202c0d082c10044401c01c450001025200e462103035940c4004800c540c03803040c01104025518090307840c02c9446600303c5040800503444107003e114044000200c0c40242c200300a0801c0104c2c010741480e803180c0900d0705d00c0c4240c40360018a10764007400641d1440e650b1000400003061740001c005a00c040919110b00201d07034541c8140195041150a0212401c91118140c0703070501d1a00d00c0f4201a42900c00a4000c1280c0c40761030b403400030b00350008905500158010200a40903481c00001a80e9440c10000c0e58812000003a00141c020300041024001c540c20161502e41c0040a6a08003441040800d00f100c48508003602d40d401070310000c01140b80c11520417519580c0c0440140100414600405c40324820724595034100365490700f844090501c5040c00210740340c0300030905089965504441c0c1c0100386c9020201403c500 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 180007365 1250 180006115 180006121
    0x40f0303020d14160c030219090e19022b151802010504050f0d0605040b071101140606090415060806130e0c0114040305030a020d09060201090203060402240c0a0605 72
    0x40144101001c101c56111141e00d0444c000048100d80c54282004035001c8880ca40c2c040011b954203180c00d1005000c0300d01401c0450310380b507450400e6403020091100e003a0407440c030304241499645242440c403078040d20010048200300382040d03006061000c0c2c150083c403442c03000002300710b4914400300e0091181c00b020700a6601c00410030080d000007100c02030100354100300402087c141070b0403022041e00c3c014114602041a91219016101e08460454010004c0410440c40c1a0480c5070301080a03201e000030000c401e2181d0780c486070024041c200f0303446840c1c0801d00400640e920b170010f41d000119100b0a8400701e42d9032001400b14082940d071644030f000c60114601c6400311900c102d060035980240100040b000c50001524040e120380304405c3d00310390030007001c004903d08000820103904d1035402440c503007c2c0854020100c4d14240c003d1411a41810501800f44c1d600007540c681280d01110340c81d41022190010341e00380040d0101405c02d401c0082001302141601048040075a4000da805001c155 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 180008615 1250 180007365 180007367
    0x3020304090b09090706081314011b090806010e040807140a0201080a090b130201020c03070f0906170d080702030c160305070803031b160b0a050402040f020405010e010e0a0b040f0303020d 82
    0x1c041110f5120403030340240b004200f094030074042d03241c01c03000b48c0441103494013040d1118107001c4c1c101c1910502c0781e911000010250441d40f1070f004600401480c01c407410361305102c665901c0f2041840b900c8001c22100c0c02050a210952080703d000d2036111a42c01104202260610340702d0303482d58003d0303010403c100005640d0b138140c0d001d0443c1042e48621080f05581d40ca03490030b0802000c000d4142e046101e65401c04450b034400f0411640030b00802c04500300c240c0e1400300c04209840380ca0b0014407000519030700381108254005601c403140901400c10755580e60702c81400b2440c0d0b000d200090405403203002c840c1c5510a1544c01e220040e0390080c1c050f12038168442d03500380d43e20306c0241d4144040c1c009440000034100706010240095034001c0944441180f2580c070307035a481c0c441c180c8403164240e6030754060004518103441002c466000ca50f40550416251100282c91540c005900300c0c14422a100000143d542d07519502000d0914400155181c0d611105008039000700747c0411800342c07182c16080f06000d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 180009865 1250 180008615 180008629
    0x912121517070b2115040e0f0610060e0402030a1b0e0411031b07080f0307091401080403050901031e02030906071d060d0f0b03011b03061406030115170403020304090b 73
    0x69000d02c08011503040358504407483c400801088507000d409500c5d10006a9a80c500038801900200341c000c00e071081504018501341403001e403000c48171500300e080030000f854002c480d2a2692030100c60058507a56041e00341006000001c0809a11000503500100c5a80e008030501064400c150380c20000a0001c206400851000b6508280002c009161205090f2003d00c024514940b1540030a0708150505c0201c07040d581082d00d221001c0381c6c01a5051240102c000980716541c00c0901e410002401d090318080c1084c400c9150311410551204184003444140e850564180c1e001154210b40c0c81c5420068283c94070001e070383e02800a4803040c498110354010810030484242c0c01815285406a00c42001e002001d21214200c0229100e0a0f0481140c0d02885014105c00d20400025111411031f14001d0896109402c4030415030800e0690020035100e0b0307410380307040d40e81003031211100b50006c02e400d840241d080000d2052062444041000305980071002d44103c2d00e020381c0902c072010240080240c0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 180011115 1250 180009865 180009877
    0xa2d02090402060309030c0a06060303110a11040b0625060516080708100e13020307380403050712050c040c05090103091425090912121517070b 63
    0xc056100004540540b810200850f00503101400312842e012071000301506101d8040c4050380d120b90768050030800e1540102c03400300d540400300040c0c070301c900700361703682a0b8102090080103026540e83e06401007642c403a202180d07109191011442c800f003487c07081002d103074010400c0c2120b43c02d040001052448010444d4524647c01035160780342d03a1307a641c1c1022580641c00030901100c4c4a03d2881c00030f80d02c00f64908442c003501440c40400f6041526005061030a646540656094003100410804003200901400c80c65039440e035020307086042201c900c0d03616001d1600003a14502402c40000b801c8041a42c210707000303074032036401e070742d101413581c4204411214502030500c040b400405c1002844d6100f80c0c0410802845501c0048400072840800e61914002c440c01060a854681c10345001e024251005001000280028880541166140c1e011001d000b0045018440c690300300703542c0503200f03800000600404100b104e0003241d455403040c0d00c5071f03480210349d03025008034200841d88144240c11904 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 180012365 1250 180011115 180011119
    0xf05010f08040303052d060102060c042603190207090605030105070c0803060a030b070309030305150607120905040c050d18020619020309040f150803131a07050a2d02 73
    0xe50b0300e5840540c09444014581c10000035807144160f102842c422100900031a001300f2481b1502d840300019291050151145803100802d001c100300c28409118101c1e043c45c0313145400582c0060004480d80785001d0030582200e803401001c00a517040d03500040f1642105d05c166010700106a85a00b0700d4200ca000f5a0b1280000381120001b40100b410302e0019030b00104040c0040000303d40e02c1e240e210642c1c10544030100000d86070701d0754034149580f500840d500010003030900e400c2d03882075200048052050070030003400c2c0704c544103000d500309005000d2a0f0003408050001d204280c00c01100a0044c0e00104c1d804440d603151903841e101d59110b9007100814103074094055450640710f14224881b003072101d80b41c0011444100101c0545841ea40607440401622540126402d00f461202c0c1d10100d03407603081031a00d54410f03c03007403020302c001c800080704940c101c1d1a806520114040d980c84948215400a08a403003a0f001200400441c0c0c40585540d41081504141a110071140600f0640c40030750069 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 180013615 1250 180012365 180012377
    0x120c0606090f011a0304080702040c0f030e0f03070308130b04050a0b0a05090a150b1c060b030f0c040f2d0b0d081806070f08031603052202030c060c03040f05010f 71
    0x804c0c9691048001c54010307000f44603860500d0b689500060a45140840c40800284a98180f00195070940218002e0703880f0440941506418003610580d00e004004000c1d04000105000c03600010300344071880c04080e00f00000719114680f40c246182d0391140020100c80c40003050340050b00b03003940d5204d0603028003c45d0002e0401c1c0c1105c0e8482030b090b01307100034103910925a07490440340b032642c4117000100840c40c41c1200560401090520200b12298410540d009030450600940c4500e008154508420703002c50f000601c01110240c0d810060031071010111710495550341414242c080700001005480e000407050089000c08000c0c0890804502c1000b05860814028001d01d840e94103090a20808068a124100700564079003400310303056480c0070745e0000800400c0c8000c50604100d00361001d40c1c581018452401d1020714140028222880080e2240340c4d48404400c554003800b22101400e0020845c503299140501c43d40c2d141d500c40d00c80c00c02e003000d0202001500394010705605000c144180c03500 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 180014865 1250 180013615 180013649
    0x6042108070f021608100b0402090904080d060b0403050307020a081902120c0d0807060b03010b062b020d02090913030203031f030f08040608070c0b01120302120c0606090f01 76
    0x3510041a0001c02c0000e5009842290f9aa0055a80c20100406000d001007500b10300301c4c0031540450304000031081c0654010011040d55071119a11a03812a6000740280c0d501d40c00f09030090000d122540040a068000090000c1030010000150072401d00840b406501d01d40e03101611640e0b545081d1040d40300111140d115405441d1455105460601550a4039a15150314000510000022108075003044010907148288083d91141c101d103444107900070011020303020b000130300c0b9000b9003810b000100ca078004181044030100300980c82c1c0311500e039070a54030307000c0c6040e00402941020010798007880c9224002020384090882c03141480b40c06401841c690b0b00c0c2d01c03840c10f05050703100620365188001c40100100044001300c2001550b8050b82800e5152424581c2c0201280400b400700000c010719502c900c004500c01f00642030440d03014071544000074140341381c142c1c03c09000001817510380002081800b03c0840104644c2d1144a0441e00b00c8410782c4c03400e440c1107a450080c020481824000c80c14 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 180016115 1250 180014865 180014867
    0x91506201e0a06061d0c040503100c0c060903050c12030f0406090201110607180801020910031505061b0105010b0f0703030b0109081b030d050403081c02090307080604210807 76
    0x414410890341c4082d00c8281c402030b19440140d8040b64003d103611003003454411040c1d50790003480c03600703c4c01c0e411907075280614200c0005c0e6101c07a808a29180c15544014000c00705000d2031540d41c00d0342c2d0150702400380c135440e401c0180254002041e44000d500544102c104058580401c0707034880e8090000c0c200f500c3c1c03103903140c030310085c07150801c101c0c18060702e4000110449810400ca41c801c03009030b03a031411107d101c07090350411103040343e002c80c640d81e0040c03040c1900340e51600c140004107840c038600010702644c0040040b00100c4268003060300660b0014028580400340d00c0e1a402c40b903003203402400035907070324035140b607840c41003910900c25100c05004860020784260000c0b000d26a0500d030a034902502d0794580c0d03040c03504016512104609440107910355007400e0003040c282c8140ca0034441e040c00c2c5075480b81201d0303218a52980441740390315108090201c8541d03041e80c121040c0502113480c01600d909140303680e00400c0d1025288140d20b003010041e071841d20b105210f907140d41e503078551580b0340341d03420 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 180017365 1250 180016115 180016153
    0xd0c020610152a150209040c030911040c02030d020a0e15030601091707091107050105090606010504030b131721160c050c330301030320030409150620 66
    0x850f0500380242d00c0d900901260032210b01c45500070001800603510542c0c0e40401c804c54103020400814141000d02900106141e160380c09250740e4240d4000c1455016103034100d0031803280100b0740456a201003120050300b681300d80c0c50a000d20080e1208510496080881d110030301040b600c903400101003003828403081074200d03288011300c0001821501401c1d1034810321000d84200124281d81c0c40d00101e12075081c0102401115081402c00d0041c10705030601c18002010b03881076001c040d0001c210760000c100001e602c40b01c08021281c2115815038042c0054102040c59404144100b031b00c0030002030000000340c0010703241401605c0c00c010080e20300c5034040041e0703013030081c1220a440c58083e4003540082a2144100b580c611001142d80508043c01c00f4103103041d0070000340c82c050700d03400c0a0006100082d004200f80c0b2180d00f8401403802c0840307280114600e94891f5420a0020302e0400b108641008802182002a14410f44a40d4140310050000d0362610040007414011688050140d048469840c9 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 180018615 1250 180017365 180017417
    0x10801050610050f090a0902030603160303021b150309151006090303030c0c060e030a26010e2a030a0f090f020616020a0f08062401140d0c02061015 65
    0x540f440742822183c000042441d5407e6100c070100079000030403c10301d23203010b21404e80d030305003020110f001e018150b0707e000303503107604580403d442d030418501204c00696420810440e90544028000e80d64941000095160400400030380c4281e0450400704401400900c1102c05440d0196121200c41e0720b1900c1c2103024010f4104010140000c240d0400d001c90214000c41c0c02030941907006540e00d105001008200d02401080d0031242c4907807415081c007070041c0c2403c00b41103814018406619031107a10712510203445c0769401404500094011513111404000135500c100e03d00c20007003100c401d416408a0949280b0f107802442a189205030303e0041c50102c02a2125001041020350b134030000e13501150704402c0f0f80d049400305c10302559081200e40f000700640d41d8041000001c0c0c5902025400709012061094404a4180321121000d01f000b00c81070419504c140d0084407041c00321040c18040030303498074001d0b544060703400303070314803001c03514460b028001e4414944a0340c030441043d428070420144941d40d0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 180019865 1250 180018615 180018637
    0x204050c0c010513020109060201110304060c200a060b060307120f06080102070b010503010501060c0203060a0b011b0f121107090e0106080f0d08060f0906040f0f061403010501080105061005 83
    0x611803401d06072001d11070710788100e010a14190340f800c01800050300c0031400f079104070110380c104110011841c1c00e0b42d003039982080d4800d202141400b0640c41c01d80d050030500d04000b10540c064004541240750000c0c8900302180100b008104181c018401c1c4030141c801101c04802240150f0081540700801c4c3cac1c020703008074150200015566850310f01c0d1a007a0b901c8000b00303441c420006001400141b07000e210340c40c01404641400060000d80303034086500d421000780003e15182d82d03840b11003110303401140010364048129884039803440d29403504014001043c0c00650707040c042c00080040c0301d030040842141c1d540440000700786240c9070038041d40241c100038000090390354890000044815080003298201c444010181c142004c081d0030040401000416aa1040d040c0404030041501e0b0829280c1d00700d58280c8010640701410091503002c0e025a0040003036003803400e00700080004a0342902000c80000b00e00910060340d0790000c103403d950050700c810707a1084c41000a4007190b4001c1c40200b0b000f507a2 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 180021115 1250 180019865 180019867
    0x10c15090804080106031a060a0302010f03020708030f22110d03140c03030610030204050a0308030601031407080a11040815040f0b011e0611070506032a09010305090a030206040204050c 81
    0x900d0341c03001126007082d880760440e42c0d121941032082201c3d401248200d082d03010025001340c60501c0000348110054880a410b001c0004450206540710f1b8048030181d540001a007542d03401c008108070b0800b2400c1324034040c0d28802c40b508662049090301503030300c00c035001514001005a03150401c0070643c54094103d050050300c0264000c045803160207000410f6120014544a10b00941400411192080704400f0140304100502c41030341d503080300805803600084002e13181d0746d03288016401022800b442c0c030f865100c0ca4041082096104141902c100c500410a20041c04c40c0855840d0038040d901901c101600040c420320050159085e2059000d4055a0b002014003090348450002c2d00e4203811031501710808070384400034000f10320b0200008241901d40201098102c000050300d41005028461180c100080403e07103040246e945240984002e4540001d2001d03480d64404459001e00303001c0340420704090001301140e20103d40c4818154041d0064811a903032070b0700300401010300074024000010 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 180022365 1250 180021115 180021131
    0xc09090b0f0604020418020702180c0406030506040e010f1a0111070306020d090f0c050117010308030a0903050405060d060302040e0a030f03050606070c03032706050406120b100504140102010605010c15 88
    0x2c240043d4850b002c0740c103040140e40748428012b001040074007136500d800190302c1d107013800109400001120100d442e07902c0c0010341c81d00ca607400140508013903110044290b0924080b50450040350384035850229140e100421400d91a200548641100305001451a04942d408101164a54000b44280b81c4080000141c0500555909003100e001351015122255801c03018003180d41c102d44a0543c2c1411009248201d600d03660745c0d0421440010003442240751100001d004141c003c00a5501034840105410385400641070382e500200520300c000d038492824280c00c0144100085550a01107815170b440d144c00540c0c054003074003e40340185c1155000380b000c200f402d001c510206450005144244d490300310100505140407101d51224140c4aa11500309208102c066000740444040b9951414040d074860500b1600c40010140c443c06030f034020b40c00b0305064068030f500c81c004009a038645441c004202c2031010049007202e4081c002c003400b10340d20280c1c010102c0d080d0a81402d40e07a402c00004900d001c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 180023615 1250 180022365 180022379
    0xd1e03181703070801090513060b03150a020a080a02070c060c1407060f120b100f030905030c0a0309060309080901050702030a1212141905070215130c09090b0f06040204 74
    0x201c501141290400008401c0c031011550000c0036130300410500400307020318102031280580c1c0201c0d1900040c0b600307699490703c03071581d102030008a410031a030749866060f51a02045240103580310303d55034000200185d002668108882c42680c140981009100700300f28100f00d000d0303c82d000229002d031801e08401442c42d8003038508100c2800074100030b6440303500c3c7d903015140241c000b00c0103c10807040e10f42040488a455203410101078001c02d45880d2090369030401540a9006003a00c2c000034140e0b0100140900e02c101d07000407416445442950398051040e5100c40071030442e4070042d4010b00d90401080762051541c0b007000504805400281502c03091009940c1d00c86c040d007080c1200d44003094a0422842090049100b070300000e000040c0b00e44c0451a0102a007030140d8070700c3d0114401d0076034540120b00094400c000d60554100c038001c18200e2420300104100d808080900121440310004030040b40c440e0f0340e4001d03c100103511440000407511000009100302c00018101c0e60015805e04c8005520 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 180024865 1250 180023615 180023633
    0x30733090302010903140702032806090c080d0207060806130b09070207090b06070f0602070507080a03050c070f05010c11010e04091a090f0604110a05060301030303020a020d1e0318 79
    0x401e01c2070700000b6000055180113410504140012034840314140001d00140e24040307003143e0f07030451400c51903214640074241a031100b2600b980c06030040385060406810410b99600324030070303101404100da4030380034840f004aa4554860140700001100c1c180410b6440c2400d1b80e07403200440189034049200000e04c004218082011107901005030f201072020000d0140c140308808501740140d030141c0c90312456485e8803451442c03001005200315800101102030010a0000c070b005040b0b16030903645030004d18100249141c10101421030603000d211070000783d880080f45444210303101a11b0382c1c103407031000780c40705c54503130300f40142050510284001c0d40c0126502c91040018007440b4038140d5442c5400b040043c000c520b0002c016075410b0b4000d074000c000003a0001405503200d9801640c0c041d802c1841c5001c01c0380c52440d54090368116030040004400c02d600364001d051140107980c203c1c0d0001c01042d50417200c131030801c2c2a0160030440d03512150030b100d10a03040500900340701c1d050b20075075038003d98035180700e = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 180026115 1250 180024865 180024881
    0x91401020a022706011103040b070c03081207020d0201152d08010e011404170c0307081809060a0623040b04030809180408040e06030a02100305090c0102030733 70
    0x1a10b242c8001c50643c000c02551800d410100030300c3d00345203c1131444c070400c3d90703441540112007074588040742001c1002510032105000d1680301e10400e4440c08122802030210348107441d080f0150040541c001c51f400c0c814458846000444004031151038500150301900000441c0409200390300b0001d1800b116489844c174000a106190002034a5400409401d08480030b98081c08442020401840003042924035050b0384242c0a041c82ca50315000f14442038954410711200424140c4085508140a40b0f401c44284030b039001a0b034040a250340e86000c105060241d40580300100745143c0300d2907006503d8044214140300070892941c40c0980380c1041140c0fa411030781c8226070180c00090882d0890030940b0201d01020903401480c45142403d54a01c4a180640d000700407020300918002006a40c04101c401880c41d0007400c0c4500401c80940003c000e4a0100c1ea0b002d01c07482009010307591948000112400342e038210502c0c070280280c074440302e615201050070301201c00b010400e0304a03000f04248104d140d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 180027365 1250 180026115 180026149
    0xe0a0308010f0605030c0a0f09030f0b06150a020d080604090f0f03090602030408060601030c171f0f050117180303090a0c350102040909240b01091401020a02 69
    0x128540c90b281d50691480c00e5500701000304801402032265518920041d5070080da4141802841c00b60708000455801c22141e00103010300c2c0c05494139034244040041c1d103500964046d1522201da481548041245103d2008c1c40e1006a205441c001b100e40c3c46051150f4016800a0000c103d00d0003940b5030850740c0b0707603139142564240c0c1d0380d03500d031003c0603084860344004251900246050618007104140c84d180c008100505150b114101c9038002841800c8000d91a0001c80e241656401c0000e00140601800c141860641080500204d00c8000d00e0039114104d0b003050f91800001e89201020f81d141e110084c0140c03100c890f150751a0310140000303001452044514030001c24901046050000c40400d2550184103103404c40b100300f90b0320104000030500701c203150400346a242580652818024826503200018a41c0b030b19400500b0807440d441049102900180b84135000503a1078041000c441e4064a0603021402c0304204100300c8130251400c5501a0050066400007040c0c0d4002c18141040c1244d030034 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 180028615 1250 180027365 180027377
    0xc0512010605041526010f0c0c050706050405060a261f0504060311040203040507260c0f010903021003020c030d0c02060915012310052109060103060209040e0a03 71
    0x40079504142c4076240c1c412013030201c928407207407600304c2e486100c00302142c200180b01c0f0708810101220320250084604500e120108200082c04488001d0100002d404104e950380140c0d500014850700c11000e03102a6900180000e191640011003541c40400400200e844062001400c21000c00e007100310520403060680b42090980c2c0ca0b450310b121640b455001184200e1400a0500100d003030202c01e1103001d0300c15180181e0f2601c0da410301502d400d059510103004004513060141021010616408484079060704540724280e25204100e1340d010780e1105140094940d42042001d0f20b00062100d1450800e030400520b0441c50a0340981941d0014403154205904c0315028240250f04020b01d90740046000098020500c1040e4a10034000b810301c909500481910450110285084d44a07120a40020700d201310326a050080034209800c42040264000c643e03000e4045283d0f1b003ca5010b1040c551000074003010703030859a501c070080d00580301c09030b00640d940010030210742c0304100400740d80d13000391194 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 180029865 1250 180028615 180028619
    0x206030a0605090a18060b0d120f0f14030c0a05130906151b020f01021603050601030c0f0f030303021e0c0703020420030a050912070804080606060f030708040c05120106 74
    0x4009400d4000c0c1031000054505840c000005e035212010a603019404500070801c4649800052100c5048a1002e880a192040411001500040f08203114035054031143d22132164048103441d0800410405901c11000b000081d6589881c0c02c010150740455040076400d140140c2d881d58400c0b002038200340e10141d618042407141c2c00c00000f0013050b0401500e030000d02c03100c555102c024028244d9800038042c164008031050503a00a02c210513480341c0103024170103026079a003070055031880c080c4825100c01c004214049150000b220380d0303100b40d030b62070402490030500d1950124002e601c002040c840403031181c030000310250640da00414031111200c004100c03e07420340c0100803c0f6681d1200c0d150780d4034200780c01c5480c060b041304160396112202020000b41c5580e12188507040c64900d4002403900c3d20001030756010017510070090300640c3d11600440301c803582c3c0c20701030103442c3c0f284417503000c02c1c40d50900000e010301e03105560050b0301c184035103244015a542e0f000451182c040382c0480d045981d444a100b = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 180031115 1250 180029865 180029869
    0x601060507170f090d06020c10050429011203020102280801060503011a090d050a2f0d080c010608010c03020c0c18010513091a040b09210a03090206030a0605 69
    0x4002c68415a5000d254905880054542524403421800340d0180958018510510400342c1c103440307013242d20300d050fa90700c00862056000244421201210249011070440b1151401e409a8044564402000301c041d40d0a00680d40c040309440d07a0110110364003041010200040d0030104e242c01c009070945071004410800300a040d048050304490100f010a10040004c40518030000c14881902040155100b10450104039580030108020b00144600b1060703c041106c80d0001d10102403048400b0304540455800240c180241410040e5008031000d0500340401c46440091142c403c0c4480005042030380c0f001050300b9a240703002c0c054040f80c2c1c0800c80d4071500c00184001425403904a13a44080032000c1c500c2c4840c01501800b40a000d00850400800325160550004e01c0c140d801c450a8004003032426680d40c40040c0444085a07500110004039081c00c42c00108201c46499940300788402e20159580440f480c2c100fa4080d01c00c254480c0c1084c80940c8400c0002c40c00b60214001c0810702c9814101 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 180032365 1250 180031115 180031133
    0x90108060613033305100501050a0203041d0f07020105010302030a2d05030301082509020a090306110712030509100b010203130902030108190b130303020f0a0801051513050d0c03050601060507 84
    0x8484e001e09080c1020001820402103103002943c00909000c1d0712180140b404916501a40d040145078480a186140c80d402000103428070031006407850314050380d11010201d003a85e4080c44000d415600c40f040e15000103401c8000740c4083c4205141c80010191b142000b40700e01c1600c244184c0d4544c0000005114a803814025003a004000b036004028981d803041382004d200c1413a10584007425404109a001244210341c21801903800540601c01a4580e01c284901036001410072544c1c00d501004403282c80d80280541d82c4501c4c41000a40060010159900c0c05001c0c0c00010305d0441c0020803c6a400c81100800d01c0007400c800c2a00607200d60520054528100e0807030640c045845030340d0300071400140c2d80100150310079400b40b4010f0503000f5515003640a40200040510721580106249005035800300001d41214011180c05801c7d59507624502c289105844001940017000c80040c01a418480c55100c0e01c2e52081800c40102681c9488081c18100c0c280c1111000440006e402010b0142c000303 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 180033615 1250 180032365 180032453
    0x22a03120a0912031d0a080904050c19050415030c17040303110705011a01020f070b0901052107080c210c0f0a020d090e0712090201020a080d09060e0309010806061303 73
    0x24014840c51b1026103507050a40500c3d11040d00c01c0743c940f0700003181400d440c0c0c195201c0101c2c043d1011034001c80000041e11b01d4105000e20fa10000581e00c4c110f48107031103401a00820b40c0103440345901032652114100f0684030081056040c1900c80844a0032158030000909085000d0b0000103420343ca510480e4080c01074000940e411507101c0501003011041c0031901c103088541c1c0d51086940c0d1560080160381601801d20100045900c1c01d0b0500082900a80403d10954980d9101848c81c2d550710700b0300b150b130b028040080203883c5481d10454940c01d83d02a00135049890800200d05000c03216400400b04d82c0200c8500d00142c20500d20b0022550704044204068091300c81c840034a4130f003295005010100181e201e240c800e40310340328401564001d10440c03804a07040018213070351f510b0780040c10002e0b06580204941c4281341080441c048040801075400c840c205a503200140d8586400b0000c650308110505000c0c43d190000c00030000381c0d200d42e5480018000120014520007000d6400c0002d1461 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 180034865 1250 180033615 180033671
    0x170c131e05091b030f0403030e071d070c110f0a0e011e0b070816150903051e04030b0a1d010603060603140105040f03050a050408060a022a03120a091203 67
    0x40d60011210381c560103483d030184500305403c1da5584c447c24104d01030030b503e81c1902c0c114010600041031404501c00082c1018405040e4a800b0340c5550108a620071840078001d0005404286480e849280c017042071000300d1070060508141644803038614141000030323400300c5e040c1c881c2d0b0320217003c41c24200c2d4001001400c08102d0142045032382d40301c0c0041407082c41e418090084003800c62030104400b810341c071084540f400c501001303840050f140c094129480f003125403c0340840d0103040345c0d000d4142c1c03040728150780d40180c000310b547d240d8244c804041c04851500003a505507410385205030540c00d200e150000d41c00b0703a40200e1013500e103090154001002103695031499041200300700200f080c0c0382440036015032600d442a513484a41c03004403414000d0390441c0046009803014003139982002e401034002106640d801c0090451140f50080410181004880c1107400501c040c110040d000b100c4d01d540850280000720b800301680d6107a02c40321004c6c00d14000400d554594000040c02d040a0000380c20750700b = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 180035971 1106 180034865 180034891
    0xa0f0e010506010905030a05250518010510080606030f06060d0608010e1903020717010219052d070b10050406080604050d170c131e0509 60
    0x1d0ba140760000b041c0c8280800c1a142c040f41d074481c241e0307014008100ca5411440e40b452440c11020301071039000943c030780014942d1611050983c2c0d0640b080003000d0151b041c1810000410740c0320340d60a0800000000700461512003c00710dd802c8142d490503540075544203c005810340c41858402038446042100c009245101504076225070780c0ca00080c2c44200c0800600d2221b441c0b05154040d0069002100c00c0117140e01c1168626044c07450340e80090314207803070b612405420030204000c000004100003045903400682c9000001d0740ca00301d036100102c0586507d0450214040c0b40005000c80740c96001003209504d42403c041c000b403001400034021a581c0348080c0307403229011a0182c8081c0100c443c19860030307220b0803090b038a503611000314030f0b00c41c2c58800328024103401009071740d441e0407103203d0040b40308504940341c180c9128149129001040c104428440c0d5410050500c00720303211 = true := by decide +kernel

theorem cover : BRFrame.Cov 179856115 180035971 := by
  have h0 := BRFrame.cov_init 179856115
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179856115 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179856115 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179856115 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179856115 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179856115 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179856115 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179856115 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179856115 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179856115 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179856115 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179856115 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179856115 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179856115 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179856115 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179856115 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179856115 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179856115 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179856115 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179856115 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179856115 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179856115 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179856115 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179856115 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179856115 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179856115 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179856115 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179856115 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179856115 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179856115 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179856115 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179856115 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179856115 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179856115 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179856115 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179856115 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179856115 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179856115 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179856115 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179856115 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179856115 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179856115 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179856115 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179856115 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179856115 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179856115 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179856115 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179856115 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179856115 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179856115 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179856115 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179856115 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179856115 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179856115 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179856115 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179856115 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179856115 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179856115 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179856115 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179856115 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179856115 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179856115 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179856115 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179856115 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179856115 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179856115 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179856115 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179856115 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179856115 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179856115 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179856115 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179856115 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179856115 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179856115 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179856115 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179856115 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179856115 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179856115 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179856115 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179856115 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179856115 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179856115 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179856115 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179856115 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179856115 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179856115 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179856115 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179856115 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179856115 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179856115 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179856115 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179856115 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179856115 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179856115 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179856115 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179856115 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179856115 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179856115 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179856115 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179856115 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179856115 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179856115 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179856115 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179856115 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179856115 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179856115 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179856115 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179856115 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179856115 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179856115 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179856115 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179856115 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179856115 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179856115 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179856115 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179856115 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179856115 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179856115 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179856115 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179856115 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179856115 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179856115 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179856115 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179856115 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179856115 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179856115 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179856115 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179856115 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179856115 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179856115 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179856115 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179856115 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179856115 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179856115 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179856115 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179856115 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179856115 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179856115 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179856115 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179856115 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179856115 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179856115 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179856115 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179856115 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179856115 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 179856115 ≤ n) (h2 : n < 180035971) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
