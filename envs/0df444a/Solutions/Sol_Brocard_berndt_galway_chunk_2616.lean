-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2616
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:14:43.287258+00:00
-- url     : https://prove2.me/submissions/57f482fa-9188-464c-aa31-e86f1974b968

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 470323741 ≤ n < 470503597 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 470324991 1250 470323741 470323813
    0x409061b0f051201061b290a090b070e0607291f09020304030c140d0914150703180e07020d110a11010203190309020a1703160204060e0108 61
    0x89544680064140188406c0c000305142560300c40d0b805040c00304c0c5e190380c80f40500e1103000412024803100354588a203814001ca0300380006011072100e0185a082d503078800d03030b045440d0311502015646080c00800603038025800703002d001c0201d075071242c41c0c049100d0141c00f21340d00301c41d281c640c06084801c010400812005d40c00c1a58042d000e4070080307101220011a00140c07a920340d45000c50382103011040182030b400041d41c9407520030002003103012481a5a0700c4000680741e961f0400490a1010302e843d5a12038050171190084036814001850564420315014110704250320240c060780d161504049007090400307042104440e010021f0104a1903141802c03001404102081c541e1100315440c000e01c8003800c4c1d4420802d5074001c0041d1485481c10001e01001900c1c440e500034000c000d416000c2e481346003004400180c800c07440f00b11000303642c5a9806180b4050741c68900da0001d206141080341c100e580c608000501000f21001d0314003034108280500329448603002d00003144035444544a180c89510 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 470326241 1250 470324991 470325007
    0x2709010e0420060403021002010f0f0c0203070209040816030f03050c03010f1503060e090c1f091e180b100306061b051e0a140c0d110409061b0f05 64
    0x10b002c199030380c8042414035044000414021465034012070740000e411603240c2c200e040300765070190030007185204645070070050300300700c090001c1c155551210303cad01c0540c104021100150814581700c650140c05100000e01d801d030000100021052000403d8002900d0102204403699050051a81202c0f0ba9080c00d42994108400c080028040380324804141038040f40d0064103e000360004c400405030f00312200da06240c03920856440c0c421032051244101d0354001510125a4040000c030602c3e510f41d65040d0410382000181c0c0d806903010118042e11100c1307004c00090040f103822460408004e070101c0856502520342c1070149840903800031f4800d1600f084410704c8200d40c8800c02c6051840c00711794008030f002d1a424510309100e40c90b11610a1041ea8280c0004001c4001071710703504042c4100703911440c1c07100e05035040c0e41350207018010b11360020481c04807401158040c01c0c00385513090300900020b6903540507602c0c4400c8529598507400a8041840e40030817190300100000c40320f2a613130801901e0301d006 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 470327491 1250 470326241 470326253
    0x510020301030c12084f050102030414101209061505040902010f05030a200318070807051e0915090901090807260d021806042601022709010e04 63
    0x3039046d807812450168008540029007651403040d50302c075504000c1e0304c202e1020703482c010402030040d000d42801d900c214005210351000049078121100b00d8112030915410780c0400c4024001c55000340d04010a140071110296410304c65900b146208030400602200400c001d170703100e0681540010700c5145000a1500541d81010006440803031500c1c00356501d82d1583c071410014010340c2101c006170075040d003484803104001c600075805425048500c0c00440100c00e000d69a91030503004a00c42c41e04221010480b5050801340440002d00c181031001801020300007040d0f0b000c10403201c0000c0c0f40c03104410385081c0d041400c0c0c2c0a410281200003800187e001d501c410031180f01e0804c000340304921004860f070040f01e1160b9230181c40701c1c41c0d06201d940c424121026001a40019041e48101c2e1b46128018400c2e20f4400d0494044501031241d480079860565140891070041100020381035408002c42c025123001200d9560005240300c4401141031074480602400580581083c2c0301003a00300140300c00700720 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 470328741 1250 470327491 470327497
    0x1e0f0d0b041104020f161e030219061b0347030307020d080c06060102061306050709080106090e060a0213031205040b07030903020306090c0a090b0109030510020301030c1208 76
    0x40c000c0b00000315801c40101040003445411029039449002081a4195900300340a803401140030f803e40c0590f9194603509040c144078039000c000c5c050303030107088203030700f100c07446101400d840c3d01603400003030311129207200b40c4d036052003441050000950318407a8203d000030154000400c41841800d0070312403000c1c40c0d04040814810342c41c4032441030702c11406000c01e81d8104203d0301010307805410080e1b507184600c0c0001c0d542d00f140c010601540985800510f0ba544000f5906114000c01d00c100954013183e03403190001440080d0000d010030807501c0c1d0102e1386040034003a540080c0b1681000242104000d95400d040c1000074200039096070040001d00404004180c800c0180c170307000314907000301160300314043d682440381754042d180003a00440c0d44800d05801c00c2c44d1b98100c82c0240c090340d42c036a560810a5442d440c441a030580d1202d044202400300118643c4000302210b01810b2035440c01d81c40f81c903a640382c0044107940121880d0000b0050042100307500d00c24000f000f2298000d4401025540c0e1002280 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 470329991 1250 470328741 470328743
    0x10e092d03070602040303321c020c01110c0714031b1903030801090f02030405150a1d0328050d0f06050414070906050c031b07051e0f0d0b04 62
    0x20240c0c80404038010810700c101d800c081c0c2c0c0488110355459a078a0003420101400742683d01100000c1e40e03091085250f036240c2d0403404400c0e19618500024404034a01005002c4440c2c46d1340c0b0381c00e12024250b65800d22030141503013103070300040c0e403540c403c1c200782440c020454110141c103201c1e0a1032000c1540700018000314140104038042880203070100441c800c10f242140b0801d07000eaa1590000c24150003120792810794805607010f0101c29020703d0b50405a00c015503005089a00003035098802c1201c110000b500702113201008119108202c00b2440420000c0080340b5440d040003030f401d04103c50380b18103014030845001480e032003400501ea001d42140140024880080d44601718071903517495642c041c1024200080c030400051803482040041400f048032240003248030200040b91883c02082a14180000e03503008615080b071044103105140000d01c1300300380320710440703401107903a0f81e411415486402c806441e6000300c06080b010405006801203049000d1100c0700487e8010540300000b1690003 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 470331241 1250 470329991 470330053
    0x9050c0603060105130e1b21150a0e15030c0d030c1b03050c090108031c0b1f0c1a13060203071112040504050c040e010524030708010e09 60
    0x42d64a15005030340d04e20608004140890346201c011454448215259004204c6024041e8a4a001d0441110070303201c0c00280004800d1294054100d18408c0340300141d1000c683c000c0b2103a0102c1e25004640ca000c0c0303640010322080e50280c00c1040f0f005414a040d050070100310b006045103a6200b020501550401c2c10140c20400300041c500c0074003030140410f03c416144814034a0f0059500e04010340c580001a0941c0d10443c400e02c0001010a030003c1602d800700c3c2d5240004420500b00c0f620340c0024580220243c0c2c201c81d038000507036452000d50712100540ca4007a1034200102901e85030200c402c80003507100b11724907c071400a100340da01e0201707030680a0340e80c45200140e40362107000c001d4504d00845030f1003049520480303503002c1043e0103442c0508101e810035076083c062a19810059025401a40100c102d603070303032100c01040b040c07904403c503c00070305031492107050328466500e50300034980c4100c0e01540400c100400421000105910701d035030140250000d00401072840c0d424502500c1154840c10320 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 470332491 1250 470331241 470331247
    0x80405060307030207021509010f0206090c0d03020c090c03040210080106050d022803020d0e0f1b060d020315100507020a0306200309070503010e07061e0309020909010501150309050c06 81
    0x201800f80d811101da854005080325010ba420150611940d8000d0081c18000b4001100203228140002150f601460842000e041220700c800c0500107000488041541188284400300103103444000180740a1b1054002e13141d82e0b40703014010b01c800040091a48000c0141103001088000d911105513609460181405aa11820001d0015041c00c00d1048c080702050f95148100328260144d001307003408080400701388140170707400442980703481542600302c286801c403402c190160983c1c1c004036803e015000301260308280e01004600f0413170300200c440110314684181001801c1c6000d80724401c06040a281c03d62400005a0218111118502c0010116178031000c0b2040b0305400000034508600642c00082d40b40d151a443ba203030364901c18401c4c3c0313000394038080c132100400c1008a051000c1e0389050310303148501c41ca2040c644582900d945e8101c4209640c4031305210069a694400902480c411000800c0d203506240382c10703040e00407070070450090500d4021080d001801c046280c1031040c0c82181c240b07803 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 470333741 1250 470332491 470332501
    0x60124080103260325090f0e280c12090213051503010c0302040f060f200a06060902030a1d0c0f150a020a0b010f060e061303060e0c0f03010501030804050603 69
    0x84284840300c00340000d00000301c2006032030000c551a02c17203095603a12840d010900b01010a070340841142c0201c01080d041d01500380181d480751400150041c241088001140345a025550040408140320140130340e1a00d02c0d0301000e590080000c04280c034000000c0006d0029980021003d07146a102440003a8a940000e00d032164480f40391450000d0280090000c041a900020000e41c005d001d11044070114003000301d90700388281d00040240c451926115984000600007481c1641441c90b1503900c1c1c8900009040010035074010140104400080584c880c00c0041242c005d41d1051400c407402c401a0390f8666100f00310000b81c0b04680d2074203036010007884070520042044194100700c1d02c45040740010742c0035005680001d10002d9140500450002d59032030f203502031080031651041c0c000281304040e10031002d02d890740c01001d40c0383c00c00004010056a030343e240000d81c2d01021401000d5081803180380b446041805100e12a060110020485507045070398106083c003d41c05610300852010000803 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 470334991 1250 470333741 470333783
    0x516020d080c0a0c05280507150215090c0a0b04082a01030c050d05010b0a080f0702061b120c180d0b13030c050318130e0c091314060124080103 63
    0x21a50030022052115070300070206040f80c0040d046c20f02103038544a9188005150404024030403000d154960290803030390b9114041048814018105800d280103e00c60701c03100765540d01d4100018032070340350030f01c0c1c49070701c0c18103c2820088801e42054210102070350b40d5200071584020820f6200b0b0900b000100fa0103201000c81c0e0034011768010400080c5804004540c1082a001030700202c000c3d9990304200d03070b64422a119480340b040d6881c40159000102041c2001c0c41055014814411043c40c141419907201c9424011031080c0c681104082c00007500f16440740b81c2142d0340001840c1542c00503820343d410742c2c0c0c054028400418041101000900c0c040030144900a02071020f230308041204d858030101180544522114125144a4070b4070420064401001d8054042d0812121000e005240310354014000035480040a0218890b210780d000400112aa5000d14150003182e00034855503040401d000140325a007d6001c03a1055144035400585130b01c24201030640b0b5114803406840d641005841c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 470336241 1250 470334991 470335003
    0x20d081b060c0405030d020304061209030c120f080c1c1a0613050109050d080a031a030d020105040b0f28020d02070f06060b1c090507090516020d080c0a0c05 69
    0xc030100e000301402d01c80034150a0740a0300540d0b60072429181c842d1000c1c00107a03603d00c1241b20306030120303498664030b07503c0c80c8203a886071010b18080e00b0550f0b10800f1507510340081680d249616004983d0000c120b5050540c0010050380c0714058420180c07400d6100078050050920000203544d82c29115040c3c00341c1e028503055040c521910140420b5110f8003908a03100c01c000960103105c0c0007501442e40000d161509d4141d007400b00d60440c05140c900f4544500031800b6000c0c01400b940401c00c6000380c0f04682e01d00b00301d55910b05941341d000040506082ca4090040e071400340000003440d81d0300c424001c100d48820580a04070440c40959005003d510220300080d000d0f45004401d00c44c0701080030014442e4041029003481e10072a01081825219052010b450003407a011200c90703441400308007282c240300d5226628850040040362009580c0301d580c5ca0039200b0456011010020743d5050b1501c0d40d8041004103201c0b030003400d20900b80d2900c0d180d42001c40c0110513200003001a202030704010b000c3d0074401 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 470337491 1250 470336241 470336287
    0xc0b090a0f1202010f0b0a030308090a080301120c08030903070e1008060106030b3a0606080109050a050d030b010c0b0c21060a1406041202130204030605060f030109020d08 75
    0x118407180e450800003158031080642e0800365080c0340d240b503040d4405101d8000c2403480102040c1a50f400c40d101100d4654004286c00c01520513032429070042594540071358000d200d6201100a503038020314114114070200d601401c0d0951040c450021259030215034a0262401520000c1182e514602c4d000300e05150f0b54401d881902403000042410759240c1c00c4100038034030035210700055010350300c404800c0e440c0a8006244207560340f035a004a03c41d0054843d485d66002d1580840c6103500d412481e0f085501020b2304030f580340e01840020040000c1409660003904081c1410003441c144840064655405500010045a12080011615040b000c180e4541e218000201400c201e240080802c8102e01621164416184100005980e0020382c0c0201c2072000701920a500b03061400c2101200000d60500032680000031000e000429913062026000a5000d40e00100d010b04021080c840315110190045002e80d0610081c80701580b200542c030000a944500c0c4c0960b82c9125041d407138880002049 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 470338741 1250 470337491 470337503
    0x40306020f07030801150c110301110c07030b01060810060309061404030309020f04200a1106070905040b090915070e21060903040e1305190803090c060a0c0b090a 71
    0x50400e4403103070200c01900d4194829243e04a090f41c17103054000b0a102d1703210f034410008601b0f12494001440b000380313803140d91074050000302da9204044e10b900e109801180c1d045910f50b10000041061041055409006007494105603510b814180400d1200200354068002032588490b04042001150f502000c0614113004d0301e1b05c094201440c0040140c03903180ca082e48a2041c0500e0b0144514161040b206003d10702e07090441c21411061a50001c0d4015000320020310071286103704d124001072080502c1048581d4072101c50508003005c1104882010181034092210b110800c0f401c484000b443c07203c12400c1582030505a920711500301c40f8144580400c9810100d24000c0101010a1010090001d82140700740e4a403030b0703107a0009560784c0c001c40c803070807a8508501d004a040310458100f4060240d010b00d01744c030240401c00807040c2540c030321044111181c034400401c10400200900000f080c9280448489103032220001d401040c1114401c1d01a00b80c0c082080481c110340000c101c4070032082d80c40720b = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 470339991 1250 470338741 470338747
    0x9150e04090f020306060f0a0515090603090607350a0e1b150a0c030c030309061e0b040b0f041d1203090f070302060a0f030209030610180212011a04030602 68
    0x31420b40c44040c00064128040c1c820b0401195030740c43c1034040c2c42c248040140c822450b46240600700802c0700d54000034500355034010440201c00349c4900e401140708010b031200038801c508122400610910104144981e1400d4070f20320071407802d40d8060200011ba14103030780301700c0719140c24040500805841003200102d21a0345040d110190040150514800302250081e080d030342c03031070340203a0203201d02241d03880040c0701900040d0010740190801226a406031600181080c4141c1d6100100d540403004281e24586c4c200c5a5940c3c2d4a0034015410303280025101031104601c07501c00b040408a88804c1e0b2072203035445a03809180601032110000b541c91044044589000320020707990360a52040e10b05514a015100360031180c11400589441142c2d0301508403031420104035000c640c8814040340700b5082507000c01c042c03031182d5020400540911032100880307001ca0301d05400c7c80c1c0901c10344201c090940340180030651100700604581c17411140a155400407180e5500c51150b03443c402c03600300824003031003c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 470341241 1250 470339991 470339993
    0x1419030308010f0b0c1009050f01051015050a080c1806030f0a150e1609031406010e01090e03040312050c07031103010b090421030e07031401140709150e0409 69
    0x1181c0981260184881c22010303d40b61840e141d6240704600103ca82540800e408161503605903104044c001d01641c1070358180f0042d80e01342c034256142660a912038404124041c410310621201031117204202d401c1c0245440d100c1e610240007084001c00925030103102142c2850200156410388802400003030160380c0e81c0c682a00440199035048d29040c06039480d000c01c42c089519a0011030056905640004a896a0b440e03885829040300f880720108100f10071100000007080c256190001034102d201a00789907050022803080f06405910449403141415400d00c4541004000c44003a00d030402200158001d490a068501d4490082603045034800c268000052000c2d03403140b007a4500c4110024000c44400d102007001400d016200035190040c41e61081c001c2a6102d42400403071039141c1800724a120004040c40d08000322036005851030944800c240048440c00c0c03040014800e0510750000250402c524001c06981c0a401103420410061420720149030003401c0e8607109000c0144148400303001 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 470342491 1250 470341241 470341247
    0x10c03030504172205030a02180709030b010602010c020c010306050a0e060324090c0d030f1803060f0b0a050307120b040305120103150e370602030f0403140f0414190303 74
    0x44d1416007600340e00340306400301786490013042039011070341c00a1840c041c2c40c44414911040380b0020348000c003403081a400c000006400c1d045d40034000c101c0c80e0000560b00d640c100e0064103100041c1c0c246410545041018402ca550380e0522000362046840011440d81d12040440c1c5414a9400126401580c2c4014120495814606c0b13501c1107590724182c441045002061004824081000902244a000c0e4070821944546d0080d85c100307580000300d0148690700d4a88000700c0700c0c2490300d904600e0300c030003444541d4149022500014203044d001051000e00d003100c03081c22040003080041c900d184030710100303080c907204000381c1d1011207107281960900c0d41d5070b00d040c800d15228405640415070174020020f01c00300c004211040c0c80c1200500c0028050312100665110a410010503400000c8461440000c14004e1014622a007a24061843d45003400e0a001d080300c5140c4002021804040007805150f540403000e48046035481e0303c4022401c42a0000102501c1140440da081c1c902100c2002091640c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 470343741 1250 470342491 470342527
    0xd09060b030105090606100203070c0b09131b180509010b0702211029120304031e02090f010b091903080304060c23070230030408010506040209010c0303050417 70
    0x4800c6600d50604400c2d82c1059807640298400135289a08a41c020400c41000400501700808010681d201200f0360b0ee03800c50481d000e030003001c90b20041460f10001115001001860f03045803640d448040ba038076041c002464403c050207440c0040d000070511008544501c20184410810381800c0e003504020f600e0100d03510b408400000590300e05028801520b14821200142c0c46041075040800f031310003030700038070004280d0a804c8100c0fa2208010010126907032001070b2455001101403642d82030b00e6070041190705603020304600c400100e404010000c01d405d60045560340002611080c0030034080c0066050180b80992018010b04800010082006015403010580749070b00d0320b520003050f860314007012403004140803100c00140100104405860300601c041c404070a030391a80c103003649040119680b844d20703440f0008100d902c0820300340b0086d4020302400d41e20a41c03d071021811f114020300000c1c40c3c41980071001d07081c50b5442c2c0120f0140f00003070810325121130318002c1e11940d540042000300c0c4460 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 470344991 1250 470343741 470343751
    0x204110705010e0c10081612020d0203090106150518060717072303120a0605100909060902090a1e03051903080105030d1403130c03150b040509030d09060b0301050906 73
    0x1004e010b03281c811a01d454402104d16100d903036102c02c0b56644018000303c0d030700c0000d00303039005020754008040d45207201c500041c40b03c0306000340c1c0581c072400d14500c254203460154001c40c0c9c4918148154032800b503401070a6403c0c1c2d101341400e20701100c82d000d000c105140f10702c0c0005810f103420202031403000c110b00b000404100d441051000c05401c0590403001c0407410380b00e003650050b0400c00050410b2010000174035000300307080c0000203145590700f00058004015980c3c1c0000305a44820401c2200000d1040c42c0082c200c61340c00307501e45120394000803681c2c0c501b4003400e1046541c00c0d40070000c01c0c9000c1c1034800515801021034580d1420346100302c00e82e02c40c50004800040a100003c5802d08001c00c100e6103560f0340c0d1305c540c10390081d07258441005400c01068003107100c1c0d540c040c0da40490b2048022400450040c0c4a554044a051041e00243c2c0c6000c01c40780d00443c240014045403a01c00801c54480040048002403a0f2000e4a4482c01519010318055072540c240020701610400c0840c11500507 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 470346241 1250 470344991 470344993
    0x130603061e0b0418060e10050a0e22031727010e1506190e0103060b010e0a06050c070906030c05011106040c090504030905130c02010b0102150a02070204110705010e 72
    0x307444401e6091124440c035004080c114941400104204032403083d8100700f00aa080010804a440d80303160281140112214880f400389003a0411181c201a030a90b0081d00d00020300c0d0781c0e6440c0109810700d66104000d40c50700a940d11580080c14503224900e2243d0001c000d02c0085c1c140d041070f0b1495500300c54401c03849141581000240c2c40025014454400c0c03946419000c0d000000307011140080c1120010141c6400c4264017000c510304918030801c6070060b01c18003404c00798650640c00c040c4100c40107411003078140145100d50341926030314800c80a007140e80500d0910358886402c10030f6400c3c1059544a506503604105020003007101301c0b00104181e5100780d0f2104181e03599002d440c1e50b45c80060341c015150000d221800e10510b0000c4d046140e020340030741041212036030b9602c003144c2407000c10082100d0b001e83d2080400f01c07560342030145480d0702d8024801414000c21a507003c1c45441c0c0c001c0c03c21400303e0703800601ca4086460301d400644071003032101c1c1c419403a07000a0a0480c040c2601800500b52 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 470347491 1250 470346241 470346269
    0x506150a090e19061815180b18101d010f05131203022802070b03191a030a0c0614030c0d0f0e07080a0b01090908030601050f13060306 59
    0x1055510700c1040360000041d002420740b88801e000121540f0b407108020b0704d0349510380d14003040844203103201a15251090a248500b0140d50004000300c409440b10984011001581000800d0302508807541050714440c03d070302c0401615001525052007800701c0301420341821140c500e18641001ca00303080d0810b840007071100904203601c9400f01c5504844038544006503644203000320303810108044500f41d03070b820010719219409100750f6a01072038020036400070500d40544610a5410700c0424010004882c20794214140540c0c20f0031031000860302209401d542e400720300e41c41c14452a4200700d4440103001c1e95a103020318200103407510710701e00032140400c0c85030301440200c0f004041160700c100b00107181127040100190f00000a0000a02100c0440d81c0b55054005500d03000c0c0b10b0500106500d0008260070121440c11030131a80341640550181c601c0c0c0b0806c0d00210740d401c0e04072a4414002d06e400b40c0c0d51851002e1f0900c2c00d0142c0c0c500502d0782640c1c01d40c0805c6403030309584000180c5e80c0c22904016 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 470348741 1250 470347491 470347499
    0x2060c0c122109151c05010b030105040e06072019061d0706090603020a051228051303030b1311030f0a090201020c3604030e090714030604090506150a 66
    0x241e02e104200c0c01070340003020340607014004c03500764000e04107807103100d841054001042c00f403460640e4000e03080311500c1400000104043e2502d031181c4a0780d800d0341c1780640301e82c1c508210042c1c200641c5045007110540400c035a100000820301441c204815142d480c0940707003500d800c05000034180003d1496500700400b03040b26220200141e000200c41440d9910992142009012406034001d0110901400024041c4020040400000c140729908983d010100d1200c80c0c400f480c245484032500d100c5461811003031092201070003480c9000f03d9010704010030441002004544a450b6849080b81080d1030140c010030f4411a07034005501400c00f00328065407903111010448225081d00d10b0080c00b50340080407468480c203005c6050341e0400360041c1c64029007003102c00c500885512411b00b1030344098502c000c0000301600b00c41d00f000280c0c1705950490f554a0a42e030003601c01d605140010300c800c40048001211607581d5041801d50030f41c4001600c049060061000d0541e050b4183d103e8400e00300900085 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 470349991 1250 470348741 470348803
    0x212090f10150e07020f160308031308040803120402041508030a1107050a120203120910030216210f050c07050f0301060906060c1104020901090302060c0c12 69
    0x611030600040240201d8001d6007900c000a242405000c25080441e50703001410305080302d0060b01c00d032840d40140010b04d4030805903d00b403041040c8003003100442583c050010402c0c201c15a540862003c2a4a0080c640c504203015207004a910000c16840001800c13281803030012005d40c0078500c00d60b010700000f00312442042d00e880e482e01a1003c0340c0d00a0211801d120f100c1c16840f24081c0294040e69900e60b04d07600891480101034110038400c0b00740e40f40b00c03011420204591101c0700d0a4014460a1507003500000d081461944040b108142e004182c030a4800940e0150550295000c00380403800c1e041d0400b4440d16502041c10b1324042810f400c10322442500800c122031510380c0c40030107401040e0914041091980324001e18540641d42c4031340c00718400615104010182c001c0d81c0b0307800c0c030300c42d124507014450551350700003039004038018000e580c0d4503600300c4045004c0c1c0b581240c3d940d480320890202c00349400c505818a41c0c1c0222803c0c5039882d1010046629214910803551500451034a034000c0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 470351241 1250 470349991 470350003
    0x20d06330e0f0103020d1b1d0d08093708150c0301270207060e070b04030804050918010501060818030309151305070602030a090509040f0b090f0102030a021209 70
    0x210781011002c0d48041807588258000c10034225040400184241160802d010f401034040c0c0c1540444c0c1a03904051205000204501003a00b00311850826a40c05545180181c02040314040c05041c02140044100311088070030301c3d1100409100105041c8004181007241442d88212481c0e801440520741110301c440b00c109104940300d1407103906d56460080c1b00e440c01070043c0d02802c00c100071840d116000c00000d000a210b828014000891079501c0d041440d800c0403030039801401841d0302080100001070780c2ca01178804841088461001d140c3d41c0800c0c404054a4000c4045425440c010010800c2500b0030f007154014412044018040038103a00059076034401500d10081c10340c04261942940c203480710b1704682c4030302c440f14101c41070405659207500d042840c0e001080940c0010540303071895580984a480207290882e410021410141c4480b03450b6201c12001415030808840042d525202c20442d6000d40700d0018000c40d40c0380380c500300300402500040310486940182c1d1001c01c40c0601d000480c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 470352491 1250 470351241 470351267
    0x30c0909110f06090d1104060501110d081503010219080a02040f0b07050c0a1719081b07080a05030306120607090b131502030903070602010c0f03020d0633 68
    0x1003030809008020024074200c0d2466a9a10080130040c0100d10344070000407180c21445400000741c070a001038200025101030f604500c2c101310b581c55005d02407202c00100e08650000b0303820020010789502d952100340794003000b4883e406600014040c0d140c507541c002d0b001041e003125524613007180c40d10758414042e44518420102d414540c03a00038005040348200a0070001d10400032a0050a42000811401d01040d440060501c0e80c5190081d000082480004807442000380030581040c82551201c801d40190540103841100031340c0101c09240c2c0030030010010304641e40466064040c0e83c0390080d0f40c2c1c0d00480b02a40241015140120a040c0000c0d82034021089901c0d02100c460a0070340400c3e80760811841050140880000000c645030464403420005030a503014564175900901454075080d4a0303070148003107a1501d200071480650211000c0548030542ca00542c0d10f032940400100030b044690852090181c00359902c09403165030700004c0010a104002c542c440b00d036101010f80b002031a01003 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 470353741 1250 470352491 470352503
    0xd110a020c0105030604020d060b040f0605030613180b090d031112011a0d0f0203070206091b0d03050c0303070c03180b030403030f090b42041e0c0504030c0909 70
    0x1da9008558041ca000d154010f4000d400142020440c1e02c1080c1600c80503401000d0203040017505101780e0343d0110034640589201d051051031824400041400c0284552196803503d42e29014005030600080081945030b400c15480922400c21100b51519104503c0d0000e012a1400c00c0391880c031400c0380156101610102c80060345a0f20b010807184004451110390440b004081041082c00c000501c640581010300c00801038803843c001c1006850280c01800902c0c2da6070040c0a4030302410080954050310301c2068500d92041d0090f031806880700d0213500c507007201a0002008015070203500002c04210f15000341e8071441da030b51403109590180b0320603000309000348104100040100c1d01940084511611981d030014060303400340c031174007443d94040c0e444443e6001080c545001c1088a401d02c05200c0c0004001844807103441e234078100c2008468001c550003144c60305550080f100c1c40c4401400d00b401450003c0c85000302c4030400403c0b50b0711901084510480311103000c680b1500921030726005691140f = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 470354991 1250 470353741 470353753
    0x1020a0f02070e0a1503060f0902090703090b04061109040612050d05070c05041107050f070f09020f0301051017130b0a06211119170a03021f060308030702030d110a02 73
    0x4140d0b40151589041505e51200414800400140d4510501901d04d03c41c0b8400694840e072841081401c05d8040c000204150400f4115804260040c01c89a0095404a00000d4100d580402c2210768003c108416078040e141840c00505e115030000043d000c1445141580c0c0c0e25403e07503209403928041c0c0c0c440030700446950320b42440903081c16800880c2070009040030318200311039681c800b850320411200c108000e0f00101402c102c031003250f18081000d40904201581000c24041060f25a400305100301c1e481200c50400740d00c511801140c001c0425011400460441e1400301002c4c90345058010040380c0300c0b509000000e0518903a8401c1c0c90507142d058910b600d80540480824449a0200d0820b03261120074110444266942001c02d0301300525480c0a820301030302d42050440f0598401032115507581003102c0c40c00020380d011078001c000a130300c10122600003010440d0000200140d80009141d42800814088440d0300080580700c0410660000d004500504010031958010084001d0140c0e0140d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 470356241 1250 470354991 470355001
    0x1a0a0804060c05040906060e10020c240d05040309030311060105090c0a030e06070e03010e0d0c20040204060302030604240504021809010902070311010c1706041d01020a0f02070e 78
    0x65008884070b210207103066410243c80308011412500076501c020b0104a01312050701d90f90810300b00e095065450b50014000c0070100d01c0108401c49c00d401c14003190940540d420800e442c561200340c40c103080003e13101b0070030791030700e803074041c20445082c0016004550802c3d04040481c100007200c0d0b0503240041d010189a4440c2c0d01c140d00c190b00280c0906c8103040c0c60b2041100444820800c5510a24031f076a25080d0701100201407500315241c581c5418030503000742e0000d201da60f412103040481c6562107404580c031841c0716819080070b102403120056100d030000a001401c03d5241e0099802410221b508120303060350a0642c07040c03a01e00598511200c00d001b10200302030b1078a540500744000103403071004000100803002800c00e5009070040c445081d03010074034005040e8403140310001400c1050081008000b1140064280c15010034040083d800042c0061840c1e10780f90005006d81b580030000c4d0306400720951642d4040c0d085007003091300140c150200d0815291000560070708031581d180400c0450b440d2 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 470357491 1250 470356241 470356253
    0x10311010f030b04090506072303070507020d05060c12010503030304030c030f02010f0513030917030301030f03030906021602040c230d060314150c0322030e0d0b011a0a0804 76
    0x544400310600d40e480d4150002611207003d03500c12031307114402030512880d201034007a054206e5003003c0749c0d007203800c5069003503c03035950000c90740c01109071306040e6110740301341c0f00245440d4000600100140100010700c103aa400b201e0103050002510780184904d680ca50090564a000031200a000140e110b41c2130800301c0e00500050900e9091480045407001350000d080095030000e580300808035540700c0c019014550700104480107400711603442c8942c2602e0003440c1d60f682c00103020142c0b042c1c0000030114209800380e80319921095001c00d05545980d0700b0b9644100500c001e44043c2e0041c1c0c2070064182d03816100d1681c4040700b902207036528011507118419100140c0000d13500107040ba42d5a840030021495190111040000d80001020490300700c003014041e0100240004c034443c2014010701c041300c0c03440030b040362031412b4038401c4000440386420110f400780b5160b000c00b50001c00c01e90701c6505001808005606a90581500c546504e0303d04115000901c0740d0920b0700d001600340c80100d40007901c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 470358741 1250 470357491 470357507
    0xd05030901180b0a0e040f0c0206070f02340602070b160804030b01080a05150f04020d03030b090a06091a011e030f020d0203040201020d02070b03011415130513020301031101 76
    0x8400410340e1115034030f4100e41c243c59404002c0c00c0021810814070340795185054003c48014000001e000d02805d40a5400a55211400762998090003030780c403455582c0794070803c0b05c141e05090301801c07070300342c0d00410b940c0d010040384142c503071400c003214901e021070200d00028003802207581c0480054501200c20403150141f100d010000c80e072802080000001149500c13011902802d55000a0038000d146894010310741b01e0766500f441401c1402008105240108424844d403094041c0c40411113203d85103403c40003000ca410f44581e00c24000c10078803240c946141d01c160156040940b0800500c889004075940c0d00d904804542e0001d611201842e40d0711004142200c81030300b413420007140c040341e10686001a42c01544182d80c0a503404030400c029582e04100c0b0285440136400504905402c01052902d14401401410004155510705100300d45031281440c0790801000700190302e551516000c544000b040740302e404e21641c8280d07010300100610b4030032a8100c0f58840c0341501410140340040d107000c0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 470359991 1250 470358741 470358767
    0xd09140c0a061e0e0a03050d090e060a2615011a0f090d081207030203060a0b180f120a08030a05092404020a051c0b13110d05190303060e060d05030901 66
    0x80c0c2c80c58919215205d425030a07010714441d40c0540100103e20b8001040d10080c0da1160080e00c0c120014090651151b000d800306403150340450401c240707c0d4141d244880000000000c0e440e2103041d10641c0c1d641d8110700c84a050710a8171416442a00e03007080d480c2c03003038010095600d00c099002c020460441c40c2401482003900d02c1020114204002c20a50100c40c0c002148c817400880e03000001c1241d0740c0740486228020b481505425801c2c8400c264160026503060b0000c0c9008641a210005841c3c1c1d940560100d00d1000e00f00710b0746440030600c3c00641903042903038904031050810300411514480826408101080002540c00c1c0d90f000041840c45c540014000b6a00a003008002080750b03215003004500706008200070401c4031105280910711281d00070511203960940b01402000524103448840d0950403c03651558166206d00f030a5082a40b0030300c207280040c4000041800b0950150807010480c0c4021152130300668a00c0140003104604400050803504104140c06035036004030109545a = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 470361241 1250 470359991 470359997
    0x3090e0a110a050d290409060225050120072015070b0604060f050d05280c0b030705040e0a0608010c031a040608070605030703020d09140c0a061e 64
    0x701c801c854800e04540d0228020200050002814030701c0e0041034050600ba000e8030b445207030303011002409000e40c443d0880300f001e840396031258602400d002c46501540c210351402070300310590015599460042441c1203c044440b9420860300d5100340c40713400000c10120610062503841d01005980340c1d0160710070512440c03034465106640404c3e0380c03200c498450f442010f903e4800e6440c2910308154090440041ca11440303942408010310000c1c640340180700031590261400c900071403251800b1401c04011420b00960241a0000810154000c80012040302d02503940001c005460703408021062100700c0e40030300824020481000244001002641e0007105900000f6219441e40c50b9a03003525400c03404540084c0d02c50b40c00c80400c0300440744a0850000440781044501d1604112645420480c480c2100340304010000401c9a0b01a0b01240c0c2c034051240c00c1000924a6440d003c101c2c4404800c0001243c41401e03104402820121520015240c0c961200000d00031b81046402009654140700c1c410 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 470362491 1250 470361241 470361251
    0xb0408070605010e0601180503030d02070501020702180f2a033d05032404020d080c070e0112030c1209180203060312070c03120c0f05010c0e040903090e0a 68
    0x441e01070302c5014040d150307600300042c503130405a000420901080140700c1105002010400142d0340000c01c58261400a030740140e101c0099007021402402415000303900b004840d82540e8003482a400301e0362148002242c40e01c1140c40d022582d0740302d881000c040b0b24404619082d042d0003200a5006180c0c8600001081c200000100c40144404070b105210700d01b41003404031068510920810062001e030100340c1c024845240c50300d400f040c400c9039185140710a0402400441e00f95102d4525464090350008441903130783e6503400101d030355107085215141c2c2c15030290f0000700d040e54194007184141c40d010782c1c51000651154403a0011101d520782c602e400c0c81222440040e81d00e1042d0401c060002c0103200c0181c680c5000c01c241030502c502e0031490b00c50780c1401c1102c0d00008030014a038805803a040b1000d0880000e118005541601c0340c400090064400050403000b00181500020341c44c0c0c1480c0c0ea80e5135013000b641c00748000e51f81949401404100740b00e409108101804401d640e100c002c0e0a80490 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 470363741 1250 470362491 470362493
    0x606010e04110a18061809020d06050307060c0501050f0f0a0b13090f02040b0118090209010327031d0a0b1c0e0f06010519090203040f050f030405040b04090804030b040807 75
    0x2800343d2104021401140c0c1c0d1180000144010140c030000424080c2802c0080c00a20200c9141c45409805149400c81e17000c290341c07540140a5100101800c1e01800f2640e070240c03130744005001036a0308a42124a90309202c0020318142e2940b2641d03028070380d0484000d046450348064140940306212800d9001615090200d1120890b0f006a203007550089a00b50f248074040c1c01400300303944030414141c0c133006642c490380303000c0303c043c1c03181d1011207900c800016110280d01c1c0048000d881c143c59148c86a03544000c2c449882c815400e080c0c2c6a8501c81c0c0c461000e01404d90b0b1007000121040801c040d03001060400c00c229403101c0030000d041c1400810620b501004480d500e10f821150b0149125040740d001c028000c1116000300142c0e8007401040b01c00c1d107408050761249a891600e01d000796400a500403001c01c041150403058900c0c010780c0b20064586900700c0c0300c0301c0c56490704540729079441241040004222400c11344100c0001a0700100c041e0b2a090440d21a400e0516014204031089202004030380 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 470364991 1250 470363741 470363771
    0x12121302010e130213050f010e10030902030610090b010306050f060c0106210201170f041e02040614010905010903210c05070b0706230f07050f030c07030306170606010e04 75
    0xe15400f10010b80307414081040341500c8032550840740c00340c0c0500380c4d540c1e500d81e08400c041000b050708903400e1002505e10f0314102e001d0700150f000290144102c10600c011120f44001040036102441c1d020401041c0d0200110240c0d096803060a40102d0410030f01e100e40c0c2002d8002740713040050340c000481c0144d0340d075042c075401c45003682d03401d42d1805004000b282190f0f0f010900c2d1461103070801d400b003110f050a8480224952014000805c411503482d0090714841101004004580d00204100241592929186403440c40102424000350241401241d2036009a900d1000d8030b80103507a01c5401c6c060a00d800c0341d00d40301540d000c018003d00d41c091a000a408004403005000c40b0080c964441e01145010000d481000b1b001c0054030b0643d0054071500c0b0390720150240c4c04082d0124400090b16615800c2e1403d02c00c0c02d110348a01140042000012655000101403040c400c0d80c1c00c0102680d40c001c4551044141200e148294000f40081201580700b03201840100800420001c4c070008040840 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 470366241 1250 470364991 470365009
    0x30c031107050c03010605031b060a1e020601051c081b070b04090b040f06080627030a020a0209010501021c0e01030b0a03031d1e0d0c030204061712121302010e 70
    0xc0300d05070f01445510305141420b00a903001040c050340141059400100d0101840c03050000403402858042120503126104030301006841010b110782007440d4000600c003c0d11400709000b440e020f140d1201c211001d4410080c680d01c111500b201d181d80c02e101180440c00c4031108140b51a070003600c594413001c1020707607105000304018500c0003400119925000180070596000440e508945442c0c0641000303a1940400e00e55802501c40c0366042c2002180112018a6100558030700814400415110b0403103800281d8000c50341e00844228599a0783c0d031004a9444044c1d54031505400100100c41c0315550141c181540c500005050102d45a0507000c040ba46041d03007944142c000409885503640c0401c40350000c14589002070381c0d801d03403003806c01e094400c2031307828911014016064020700000b40042c04a411014580c010000e01005e981ca40b402c442e11a10000c0c4c0d1380f0720340600c3c00102102810300c0d080710385078660242c605006513244066121745a420030b400f64113008142680c00601e07a135100c1e53b = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 470367491 1250 470366241 470366243
    0x406090816050d1d0d020414010b0711060a050a08070512041104050a09120c0804050a03060203060111070302010c02210d09080f030319270503070204050a05040f03030c031107 77
    0x31140940d40301d07041161404143c0b000480500c000214040070201119091340c4401c00709454655500d5028804180104488102080700311548800030802c0c105007002480d240b8052074803030500025003000c03c241d81c4211403015002c11420031001000307a000e600070590110590078000e0520700c030799018841600f41201c0844001c8542804111580ba26120f2260000d05110007004980a01d80c0d402040780c605c001104284500502140100039039102160040c103000381c1005402c507580e14003203000c1d40080e02e2050126860f12103104140d04001145012290140e54243c4600c095400740024610001100e20019400740c0c01044400740030041e02c000310360b040e034603207108914145119003803001c030320000c06441d04104280088450000e50403500d080764500d0008450031003540100c444842c03030b01d032051841c2191100406002d00130002e00394103802900c05010b280d64041c0042d04031401224001c013540c10050442e800301f07200e03a200c100e50100c1801e0020f04483d40c601d03110300b05d0700801c030 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 470368741 1250 470367491 470367517
    0x9060f043201060f3906020418110f040b030415090c140d03170709050315040c050a030209070c0201110a050703140304121124181c0b04060908 63
    0x100901503002012041e001507a26003000720320105140c03070f06190305c0762103881119a00e460820b060f401100d0f01e0340c1000e81c0d006c0c0f8115a115a81c150244448041040d4507080314609585007011016002c00c940304058000780b26860079003840403c05441d04060003c0e101152103010b0a2800d1305144204007081b03014000c404586403030080c107858005643c100450180c1040440180001e81140354941c100400002941c540c2e50341110486800d1001d512095151103203941007206000d090000a008a004000c403046039501d0b0381c1400304695061100a4100c0405800a201d891180d103821b480244145000880030401160140c64011261016a100d80203802c0400400807400500018001c004000e1810585004c0c0213080542c1d5109000d03210003442960810155641c1001c03640500403180b080c1c904520804410045401100814890204c03460f5032440600d031129014820f07203650314444c034100005a80c0d494038941c0160040f11016100d000c40c40c0010895009413401c1014aa = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 470369991 1250 470368741 470368841
    0x9060605041a30040b160f1d040c050a08010f030807110109030c090605180402030a0b09150112022707140c06070f02150603071205160305010204050f09060f04 70
    0x1080c17500001801074001c4132640c44040381ca000303858020008114511040c01d0052054900c0041c142452440c16251a070091803c004414aa0b4110020f404000065624150b041e078888503a0951840c00303003c0946050800d029400c0042c020250b0f5025109040c5004249a07540365541c6180e000140c0100589949544c801d002c0c40c12309031580b000b0407401542030500c80c101500440d490380d0110901400c0343c00c44200042c44e41c0320403c8036080505c17580244001540c1e64100100988540c40c5040344034000a294006100302c3c2452400035420721003448802540390854190340782c10b14080c03c0851110103000041c10303102c003840042d11880c41611058000464240f0007403d14600340b54185045144409100558500250040c1516031411a035454003405092052412480081081d0340c0c600d805e60100030400c064000c0e00481d481a14a441807110882c10449480c40440303090760000b0b14440c00b00307901d2030560040c020080b80d45103424005c505030602003040c0e440390041c103d101c20801c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 470371241 1250 470369991 470369993
    0x30b1908160f1202030a050a03020610060203030f0105101106010305070515040b070b061f090602010608030c03033904030b070302090d0219050a0e0109060605041a3004 74
    0x14840e81c404480c2500c206521203050401203001500c06000e0b6000c0c054002c0e21003000c41d1170421010380041d8000301142d054030080c1c60029a00c41049400e4800030340c3c2d4801c0000c9003400041540d00550040500f4065a800d2005002c1c0d000a510b801004210002e0880701c0409070622903140039500407809000c0b0700c4d0810b030030b101c2840c3d00d002544401c0d400400040209076a244182d80025a00c0b5074044c3d156115100000e07140b1a0004480407461200c480122402d40c03c9100b48007201c8032a0002c1c41400d94408102c1e4a80c000c0103c40d2130315800c1003000881220404018843c0e0b100c038141140c0240d00403408506115101110940c1c07415400078040c42400208040e45510070140d2406619065151340803a0050760441e400901030314121450307252500101007080b0207045c01a0100124550340c001d0221481000c0c4180b10110f490a01c5c041005486003086909880707a0a200d1001070b401d4101e0302c0c0c0746a1000440034084e82010300d40f121342c1c80304125030182e031603050f2a503c02c4900305 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 470372491 1250 470371241 470371243
    0x1f030b0a0506010e060403240c08160e01021b03010e071511030307050f03190c02011e0501030203031905040f061709060f0604020a0c02030111030121150c030b1908 72
    0xc05482c0340e0500204054540e55551400d00f1101030303941c0014981c0307150108040100c40d01d101462030011050a01500c01c0c0b03842c0c2d22403205031040c07a028140b040007100c0008140e40d20500c1c4e5151500581184a14046c00d00d520328007000c0c0040c01800004103018440c0005003400c0441d005222500d132071010840d03107198820103074224280b41502852a40c1420b841c0640b251040756125883c03038102100213040e01110408589010a41040c107102400882d00024001c04811052040d85107540381082c2d41070042c2d20901d13060702e601800a40c5000a07602c008071141c0403400344a81007047c2000041040310100140c00e000b049151541c103030301d001012500c110303454000c01291080e131140e03080049142c10a0b09440d04564140e03401651030380e0000f0304a4030018044e4010350198200fa040ea03014558040083d4102c0f4601100200e280703070781e00d10300b041403a02c082c4080c02d01c0e242d8861008480075141e00480200d512402c2c00107144101c43c01007100f100da43c4007446001c91145078100403a04c8 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 470373741 1250 470372491 470372501
    0x80924070f0209091513110306041b122a2102090c130311030a0b0f1501090608060609280f0b04080a11150706020403020102070e060d0303051f030b0a 66
    0x4143c501030041740e40e100c42906200c4100030040340c0308107800201c0303009125060014644450000d000d42c1c28601d45400d00842c0400d640280c400b203150124000180da1259032440c024450348815054445005811803004500404060301c4082c0301c41074000031180000e0072041451240c00c604a015402341d0f004120940030f00500c03203490034000b0030000700485000c2c5404401d0b26407101d00c02c00444840004240742c04014500104805a04400d000003001d4a100551150300b0860568950200c2c20004440a481a118113004200748801040c814a8201c000e05040c003c00340250350725245540c03c0200b80031701d11416414079050550f09018000c0301803500d502420034400143d1905103000c05081c0d54a9201401500052209112801a03501c0100411000c604807103011f4641141c1d0500400039405840100d026200304000041c0008060403136501c5424010071040000d20145c03003d8000d400001d00103541c1d8080c40000b0044180080040e101030341c0070748484186403404140ba07a08445d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 470374991 1250 470373741 470373751
    0x2702090c0304030c0f05032208070902070209131a0408070302010b04110a1224060801050108070504030807031e0207050307050619050c010207021c0b060a03080924070f0209 76
    0x3040041002082d000940380c51070300e6001c1e0310340c0c0c81841982002420b600607961903250f0b4a45401410000e5140e140310704040e20301003419550700e1540c507040c54041740310310503000350800303840c40015000d0f551803c00e09128500074005c50814040c000303142c190329202103a040f5107240c0081110070074168240b0070510301d03240c2034034100074940c2102c002c090702e030290080d0f0004000318002459081c40c0c050308070781e1242c8110f00b9503142410140380b403501d42e50094003a41000070160380c000602036115903005805141140c40e40c61819041d910313424103e0340a00800d0b401d000b485c0b41300b0240c3c0d0300c5400400307060a5803a80513042d01da0078181098208512640168400c00c000d0145e0514003100d035441a484841c0e42c10403507901c0d001d0104440c003a004100002c1c0d407008001c0a00c075814240030ba4005145071103004080681d551b004108101081103000240580b8000e21401c102400c12a0b021961811064515140c0c104400c43d454416400f4102c212852134801403c1800c5003440346407203402c5 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 470376241 1250 470374991 470375011
    0x2191101050411130e070e1b040501080106030929010f120209060f01180602010f05090d1e05040e090309100c03120504030c05010e06100602030f0d02070204270209 72
    0x74202512411000b10340007400c140b01c0d4882c0060140e400003517620400d0404005401c0d203501e50707610a040b284e201400c644080d80a20105901b100d14810641160181c0300140c4503c00170703908000702280200551107040b41c1317448000498402042e0070100d9402070824070220008250b05100c0303402c81446541e401029140c6e01c9400c80b800503990441001d920140a0300c0b0012440c40e24001295100300401010f8041c0007141408100b043e4190007650002032405818400c41d00c40c1503820759185240c4440ae4001003040071000041000b4882025a100c1c2e90310b4220300f000e07111142026410400e6510340c0ca80c1c0d000281d8280c0c5400c2801040382080414203020f4102d0f401610040e0000e030300c0074526100750707503100b0004040600034100d500717445030000000c1145039a0082c8a82e91000180c80c81d0049462401c030000e002d520020440748451090600d1031b0502c8580c1800c02c01941086608a070f1254030b0703200b401d0300c1060000c0080706030002400811000b8145005100c0420030261000b00300f = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 470377491 1250 470376241 470376251
    0x10603020102070302040b03070e040311010510080604020111120a030e0118200102071205010504110307180213050d0b010603050708040807020d0501140123190b0c030d02191101 78
    0x141c0c0c0c002c240c140840b601a5004220010080002420305203945c010740350804034102032005140c0d102600805500c1101d00030445516644400c240e41c540510403c0300d41d6010b040003d005500ca8540c0800c0c01d041c01003107803000f05407407100c00b259030048580000001d50303401d40041c810b4800d0041003200c0e50300c0c0e034144110441c80e80710610540052550340315400805040c1808691082020000400040030710081400107440d05a0280000f5901642c180d0820440700450b41380c0410600102c0300703010764481080c64001d02000103500140850803075000c02d444001b80c5070300d0781c05480d04564803a9080740e50070b40c10420050100c0b05d001d000d0004001002c0204000140d00c44221100c954048548400425a40c58914098001c0600105003a041c02000185500e910718500003e01030440c10101100c1c041014085000203030350b0030304490810304c9410004241080000c00b2030440100550740f07480c445000380400c0e80d10040c03003072880300808031444886070303032100010280c070b10401c0083c0f02c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 470378741 1250 470377491 470377493
    0x506010f05151b0109110906010e01020c0d030309021002070e0106030c0207170c1e040c020105060303030604090804080303070e12011407080a061212020127080703030e10091103010603 81
    0x4107803204508481c1540300001d403141e03000d0981503620000d0510603000740300e07170340480c940040a5204550003c0c05452942e010900e950f00075030201482c860103174020841c000c118400c120f07402004036070503003e0680e90310184d405629444407004956096400a0042c103150040707180007000144d0000c4101450001e9040549a0100301541141c1d0340e805441c0030240044002428400d886050790344c4100c800c6200c0d40c9010352142c0b0040804401c68082062040e001c0050342aa0b00880742c15900d6081000081d0151800d584561581c6020f40d00c86800d05490b101102d02c1c40d031068407590081910142e01282501d408143d4030741e0000c0e240000d022000310403e1004200c200034004505014004000031a1080c1b50b0340203200904010682d191030b0081030410700821614205103000550030440d11800c44152080c86004041c06007080103070b1002503440d043d03c150888c140460416454140001c1c55920401c4000000012100001410300c0035292501e0141c50484205000780d0418070300304 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 470379991 1250 470378741 470378749
    0xc0d0516260f0c0d09050c13090803060409030203040b0309071505210a0e010218090c040b04120302010b0d0605060a050406060509090c070204141504050105280305190506010f05 78
    0x240e0000e08111502565449082c40c4010794084c01503021181442c00381110240800012051a0058256100c0743c0b200d411603a5082520703c3c0140c09012054200f021942c6801e2981c00b102e8880e001e032058909290b00e07501d00a80c194070907640c0c2240c0b03502548041c000030344101404110001a803c0c01c030306e08030070310001c4400e00c1184030f54805e02e6448180012516103440c2c00c00710301c54058400031903031200c00ca4000c40f0800414008140902e43d01c0340040e0b0070848000c112020b40e400c210360241040c0c94076800d20b910510f204411005c41d501e0701c043c000e0741c1c0c85810090302035a12031400802c062030283d05006c0f4014540e8071492046007030882c20090b840c0c22100b2200d05a200b6a00d40030b480e40c03844014215032140140017500607207015202400040b1710440c1d03602a02e881012042400d1009081009444003800f4031a800b80074009200030b1035081070440d10307141d2030001d004c44c007081d500c3d1070715800d0030498075020140d80843c5904ca0104141407018034050710000c844e00b1401410030001c5 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 470381241 1250 470379991 470380067
    0x4060302102a0b160c05030307030c081302010203040b0a0201060911030601110606011d0f10030c090b040608070e041d0304050423010b030c04170c04110a02150c0d0516 74
    0x1e1516400e0329144080c4c091281081da150f05400401302c96890910440060007000700c160004000b850f004041555140044510003110303130143e000714101410000c0c40545680103000d2041950340e01c0800240701c0c0228001c009582211044007070700c0341f42c071780d0000d040303901c00151b10388098001c942000802ea800200c951a82c1440480311810292440042100386494481e201c2e03022110174546070a507503061300161805403140d40c641c1c007210380e58909540c4900550140e04041280040050201e0340b0503c1000c903801c500500c00316040c60740b07445000460300c0011451941e81c04c001418082c9080600030f55480c0d14113030310030210f150560035054912070418060311984120001c0480c002c50800405d48010b01501c0b1104104ad0b0341d4250501c1c1d82c1c02c030880c012401107003000860302da210540400c0d07803802090394029101520b5844c00d9070003200e80c000c00c00f440c0041d00f072254200b019800c0c400d591042c0c1c40c1c602031074001110f40c0304c060140c082400444124805140b2100c0030780d82801c485c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 470382491 1250 470381241 470381251
    0xa0603051009110d0207050a06110703050d050c091201050103020f011d210d030e0705040e1009020a1802070c08030309030403030804050c150d0509121804060302102a0b 74
    0x10004110404400c03c540601c00d0002c05941107001043c14814000b01003000007080c8e03c94401000036495070194090203010300c400c09408100c0a000e00719540081c0d03000240d02412001c070381894450360302c0014190b404d5481840800769910307401402141040034807c0c04a0809003480c0e841480346540c004861000303090f10b0307030080d100d02085012400501c40d5215002031000240e80e45901d0900c4000c00070541110f41c80032511610a0002e1941490321500d0701c3c03400b00c0d20150080e000d1a04505000e0041c560003240c0040c05084002000510328492009504113228090f80d10b040c1424803001c501225005000c0f680c10403c1440b0007103030000300b101d084941c1418101003584c1c85003861801c012180065580026410780c44884903141d00c0010191109041c0c801c0080c2d0326040052031b13498000b20007000e4075890404c8031046030660310703810031164a030003880130401f02e4030781e404100ca0042c800344560102c0c00f0050b02d0060f03109441400c20601000c1300714004100f0b000e490b14850a500909 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 470383741 1250 470382491 470382509
    0x40611160813090203040803072606010f09090204081501240c11030a06020415111e0115090b0a0b0f03040f0f021f2a23060c090a06030510 61
    0x212200c2c50003503144500c0051000801c1103459103007a042c0b00fa280d5004584001c006038646030b5003404500700942021051620562034015070b40e460005480c071903207000210041c00711500c030001d1382044500040010342802e43c041c1c100b441d4081c0c800285000180c000c1050780104407401410f03030381001e400246c10340d8a0316040394a4880f80c18166044040c81c9002509802108500070510000c5c3e0010b10813141e40c1c441c0724400d05005070301102c80c400082e15154464002550301c646469201000501085001c0300010704c1c0401d01c41c2d60b0b40344025560100d8051038442035061b0f00b9203001d2450300e00404501e03100c1e40c5441880100d80d1241c1c030000b000203000403940220607040c00391200c0802096540600b0700c6082c2c00d43c41180348580c0d0b00110090002880c107e907100f800e50b20700900b20300340441a0000080b00b40943da68032061840400d01d02100981b502d101e014400410400103010b40c403900e41c602c1e6190040800d101a904080d003111b410715040c071003442a855805180720080351f401075 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 470384991 1250 470383741 470383747
    0x30f0607031a060f07110d0507061814030c01110c040f0903140a090e07110321060d0c0312052205041b0c060e0c0307030311010b01020a0b1f1703030406111608 70
    0x1400904413400e2000050310509c11511f02003801c5402c408d20420709405c90250766051359580c152116940d5030510348a815030040341c1c034100b6950145524694512440c410790f02048103034000f013012039000c009a07000c0c0f6901c900b400800d00d9040280841e9003031314281524904031440380e0181c000070700c84c4206081f46403c040040c520b00d106001c1502400d405005503591140c3c04c4850005041d504540001403559181c00710364545000704d1900c511652191450112a1035030300d82c003c02135210a4041c045c08000c1140b0041c5610690020fa00c03e1038080340301030980c3c144014082140e2140c2c0c05030314001414a0680c0b0050b03007180c0d8901040b90704c42008030345d5122012515003014107a078416174143c07095040c084205500106070014000c848c2008020700316034000120396a10b02d020002d007524074008040380311700042c1e0035481c1219604d01c0034001d100350756031030681c403800e00c0108224650f0008814801001564010080004061607103e03080110710000021032242034500141100400 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 470386241 1250 470384991 470385023
    0x40e030703170c0403080703080a0b01180b0d0609050c0301090b0406030b19060b0301081b0603041707050312011d0a0603020a1e080303091f020f040b09030f0607031a060f07 76
    0xf407000c50b0f002e1584a000b05885005a00c1d000d008080c042e940c2c4010541890341d69034065100308120031305441010404032000d4130700182000c541e8412030342d1240d43d0b43c4030203010850034864002c0a00400030841c06668075032528075400101d4681241f05032240d41020350400214000408036030300a010269011100354031803400741c00a01e884e91105601d224040300001d0001400300d42035002c05203048a14100c0c440030000c101a5100c1242c00500790801001e280b0206004807015040c410321602c2103031f150041821400744102002d9008002207450620319111036505040080e4105002e100e003408014110344c00154640c9843c022042c05e0051551025012407082443e0001404004143d03075036800c203a02c0b030f04c0c0c40d8032924154500d400400c0840700c1d4003101d00e2080700c0340c1e40701c1106500e0510b41480c1411040b648011192079061007848090303000f03a031040c040c06004a55986000540b2204112041c40021018048901c10a0144074180c403034250398003142d8441d58401384a40d050044 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 470387491 1250 470386241 470386261
    0xf030c160209071110020f0d021c021801031b020601090e010212040506041b06091503060b0a0e090c040b030c03041a1e01150e0108270a02040e03070317 67
    0x880400380d8401094000d100026410003480001000341c4000d607140d405c0c089110006a20400c90240d05401c4200800385482d80c840d03000e01051003004058018107081003200078281d0f08440071600c100e81071044100903540e094446c411383e03120030325004000d00904410181d1a030780144110307250681c603101c0132010f5000030b41c1100e15420309481e08011030304050800595422046a0443c4c12030642d40c10710f105c4210711030300001100d8883d6189c000c11800d00032034580141d84404a1014103490f00c1d80030540f50210005014024445d40c1c40c1d9000382246030820000440140055075004820007080c8520304a00b0308607039000c20152803140d81d81d1107504d00828001240c1a424058040080138000340c1b03510854452028155241c00c865241d03220603515a4100c40b4489a102080d817002440d00705502810419034440b114140440702c450b844050407204549c2d03441c04081940041d6000310452074144543c4010524200080d4200701860b680600350702424010000d01908800001d651000 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 470388741 1250 470387491 470387527
    0x11030403030507091802071208060904080708040b19121814070f0e090706211e0c0c03020708060601090b030417210f04030827010204030c15050f030c 66
    0x205000405e50900c0b481d4005500035001404103d49a41d070008140030007a10802181c0e0051700010070340780311a00c4c0c956801e425a0b000c800211641a418000000c2410703802029007081c4182c8c06800008014981c0010a041c85c03180c011100d2a00c3e15081423100c41e40c800c0003817030b00d90f40140344503245d200240d012441c10f01146c0c408074480d20703000b00119281c401c560b11607005144400443d554152282d4041d5601580401034030840900c1c81d00300015080305800000c17101004650038139070594406040300558880000207000700703e10822000800d581000408002c024031000b50826050480008005000501c00d070410100301001181c240f0100042040c1c03401e030f035080707039a940d46200d500c800000650400310340301d06100c2c440000c04080c1c0d0404410b10969250f6141c04055854201d10701007014100c0104001401408818000c01310901c000c0c80554000e10b01c01625901d040300400f651040229404200181440700402007070507441500c0c0c10450400c00f1644460700c541c0120441c00b = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 470389991 1250 470388741 470388749
    0x601110a050f1501090902031207020d02100504050a1706160210050f0a0501090c17070c0c0e1512330a0606091418040203070b180a091103040303050709 67
    0x80201803041c51801c0e400994400f1800c100a03d0403456070382d844000c011210782120294040d0030152040c2d04141e034000041994a00c02811041841c00e40e80105c4c0701c1a04180d1001e01182d40010180034038505180c02c40b00a00c001041d000f481d9034491301c0706465500152107001e42d111400350b0b01044038002d102d2803500340d00f880d9003040140303440341003081d07080d00598040c44450b03d00000880d04604034010000160b0f4552101e81c031040c109024001c0b8a90010300040c1081110385003a40021100049140101005160140c07030382800821013000071007100e9568441c0c020300d03944452820340071442d11081e40c2401c0c604440040d910700180701c050142d0483c2040344405100300890546151b2000054903403130795585800d50740b1008441c040000018405a1150003401c01d802285070001005501c14400b07800e42d501030f40c0d104200d44e42038001e0410074410120039112111141000c0d05148020304088905100501d40b404440502d0b100280000c0e04241e04d9400007414680035150350300c010 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 470391241 1250 470389991 470389993
    0x615011d060408100203040213020703051219091a0f061003050c0d091a060102070b070b060303041a0406080f1e07021c05070c090e060c030a0b03061008061e0601110a05 74
    0x2241c13840902c1000354000c407030492058010f62080b24025000d40300352590540d042c0c0b1003900c0c11209180c6800c0f0130308018042c04900c609860710000252041c05502c01c000e110b074030002c402118001c0c2916101400800581541010101304080e41c0c0c0c4443d1405031403c2030781800106900c80444006107442502e0803122520f003007103052400c0184001014800760000410200151180c4004a0b1251114881d4a018110511401c00800d81e202150b07500007200030200c910f06580d0704d84d00310005a403050b404411400100f0f0400c0380c9030700085007d611078080900e80b08289052a1000311b401c1201c030342d02a500c0800070001e0b0485000300072000e07000600c03032580300540d0f5021758028401c0e072042d14111940042450700103505041d034040e610321411804050001076480d240f12402540000b4405004c8a441d004d81d103441d0345050000754011030617400000e00d46420903401030701e400c601904202195105103a10300b1812008924190403003001d2030a28050880c802030103140c0848040c024281d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 470392491 1250 470391241 470391253
    0x209070908010c0905031b0603060f030703150e06090f0a080c160905071101020c0d0305190f150e06030a1b082b02160302040504021503070c03020615011d060408 71
    0xc000c0d00003007104c08481c0200c084400078030040140e0024100341c60a50364000c1c07400e1001c21740070f160058005010769001b800f2100159030365219040b540180704c0005070481d9441401815050050020b00d0303101c000c500003002c43d0710311211810303512a40e40d04040e20101e4040390076545503c05014111004e041d0951046a041d250400b190003004280c800e00086609265040c041d40c1040c020313109200c0441c00940002070102c80300b44d02404004010441c8a1042c1c1c1140b5507203103c9106056000c90a88000114480d0101f29502c005e44140c0000c4808200c81d0108081541c0004201442540c4140044044121507041003540f0080d5001078910317000d00c0041500c40d000d10070b100b2040d44601503904005c00b903488016078440d08904038a00d80441e008109002508281d0881d513003080c0301a210809090605c00748508540043d10101e001614413203c0d8018075030704002c0d050300209940c20910b12179103a54006480e207002200c100c0e070000f0320030303112000564a010a6038000d2409034140c0c2c0d0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 470393741 1250 470392491 470392511
    0x3030512100902030f3c09070e190f021615020c0129010c0503040608070c0c0b0a02120c0a0b0a09050303011215020310120c0305102a0903020907090801 67
    0x1020040c101d03060069981003094001800306c803100c84540ca5103404442e0200081c800712002604800200344524a11501c00002070310701800300b040303100f501400410f0a40b41c010621500c15114440c01a031403081c01030140903800150016450303501680900c101c409854010f0400c000383c09004012011540781064900002681101a0580d8204110411149518000191602d00107000080e20035407040c041801410300810301681c01c00800c3c117014130030011039070b6480740100e420b410801440c03801007110b071a80d640400903040d60010440030182091284096035a49007080e500240c610f1a03101e0206100d5415a4040300c44181c200c820380fa41c940e1180c0fa40000c028044100700e50801180d1400090320011344292030140b035a030300c4a01c012900d4050741c06d427810b014640944030381c01c03000d80000000d075042180b032184013000302c00844e9200d45019041e1420240c0e09039214841410800c0b6030340244e02c10501c4090f07030307412102030b0044e498510040b1204000c0b9004003000d58071b0030701880 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 470394991 1250 470393741 470393761
    0xe0109060f140d020f30120306100e0303070309060807020d0e040b0a090e0a0b09010b400b010e0103060b0702010522141c050c010509010c0503220608010303051210090203 75
    0xc18070796400c0449012030301b0441412656060103940c4950701c8030307007030020510324a400850303041d84134801e15268240e006220006425a84540360440114012403020840903421519080c1d1003520740c006807103a010704d03c1c80540400741103110944201e41d91100c440b841d59415111102030995480100f240524150325680d454803a104240e40ea00180d000260114205004420001e0781c0030b014801003c040110030500040e03044401801c9550b0b6240000701ca0380c00c030401c0e10f02019203d0300826943d4903040090602520039145904143c10801309101e010480310071210107070f41c2868081c2e507444040c64680f1424000044c00745002c100c51500040c8002e944c40c1d01c8a540400b280c03401d11114041c4044100c000b42044020004d80010070b480c0380c0c542c0075001a03c00440c06041003590031410760703a20f508660084d56550f040360040340b621203038014060001c5015180d9420001074550568030301408038065443c00319000241c0030005034000c04010200c400808142c3d0041d52a414065100 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 470396241 1250 470394991 470395039
    0x8010f06090b0922031119030f17180705030706030b0f0f03061303050c03040617010501080403050f090109030605010b0a08091207060e0c0a0e0109060f140d020f 71
    0x81d000072030400401c40024646030f00128000c1e80e520701c0420911018907020300c4041e508180540078028401c091554403803040c007050f0400c084110360000050190715025000f85606a0b40700d042000d10080404d00c10744441c3c0c03440d0400d024003640c1d0242e02942c801e40d460210240c0003030b5014010b15000084140e055005960000011103401891900c00410300c0050005020000da06621150104141810118804800d24028900030f45031600c2c0395082d0b803440d84540e000800040d0703500d00701410011070100c221702601092915941a0038580c0300100503010b0340380030040c0800001940c01041c0e001e12080c00040d903114406001942c0d40d08a03501d8283c0154001d840030801040002e0003c081c0070414140c82c2d80015880c074207101e00e64445000902c445c18000100d0311601c0c03125900e0b5601d200c0c3c441c0041002115020300c560422080c0d07030a0b5115680400408a18080d05015a012940c0e042201d40c0e01a034042840800600026688035400d254070b540114422000b640e90007912035070 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 470397491 1250 470396241 470396249
    0x180b0a05041d0c0a03020a1403161403040201050306210703030f020105150901090b010e04090b0106020d030204060e0d210207080705010806060306040504081b031c05062808010f06 79
    0x405010000c1c1c1441c0d24061142240c3e02c103e035030710030402d105a250095015120854031307031502d688843c902e24001c0041c3e07441515000d45025400000e800695405a040750309242d2801002d07003581040d90000e0709901025102c18031a180891604c01c3c0030700344507824122003480000320b60321282d59080c05060401412182e00065081400050305140e240301058200e500240c00d0010b180c0c40c0450310402402c165a860341002046100900259524091a41c500e400784e42c600b0855454881301a2400319014a140117060040c0020004240c0007440341441c0c00c0140c4e542481502246050080001c040d12014410b40b55007000c08442c40e800548102a01c4843c0e044940345038440c0010340d00401c003211900e50090080000078a5070600360000340e0042c1c481d042c4241403601c0c480d2500e41400456002448603800461480c12038403480c2d909101680c00d401c8200424100040070801440082a41c43d0ba0041701000079440c02c00c02e004444002d15200e402040101981240340000d4012446 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 470398741 1250 470397491 470397509
    0x1816121419120f0804031205151302090a0f0b030f18030a0206041202030705060606160b01060509041103010e060405090709060807031401110703270b031807060c03180b0a0504 77
    0x940e400140a04c2c080b078011501030311803490282c403040b603807005020000c0501c0d50503402c0c00c07440a402e071034074000c498040d00c1030003026031a1f150340d00c02d00c082007440750300000c00c140c1141000c01c8400403950459400441c0d60001c201d840d559215420014640080c01c5091488001307186901c1a0b0301107001c501403841030102040f81d82da03082c01240e40740548240a0181c0d00550003207810b9203000c1d4001d004410711040540340c2947c0a454410600c0c400340e000c1c0740803038070004007105030389868442c850b0f21400305e510850440d4148003551701180c1c0c00030100360203542d5420202d9101e43d000c1010100501e0001c0f000d011407a111f0041380d4403038002d440102c5080d032a016604458000601900341903180951100f03080c1181503d040314120031040144140c1400314504650400c07400b1b8000010384030351a4143c1e07507810807882b91401c1d03a00b20291800f4030b41107468207102040d84184840c0e820341e00341c41d0042910001006040c075842710396100400391a0002080303050242c03c5406132003210a040 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 470399991 1250 470398741 470398757
    0x1120b0f091b030703050706080901180c090b0f1e01030b06071e03050d051312181a13120507061d04110c0105181612141912 55
    0x5881886600000e54845400c2c2d0030000b181d07007008064219804001d440202243d075031503a00e03103982d820030348030b6000a0001070240f403c02030000024042d810b4100c9070422003050a0b411074070342a00741d10050103150781705512090500c3c2d040c0d40704100c41c00401030050440d402e2008a400080b030f124207800d8064046400c00705001c22034030781241030794062078010800007402031003080b0295065417140d000300c081c40814007805a10f040c0b00e22400f44568002c1302c0000c02a0382a090401140d9000d03031009080250199140241c00410b404810403610342c005041f4546000181c0d00d02c0b1801402d0340e44040034510100042d4120010340c0103040c5600910070344820a403581c00840e805464488443d104030080460b4074114145584004500350a071400e403410014141c4400342584c0d4241c5201c0c1c5d0b012202c20003400c904900f071103203d126130002008500001d2514407182c00004040b80040d28003000c107141036840508c248880f044102101501c042c0e454101c0c030b800c402803807100f040900052091 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 470401241 1250 470399991 470400001
    0x1306020f0c0a080a03050a0203070639091406040b0711120304061704020d06090b090106060e030604080901170403090f0501030203091e010b031e010c03050103030c1e0b01120b 77
    0x401d4940c2a078002c00007030180d501464174161100d03441500703400218842009843d010540034414200900d904c1e01000420b4203242c0300005a880628000ca0b1902461031800c00140e42c100002404840d4400041c000141c814000501e480c0030b10350140740f00080c001050803c120008a6100092030203c5e9011b04a95261000700d070380340100d000b0080400c801250380401e44041403d207036841480280414400ea0655590400b41c13986160110354a000b81400d002c2044800c0c09003502905036880d2421004141c00002030741e0b1103010f0805880c0312400074005050742d01c035080014940008820f183c4803030800d8540204124050321910b01164000f80001c034030b03988240210382c041c441000080100b0a041148540d05c410031158860035076598a4402c852610280045448440a0759400f204200d02c00720705803e40784004141400c140c580401800001c0c3c1101504d0303069500301d038070100c0728000d140703d69100c207100302c03009003110f01044000240001d5001d10a034174503200e80003005080e207030 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 470402491 1250 470401241 470401249
    0x81308070503070603110d0e0109110f15070515010f0315110403031d12010906050105271e13030f030c0503011208040e0703020415021c12021306020f0c 67
    0xc40d01916a05801c1600f0410285100b60045d00300402c03005051031a14504065010840e80000302d40c2d08683d44401c258018485c492a48a090500580340d401c290413080d00000c1c000303001241b4094141402191020a001301003015851001caa035244090f03070358440385d050700d45661234030088681c045003040758603119140e4010020305500ca208820b0800307003965425100c041840b40340e1221b441c489068030100b030381c0344c801030340e91649540000907080803a0300b4143c0668105030805030040c4107001440e91a8881c001e40c01c1c0290010341c034420040d4890850b00094201119180105844001e045c4100801c0501180d22070b20b1080d219915000c02d01c01013901075581d0300740001e0224500b4401000a114951000e030203561180706021314294035291014141441917403240e000030350106080c02242d00503072000140d262280002e0808441e000340d10752165150540c07800030806620070fa00b0b11200d15805132002203204003502c4450b90345070b000003940c0e80340c0184404c50503c0382488004080c10 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 470403741 1250 470402491 470402503
    0x121909030203090f06090d0b01170f07030602090607060c050a031a011e0c0615091d03091c0f060f0c03060b040306020c0703080d0c080f0c070308180a081308 69
    0x361540246041142c0b0200704641c184515090300e0308180204264011643d604c840315181e140714840021083d410801440f900100e030b81f0300804175034800122449110030005241c400c481d406040960b40d03aa000d000300b4503074019000001c00e514141424045590f800030040d2822809680e401c00c80001e5860b07251128007041c3d80740602080b0000740711801240c4038520341c3c62150b11402e18581003002560b5440484584400c140d1308848400000d0204000c00e00441ca01640b1042e11a400e020040740042c0d22885080d981c144034503a209030040600c0c81c1d0440d03003c0410f401c03070f010070360602e25428a40b000c2d0802c41041d00303c90746455110b124844c000d1061500340c2d0071402c1d03030b40c2c2410f046540e00c41c004d50140c10080c0003481040d030000006802d11004260104821201165175102840f010b40800c002406820f9008a41802c201c08a1009001d407240c20340c041c940500c642e2503d0311340801c4200700100030041805401c61482c10301014000a20b25030003a0100c0c40b403010350701d08070191908 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 470404991 1250 470403741 470403743
    0xf0f0c01021213030c0b0702160b0c070e100b0c0703060207031809050108070608271e06011d07030609110c06090a0c0b0f090a060905030c121c020f03121909 69
    0x40780c5045c0d000c0440c8100c411980d02c0b044500480d0010301d0366505100e10150b0a40c0b10340e0a8960025070300d00445414460f90006040b0b0345546006801c0c940304200202000340619003030000086034615a4080801c500740007507402c031004540e660110308004120400800e04001d4004042000240e508528071903a8101c0d440a809041c1d414280403048881c043d0191043c0b0419a40e1081d010852940000d090707000301c10000185103660004442d02d07202e0501c44000c5d4004e030042001044030802200c14142110300e2903e442e201503a85290680017440030381c00c60302c0c2840c606402000d601e01410014000c0000310000c841d216910700d0281e82d035861200b500200030f511201c0d000c005001ca210003528160b031040c6007550401004902044414500c0d80c01000020400076041125040c14042242c0721541558584038188180e10351350340d40e0f070000000200d90180d5040847c4424420f10074400307042241025281e446800010b040e019080566446a14030620140d0805070030071486031460391 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 470406241 1250 470404991 470404997
    0x8060f010801050112061e0303080108030309030711030322080c1c020405071e0503010311040207030c021509060708040302040509030307020a061e05090d030c020c01020309060f0f0c0102121303 85
    0x81c0e0708000044074007422403014078801c0d07500c1b100b0210340500d504943c00c0300c00010007400740206107542001000c081041e0b10002c0345800410034480342e80b1021040b40e441c0d80d0400e13400c0d20401d0a03800400d2461003241c050080c00c000040c40300c6180d0b2203411104044611400490b0319841c0040100651710421030000b540042d031f02c0e820f0790f00506054002552100007400c019045c103005621040c0c40d00b181d04c0300440010303400401402008a0400346000d062020780d82142040c4003560b0180c060403200307078044d1140d0804100758000c000392408454810801034131440d180c00d828501012160442d000484c412401d100004044c2400081034910445841e4000c00b14a5a00d803140001800100082c03100c1c1107841c484840320ba041405194018501c160080c018030b4100d1034001d003225400c000d48011500700503408100d50ba400002e407a80c0220485010b9a140d03c070078001d240f030b4499010000c0700f0078030206200610070810342c003030b05004080c400f04c0c0c04683d0360004004586281d101004001c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 470407491 1250 470406241 470406257
    0x70f03061707090f0603021e010206070819050910150e010b091309020301061505031608071d04180c0315060b03010e040213020d060f17151b0d05010608060f01 70
    0x203041e01c240c04c403015100189000094071a1a87c000c615403245a0b4031081c0384950b0010485a5568108030490303000c502450015540c2c1090314056050945600d158001162208041107110310280851007500d2a0800108468004140c8240004405102c0c46400d410791100010300314050700100c504402c2d0003080e402046101c50094402815408800d9803d0340d0b031450046010020094009420a49519140c3d241c0c03070000b1003240d000300e120032590200250b507000d21098a8101003840e202c0000e0400740344148056201240080400e03613080c040144e5003400a10500c848518508160703805000d580390403c5c0c10100d01c400355841031003982201e22040004205e198011074045400910040504429038130304405882684c0020a4020a031a607a100402881800f1044c2c0b00c0289804c9802c4004404861100741d12100b49964184503140900d000620294900145c8800403a00c4141e090315440007803194030041009004000c042000f40700410414a044266060b150f80141c0d19514 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 470408741 1250 470407491 470407499
    0x1020705220e0c2b080307030b100f05030a0b040905070308040806010f1a0304030513030c1404051302010f020708011506030e010207200a08031602040b0901061b1a070f03061707 78
    0x5010b101380c1c10380c1c210800e0181144000610424000e600a00c5141d402041503408002041040070201814100380b244501002d5203868025080c2c079131040468030001414150400400c010308080d180080c100e00502201108004000001e401039a042c0011261540e0301e8820406080344203004040c01f075009403400701400c51801c001542d105100b460451308000442c002c402185d15190000c6a0400740520140400d1800c0700510302080380c00c543c1845103007002c10381c120760110400c0c4040e040140705040b048290f4000c001c080001e081100023000075510035208060150068020080000d0070041c0001c00024140203441140c2d41040001005489004a2070180b805420900b600710f600c21400203104041030000c2d202e4000c900c219000e031032006204001c1110a4001001e102d01d580c4c800511031281e0012001503580007620340044050018148104800d80030001ea0301d04420355000c100345141d024615015021843d102442015158055070213803208008001b00240c0c01400c1c200 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 470409991 1250 470408741 470408779
    0xd020d06081609150503030a031d0c01080a020c19030302030403030b010804031d1f050c06060d050a08360102210a0e040f060b0a0e0a03080d0b01020705220e0c 70
    0x6180c20003088001d1307000e1955500464116005801c095012a54580d460862045a08041800320500d00054481c1604410001e4510703000646407082c0f156004c203022038440030070494a0041c8010340c54455181045141c01400317540304940440c00241040010100c07540921011030183d50706071500040740d421a81000c00001144000560012a0455880d100a28641d03030f4485026140da615945048905601d4035003040640030340c2c080d80c00440c000340407500124000055a42c002c1c0b41c1760b42c03440c0441c201007660f54050065076401e500140e0001a01d200102d80514100c420307000d0b2100070044c4d0103200c50051000108040b80d250411040302c0e441c0c07250016491552000344000303086120f00380420200c88094000045000d800948440b00a0700120f40c0d41518008035044d1000358110340d141c0c4c8507402180c070f14200c05501c0b05409211a03000f401040302a007006041080c075088002e010700d5400c4620001002598036160960301054008601c1d20034071013001d46030003950390f0f04014030 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 470411241 1250 470409991 470410001
    0x11a0d060b0a03021201061a090307060f0201151401030f0b060a0f0923150c0a15020c06270a0210210f0903260109020c010207080d020d06081609 64
    0x80d40c0b05107200c802100682e141d128604842e02104000034050b8240051031302c003510300d40414014910148008006640c0003d080d10645200b0310b04081001100c0d103081c3e002d00f0740c40d14100c1c0310003135400003c2034040c00c07082104101a403d036803d0101148030b0468800700e51003100300303e0b005182080390780e504c82c4c0603c0c40c1c0010080f81e8a80000c0251341c5401c503212181c0c4018a04600400080601115103019144580c4868948400320710306a4060340c244d03524042940010607a494280c0c25014041d4a0382c145c0d00201c469005650051800c542d8145813202c0c0c07584099004951314044003c060b80c00201d4841e0640e01078048107109000040c180d4441c114030a642400701000c06000703c41d04007a00400d544408003080124034a0200c2c41c01a1a9aa41e6144801c2234880b0b00416094100d5503208181101d203403500050361030426144050181c400d000c005060070070f00140202d00c0940c0341c1d0081c10060b60580c0c04018045e1106a400e8842d04407110070040f450155000b40702080b641c1d805 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 470412491 1250 470411241 470411261
    0x10603150302060a260601231210120c050312120a05061c0c1811180f150d1407120f020d0504030e010801060e03030a050d0e1509011a0d06 61
    0x30280341740039468901d00c0d0284400741202c07034102104003481500e58124200c0d03c4038061481c03118810010101c1e080c1c10500a500c032800c05203403400049160780c00075a00c000040d02c00144c0890310715109080120b400c0b4014421030380240700c1d40c000903400c03400210590b0210300b40c0b034200041e5601c9025880b4041c0102500c516809000f012054000004c403501000c203143c452284906a00d00d4110400301c412042000003580605001e0390292805000080b11107460005041c05e06413003a000225003250030008010f504440c0d03400d0040003600d12200134102c4031a411506104040d0f01d0030882c5040304082d40c0300004a41c45904100124041e0303004540c0d150b4491000500b408034910300c034019220300340d07419000326405846414031075921011f424050081070411300c29201400021960780e00c60081401c00304880800c17a88115802c64000345000c1c15540308031000400e1004c180c044400090300c4511940d884c0c03503001d8078404c221000600040000610001045605803200005000000c1e0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 470413741 1250 470412491 470412497
    0x3100e01140d020310020c15012103111c0210050124080a0b100f021e0d0c15020307020f191e0203100504060e160e04020103021b011109010305010603150302060a 71
    0x1044034441a41e440600036054007080107041800c8041080760141006800182d611441031300c00c1010040c04218041885625241084111b04c040c00c0160410dc43c486030210840205500200111b84c00035032188003910090081000b81d03a01c440281c0703100d4034005440410200d502d440819a800b0382862a4011001600403d500e42c04c030000600d420354a51000d00031482e403030b50385113040368100036000400d61580c80c0c04000c0c1002e80055131b99560311803403150801070b0054400041100d0b0202042d000320b8000419501e038204a04041d4032444030032081041fa108441210342d0500180f9988010540c0104208070910704120008001c0d070749500041c0e816218109013146042a58402c0620540c06400001111034039510610304100c54503200c0e1031500d0050b10103000404950b14400d400c01e070309090041c1c1e50050280710624100e2803413001d007240e51030514500c132700100d030381c00130440403d00f41c0e070400450384c03246001e41c00c60b2160a41c01d1001048600c0620050800700020111001182 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 470414991 1250 470413741 470413753
    0x80d052803020307080f1b03060f060301090b0111070e071805091f0927020102010b0909032d0919050a0f0807051c030c06060e070503100e01140d0203 66
    0xe2400d540e604405045100060340c00001c0241c402c0d8441c40c1c040c0c2000852544400504058002c074089080b01803851480060000225007030f40d8480c5000c60b804040a000c09890b5030356a00c11000500f088240c03140803e01180300b50b10007d8002c030b049400d880382c8070756440c083d458042c01141c200383c505881c1000c00740c1d0104086115036414980341d128802041d02c05c042d812825407180c00810303069200c010014100038041003c03400300d5900202802040960007045034180c00100e000d4100d03100c03503940041c3c00500740100b41c40c0100c010f104110000403500000818502c0d00d4034107201311025005001802d010710741d424900341003000c240001d44440782e00080e40311000900c0941c416401203006900e00320381040603880034000c000c0200411104000640450405205c0502284030b008040095121018082005907844a0301a00000945003810b207001c0d003002e40907610584502d4518400110300040307101281c2043c80c1a00c448555440e40c41241000340300d14010308000c01c80e8140641 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 470416241 1250 470414991 470415037
    0x305090409061a120c010c0213090b0a2f160b10030c0f060e012001060306090302210f070c0b03040f020a140a12050a061b0216080d05 59
    0xa0003181c03070150040304006528030044450829500d041050a8010502c84a910111070004280305030b1601c020300f0120403192680c030000e003201d1000200c0c20f240602d031810b00c205104c4240c007000d1042c0c50082c0100031216102a4003940110540c01000441d140d000d090050082d1b06009040f641002500400b0181d110350f60b00301600504944054000b18030740010418080f918841900034002e035004140043d0409400504090300c0c14400b5040c00100c841e0408486441c070522901800044004c0080507264500f4030003610a0400940040c441d40c00d07180d44012080680301c5609401c008241c0c41e10131044040001500021b8064410301d84551380040d1000e400300086206510132001c0c407206189034410410320f002590403203542441030220701d0b0a0707500d0b500c40700e6040d11500005201e0303102141c58031314a4003852a070000c188506220600c0c4004400d45403c41e00c0b124141c00352864a02c4101c444040501e0740c0c825201c45601c51a0f04507603081c0207400901100c003441804805c00321132 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 470417491 1250 470416241 470416249
    0x1103090904060516032a09080703050705010806060903070911040305060906090d02030a02030301030f0804031509120f0c0809120604050d0905010e030c090c0d09080702040b0303070b010909030509 86
    0x1141c0944550f0348601c1000110302e400740d041c9080090904081016911204001040318030666041030728422803543c40f6040f0740103400c10741c01044408202c0320450748070b142c4a80ca4a440b88109800b09801d038012403850703e06101610800b10025009065182c40c2086180c050050800b1410300b029003000041701044041c4800d5100e40700d8070740101103c0c01d00201041ca0700001a040c041103403c10b03c40ca030811079011044038112038005c540002c0848050030581500e01c1558801401812245060681e113030140e002901c1b614080c50040320400784015003692070303070020f66120f00010104800b0600182030b80b40030300040c5602038842c001d00122103890616000007502c0c117542d070354004400c1c489103607440304c02100541340078a007001d074601c00304021a0381c0d013000120040c4901c00307101c006095180305a081e038015004d85101441281c4840c10080500d500c280030030380c010b905202d09130f0540c0c1000800c80b1051a401030709001568640041d00f001080e090b41d048040200400c130f140b480e540e07 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 470418741 1250 470417491 470417509
    0x601050f0a0206011809120507020a09021803010b0907020a0b0a0b03010204062a030509040f110a0c020f0301090f02130603021806011106092109060d0603030f0503010e01030201110309 81
    0x1582c005008650420b48003101004041c10b0b2400c503503040c196401c002842803800318196070b4035810315030b49540c0d882c80000e40141c0243c200e4240b187c40401e18020250b110244508070034425002000035110741000d100c0030740d80440d46032015a12107450440007680c2d9080a540c0450159400036850f1542d00009003a6401075001d240003070b00070402d0702d2148a40c40506810304407854800310400d0100d40d0003400c43d005901841e40b06940c0c0e0003450080700182d401412015a242c13805941e20001118007400401c240b07174059010f8503580708015900c1c101403084034410b40c2c01c04505103111040340c0c01c00c6031808845101c00d5400382c031102e000006031a5503607a0030050075250306c05030b140d16140000514465070819201c0c2d01d9885030b400e21044030703004990b20b0b020f054407014204184a030407600d80020f01c0303a07092090b00040000388045d281422035100314156817007652040903910f68460100d54900080c020003483e901c0c0240100010f6000718040070500034400d003038a007440c00000c001001d0314 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 470419991 1250 470418741 470418757
    0x6040803040b150a03030c21020618120f0f2b050f06010e0f0d08190906110c0f0114030a0e07080d080a1107290c040e07080601050f 58
    0x14008030902040010100a056014500000001c96860000009240f084407880003a0620101002900912402031001c850005644502c100001c0841d54001d41d940c4040b102c46072880f03031490012120603008500d40c455065074090103820010703914810b051a030300c46c9504010100017042070031220560140102c6000843c03400d01c0c02c0031240c1c0c0caa10410b40e88001c02113142c00408008220a603a00044980b40301c1d403041d1480300c10103c940000c03070242015200040c0903118042880100300c0900000c280c1010003691360860555514801a244043c1e24101c06140d40c000702a003559a0404c602c01814a41c01490010303118010f9030322868241e40706a842403049038580111480c005000c0214000030501c1200820080350100402400c07410040c1c185410a40c032014402c0030078503c0c1d01514101500060850040c2446290700008081c00404e40440000182c00142c4c6039446001518100d80c444505414150307a000421613070000001e0030175050000c10700010341001c0c60310018010b01 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 470421241 1250 470419991 470420003
    0xf1509080f07080d080420030717100c081608091218040b090606070f020406030b0906070801050d03090b1606110c100b0f0625030306060f0206150111030c0604 70
    0x10034204a81c15040c804c154000d4030501510030107220008400f070103c140c02d0400b101850b16015641400030341001000d42c403025202400740a620b40fa00e0002c2034814114182ca10100002c200c088070903220a803048414400d000250401c5010203405032180c00e0307009882d00305a40400c0c448001d440343e150040381e038030b00c04084166840450740c2014070a080704d21008aa15810b0b0b8607001000503901d1152120007015546404210070443d00c940c2c010030017455001c15480c0703a40c50401d04065856400312030791000940007400020301403c1078940340c8002da0b0595510080f00b410509243c40590000d280d02001d811001d036000702013406c03441b9441c0c0c1031150000103943e5441240d070092500140d98181c0740010303d4031080c00c1b02503407420094906000181c4440b600c564000d0000e103451080100d0300d20540c001010111304044d0306a0050060b40c00e280c5810f042d0303c41040c0c041340da401c01200c01601860380c0030400c081c2036000d000407120346168107084a2401042254090816100351412951 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 470422491 1250 470421241 470421253
    0x5030a06030c0b0d20041205010b0307030317010b030601050a0f0e0307030503030702010b01030e07030605040201050d020c0a0201030f09030206070305090a080f0306030607170c0702010504090e1b0402040f1509080f 94
    0x1380e9141c2e006058200c5480c410014a41a90b10a0507001b44258480c482081c42c0350b030b220320700300300081d040301c140c4110080a68000c2540c90402910b503480b440e81160501d68240e001103590190802039901078170040e5031303040c1000240e060540301c080001031138100f44140170851070225a8108070160165118030051503c07030400d684042e094810084103e410f160074042508038480340040e240741201d400c41c2d000f003145d03111400141c3d400c3c0f10707401c0741d030f45454000580058807003000580300d1001c51003a0b07002c0020100c10005c01c0d0441c0c00e140780040041c0c001101040c0e0b818400d802550b0000c2e030741001da8001d1035139943c42001c00c2d84401c000c602201004010401589418848194010a5420103080703969407d40d0b0720448050007041030071017640104000041da4407403019203000d014495010000680c44050080e030301c3c49800c050007940108103600442c50b00741402901c04030b4003003001003503010f8140700d8070102515080c03e82a0030024107240c0021400310402c80702118006c01005031003 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 470423741 1250 470422491 470422507
    0x50111101d0c0a06300e010c020c0a0302152107020c010215070c060c140c060a061d01090c02192103020915030901020702042c03190f03110d0c0908070807050105030a06030c0b 77
    0x1040c10206103031113103c2d446082c010800b6031180100c0d036001060300490f16a4598813001500040311146d2603030781d800d3f5542000c0149058000400d101c2c0c440e001d0f0220f82c400c000410780c0d03540b842c20460b061380c0051a40d0094a00081e07050f040b60715121914200084c2c0e11126020321007240d0071002c4c00440c60340c0700405004c4884051722412018012140c42503142c081c60300018001000c06119072079081342e4036001205154800e0098004c559051001c61180e404141080c402e40c40b00c0300c1c6241900c0aa07140b9203590607000e0f1003207552041c00a4203c1c603103403160f20810f400c281c01c003c08120003035408224004c01682c4030310807101c034030620007d41b0600901c8000060303401a6440c001e1070990380104203902c07400400001400e4495804d2901c0794850390081000c0340901080c4811a28000010502c204609001c3e081a2604035003555401156952a40142e54444852298180c42e0700701c0310007800309512940007180d00c400d21540100d1050359942d510103110780c960748900c41361400400e1001c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 470424991 1250 470423741 470423743
    0x302030303100e0f06100c0501060e0109020403060b041e0b030c1203040312050f2a0a080c010c1403010b07081308061506030907050111101d0c0a06300e010c02 70
    0x503000345204240070380c549442408100080303a010304107421f001000c6105d0003049401d41022003c0c0540c14514012940c3d50b4140a004e90001e0000711617071818000a4070890506224000305d500407140e41e8801000704d1180c40009109210000e40c26001d500781c10300403905c404d240041c0218101008680d0b0341e2440c1051501d41402c0f001d44000c01004201c03070304210b0410800e507000342220780500008800e0407000c00070304043c000100f903458001c0c2140c0106215045024101c111460300090004002020302240c00c4481a441a514000280010f221495400c1c0280c42d030544144d9803a0320745a10200881803080300740c1d03c2111298000001c00402031801d807283d41050030141e801e14210300704241c48079140d15540c0506030400c0a04c0003086640c0a040008080c26a08a10f04100e242c481c00150100c219551801d040700c0e1140030041410b80c100390034a44211a03540e907800c00b83c814400e8402a07211360b0741031218404a41002c000c60140154416550304070618000044c10340307050300d00030b = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 470426241 1250 470424991 470425019
    0x4030c05011707090339150c050601031203020708040e090706080402100806030c04090f0b09060405061506130b09190b121e07021e0331030203030310 66
    0x40140302404144002a5045802c41080c2c0398002d02690341d111000b81e90720b001070300d51414a2244e444101d00c03001c1046c60111040c0a5844000d034511141641840690741003101600060544d070042c001003000c20021000b0f055034450700c0c540940b5007012600c840400307801075003003807190364107007020f0103901031040281000900b0b5a09006090313240a070001403404c0340a52080d024030034170000166080e036051021101203040184101b0050040b414205032442a80104681c95a0703203030b0100701800d40c0000c02c01e100341d900c000282401c0d622613041d600d0740c451988000e60401400c1c04003030550402031035030001800c00d111a0740e03101d164400401030b020190380d00c500f009004d400000d010382c22501049075900d064201c031501c40c0c2c0e03c07a4012081e800c01078540d0442055400c1003840b070b2980d8003143c4604880084c0c50008100064400c083c0d40341d108035403000d0451140b100d20341c3c00740c43d100c2c10301100940f4030300502c0520580e40c2e00440c0c21030340220f070114a41442070800b4800103856102c0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 470427491 1250 470426241 470426267
    0xf0621120a120b1516030e1207171621020a090b03011803050306010513050d06050708090106260a0b07050406020d08060f040e03071202012702030c131104030c0501 72
    0x90a00091022002d4043e07200b2080c00741750080410402009043c091048200e208402800044268401000154890300140954000c02c03004040602d00310364001812855a404520351030505854a002c8108212102010310009400942d0a10143c2c2d10080a4001482c03000000300d64808408201402c40d289101d010b2405415000c100010903802019607074031000a007046035030b070602c00114010199459010562101c0301c0191003040022907007005000380580d1b1102400c5445d030080322801d1b80c5550103000381065202e0780751040c443d0010881551205c02c1415030301014807a0b294110704081c101c4003c1c010620000741000380c81d604010f0030282000d586056016400d0200c00130f900b819602c0c0b038042c451900d034000c14082d200184211107040c1e600200c5201c070050b44043c00383c0600030f580b0f0144041013506006000902c5001c0255603803541c024040c050840c3c0000401c15180303240c00a4541190382e0742c3e440340d500742d220380003040690b00030141d50312210300c0c000c0010507010075202 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 470428741 1250 470427491 470427499
    0x3040c0b12100e070c120e0d060209010e0604080a03031d010e061006050c060f0405030f0c060a0f02070209070305100519090c05040509040611070210170f0621120a120b 74
    0x420820715650100c80b200300c85a1021b501c91860000040444400e03040c0d0003019400040c02d5085e408101e282d078000c210034102a2904d5103031b00c84c03100402403240121f110f000040e400c405a1040003c3c4640e0182e001c80381220300842140211403965030850300d20007032080311a400b55040c05a01a2090112001031510345000c40c5850050041992100d5020300150260403841d008541000810b0042c1ea44a9034008c1c64a0346448001a02a554803801d54000c9a858034001454034007041c1c9008480ba610b4020301124203e4541c800201c0c0104001021520b60b00810840896590b40702030031680161449a54124010b0a141e0b400007212180c0100361b0900c10304100401ca40e4880141c59680305400c1640001c9065400040f803001d8450540006d51090804400700030b402e4114020258000c19507503446d00941d42c08405010020050f5542d03a4800c03c0b070703130600300f2207029207030740096840c1d107001a10003480504030401c3e0281c000c030301d00c00080ba9501400700d85031031561080c140c200c10100c0e = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 470429991 1250 470428741 470428769
    0x2702131712090303041a071b1e03200406150905091614030408040b030a0f0e0726010906230f060901090f02160311070f031703040c0b1210 61
    0x41c001039a80d2003107100b0742a921a2a1606c2584044a1802e6070300c0360782c01181d0346000c10f00c030809600540500c1c0c060500030031140c8a00009003007003260624166640002140100028502600c0046040b00b4000d64040d8480e100428900581c00c030102c807512241c2c40384000c1a041104020307008a005005400c401001001d54130800d0b80b1500c0340d0b504108009550390790b51101e0030071014500c10f541001941040000a000c10502c441d40241b444036041c41d0100100040c1107005500da690903c00e15551102518400194a1942034188504100440006581c0e0b10580d100b6041d1100c0c1200402d032103566108103c5008601c0d940254040f1401c1c030901d940e454070800190f55202c0600900860750340d80c1142000b91805541240c0c0a1400700f07034260281c0241c0c2c50700800403001842300d220103002d4050300203460f0b022100c501c82580d920814042013013650845004582c0c100900560703003515804000038207900c0c1c020040c61445203611a000a91400c22811048099607034018110701d03441d5 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 470431241 1250 470429991 470430007
    0x9050c16061e02031614070b041a01080a1106030a02040e0103060506010801120314030c09042c150c0c073c0605030703050721090b090102042702131712 67
    0xc103e140b11000101e00700340707940c2c010482442d5950b000c0d00c0c80048c0b220515000f13220a1101488403008104241c440707440f216a00c0d4501280c60302e4860b08001d011a060342450035640c90045c0195912102c000c07001414141e0740c09002d9500b40d42070b4420366a43d0740c0e48003404840e50340408070501504142c4281d60103180c02d503800900c3c03042c041003a016441c6010011070044107020048692141d4002c0090103800c0e40090b100c1d8401d070041541d20601c0c00c98030342050185130f0124a20441c038550740001a01c0e0b5030b0b81c004142d0349901c0b91040401f940624100400e0903402c1d401c0c04031000042d408903140344c1d0700f25582c034254181c995074111058a042d1204110b01c5030701ca01117940c02003107860081907944940c0d0007540c40c109140031071200e0150000400300c40e80410b502a084841c000c0d0b040c1c452646402c00c91a080f8810742c040c110000310b92881840d0a9003a41c4050b951031220300c0001854840340064035003140780300c4d4020088454584100000900e820407403210510b410060807444c080071 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 470432491 1250 470431241 470431261
    0x3100b0307060c061b02030a12061d061908033403030906060807120501050f070903260f071103010b090a0b060d09030c05120307050409050c16061e0203 67
    0x303144161000c0041c0e405440f4100a001d4001103010450516a861500c00802c00039450341c0150040d1000145081032070715030340342103006140840d1041c0b4900103031061841054440078800402d040d40040e600410b5000c00d2008008540091410b2030195031102800c01144201d400c42400484c0400310b0114070718510b020710700c9689402c039810f00340007840ca01c403071600d0000342416a01c102081d002d030150010350058840a0741e00740a21a000801c016074400c10440d0f40700bc410784110000944102040c000501c481440d1012205584580c0e40000d01681c980000c5922203e500c0ca180c0d00003140120800c05070100045100d2011002407100c420910086103640c20018031418a16407920301c588070301c2e00c07002c049542141c031000d02071001120606018080d4407000b038040b00c05101d408801252a2910010f4134098200c2da940d60346011301e88111640545005001007a00390b03000c2041000c0300c403a044103102c06030b100e003a01050030600d07004440305045041180039007a6004000700003101107 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 470433741 1250 470432491 470432503
    0x31302010c1a06310b0d0f0501020d0f110403020603070207030606240e0d020f0a0909140c1e210a0302070603050711070308071b090209150c19141002040503100b03 72
    0x800e884c0005000d202c8080051190308052401801d2600d401620b0400d00106400402c802c00250405100a010b40b4049070111000300040d620300c00d00500080c1700502d4100010b5402c8040c6d4411504140d890740c85004c01c681080e4840400ca010315142c02c080c9010242c01c0e60507500041c10001c80b050351000c0450341c040c2a88000900c40c4200c500001ca103583d40c10020405046850000c226412031403520f001e4031021004000782510414041a42d94a040000d140502c03c080c006080501d0220701880154001c1004c50030b0300b16943c0d104100d50102c01c0010b448103030700990040c2621450010701504807600034037810200200038500d40540c0710001800e0317080320b0780044c0d029500d42060030445403144145030515440040c0a00001d80100700c0e40281650140071649001201040d0107009614420b0544135160b98000b4240c0b20401c43c000c000030442e01d80920402000314004031080ca042c0410302003a03503681d5901280600641c18204200c2c010035442001c1040b0101d0380b08001b130381d511 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 470434991 1250 470433741 470433829
    0xe0f100c020a0f2601050402010903080d060b1603090503070f0308130801060602030c060907060c0b04020d080307052503170c04030206040303050d0b090408031302010c1a06 76
    0x848014410421902c92000700002003004010b010111501e407011010040140d0b0066036414a2009011a980130180300d114029236050316200c3d469491a919074242e9044107990940c01c503a210000584d0b0403c006c02440d200420030302d4610203800b5481c004c0c0480b101d81d00203a01a51084100b441030031150802c420a8075002501d090311902115280f83c105041d42c1c00400c00d40d42016000184641c000003e0680d4280003400c0e1805a5542040c4903a202d14511884001410000c4000040751510b14810303002070020b005008951215100e078202c550040d258139000903000100c8101400d841c0300d10740101481081c0c0011843c0003501c4c0100790040a050000f112040200880c0907040940121002181e000c0d00d400d4a4940c0ca06010701282c05c06003248103a9820038210450a18207018034034802c981c400c00480c11070300c407100c1844000701401030407414080080203500200e40258410800d0f00040709200c01d4520781803050102c0050001c40c040458081159205c0310107551840d140254 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 470436241 1250 470434991 470434997
    0x40f090308060d0f2001090602010b0a05011b0609150e03070822080a1a010506070201020706120f05090102030103050705120703031b0807030305010608090304050d0803072007060e0f10 81
    0x9000c103402c4c00e01c1400420711004101c948042c00c2c001c0c0403150002102d8400400b607c076945016a905030690a0310000420107a00c0070845900340a10b60003401c0720a02c040d0003880e902d0004100382d0310201200d4500700103942a50428a1080e4500c4150060080c500102d001171804c180c034030796a503610b41c06002c0803082c10090010340c884130300b030094000c070f002421440c0881c0d5101110b0b092166200b4188000c0154034040c440000c070311810040b00f1104078550683c028030040b480e002003100d03140f0680450810709512a010300740e80c11654060780380a19a410001640c0c0d5145182c021300e803542980c07000e8010000400c00202000c000300c1c04004603501424500d041c1c180e400c80c0b03d5844071802c11b0003010103e0101d64441815899400141a83d04a03203500d6083c1e01d601005960b01d00691144540c0a074107241500c002401540241d030300410a0300b890204210007503d50813201295201c0500190b1044608210b4685d1140041c144d072601a00e541c03140b5940c1070007062203040c0042c1c051042c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 470437491 1250 470436241 470436259
    0x172212030503150d0507030303020910030b0f090a1e2406090b09010516050d0206091c11031e07050c010815040c0c120314010e0106021915021206040f09030806 70
    0x281c6880c00501c403a668000181d81d107254503450b0140080d00410403403401150060202d81ccc0582c00382c400c500d01d1900042030080c0c2a00000d0800c1545035008109601c0e284d1201c0240c191107102c202c000d04a03401c10200850425145481e0030350a40c0351078201080b03400344103c200982a004503440081d154619000c40d0b9603206080142d03150f1003040b02c0f8018800c80c4610f1364081c4100494003202000c6658256030894a4014503c1d40d1410b41c00c103100a0030000f490300c2c00f1290700408100f13021900e00301c1900d00b8464a20001c034260210704a550141c0e840014440742085010b111290b42c94400342001e5525050480300c44010454200c0e0381d070b0013142e07180164a40c2c07500a036103040445505c0090301e41c4203c1e18802c001c02505106510040440c4500b00101e818040d074511f16040e500582c1c0280404084c3d03281c1c150318644003c1d025181008003400300808ad494900081c8103040040c90340c05c2c0681400410300c000c4500440c010110705140610840019600c0140150092022220824 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 470438741 1250 470437491 470437531
    0x71703062b050304031a0604050708130c0503070603090b09060910090609060510090605120a260f030f01051e011d03030d06061b031407172212030503 66
    0x7007145180c800190161101040000c10000000e44101d414501c1c40e110039030035115201408181c030415104000803419220005520320108060b03000301c10f00030300e103a5848541d5100800d007000640d402c400b0000f9101c000e24010700802d00c031a2500040c482c8c009203c1858251092a200c2281d00c0c2d1380c0101a0f00d0784195410320090fa08034100c0316400600801a50800740b40481510300b0354480d00130700604000002a40707282c40d0050752035080102026061400700380e501d02840b464040c0289060981100500020107c2500a4800f001360341c15020741d24100410388200c5c0c5801640400c1c4104101024101c0d038002940303071242003440a092003204000c113904a40070700c8024011040c2c26204c00b103204c100c14491a040301040b40e0194a60b000e09000410b880703d0188508440540440c1d500751340520050761100080000901030785100300c1d501ca440340c90b0071042e48003104ca01c0826030000301c08411012522944401880c044407100c9003494203076009041350000402d07400f1140389210310a0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 470439991 1250 470438741 470438809
    0x18050a2915010f02011103040803060114030c090a171e010605060711150306030a030e13020304060c0f02011b03090206040302032416210b030d0507170306 68
    0x2064804284031560003615202040100d0000810001c600081e0211010b402150041c441e1143d580703803400c465841c40c0d1f0b40c3c0d00c4211b03042d4000761a00e0b042110606c2110300520201e0051802030003880f0b01c01d07030b84251507401c00c405580c032a000380b141ea202c402c80102e84088000780c11070041c5424100302e18121220752489004101c0c587c8031540000c00050305000b0030440c066406c1c0c0c0703c042103d8a00701220030000c4110749000484080e905503002c40700c41b0380448d000ea00449200c1d0801040c43d0b00a20380044041c05a0f0401d4034119802526100e911101c10340051507404803191510007000310021140c10400040501e0040c5018150f032001000c0940d101c041c204c9004c1d64001c0c00311464002820101070010807020780309000c0810540105003001c0388100420506440c680e80c6100b141c1103081524001c0e015001c048010b107998080c0340403292424015608004103e450700340d16030825041036000207807400c80040140d2810820014180c2e1240d05200d00a418000481c608100c4070b4070031 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 470441241 1250 470439991 470440043
    0xb0f040b0a050310091401020f040e04081c0e010b010810060c150c050901020d0908031c09051b011b02090408030601020f03220504140a0509032106010318050a 70
    0x150f90540200741d0b0746008082c42c2e4000a2002d4804d01010804450022100d4201e00a41039140032119042004000180052000070380090050b10400c0c81c080503414003501c01d40001030100074490311550301a038030000070710500b0f80504003030804070b0840ca048050390702845003034041d00040c4150590240c052262801854261aa102408000245400c1c0e40a840b64000e900103070700600c1200b00c5000c40c28461402082207504440003941000c164400740509000303000301d800d00c400c1d50740c26180c010800800610141c08030402040180c90f18003400101502951008074504000703002840d00180ca48240d03503a40590000d0280340c0780e80701c01004034200750102e00903888901c80440c0341d41c8182110307d45440030725070013009580c165583d241408299140d00d41da600c14603100d080001e814441d03075002154407000d4141564a0710b04582110720604421200000900454404005c030700c2d40c06200d0034440c825410321164854400c1da030351070b903981c910000090a43e160107590688000703041c180 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 470442491 1250 470441241 470441249
    0xd0327140933091e07050f120a0b0621010527040609050a0302150124030c11011107023a0201030219020d2019050c04021c0b040b0f040b0a 61
    0x1100420341818240f41d6102a01140c41807440b88440002c612950b00803411190080c2091f8021400c00742a010351000034000101134a00300380e00c0d007100201075900c2030300800c0c06091040c14600d010000f034100134040541600418000e440100d00c2503c1c1920b000c1c81e420440300c104d004600c03503549900e00203015100302a80204075105040c1203404260b00440c0101400380c0d01c8020024aa982e0980c041e042c1507560f0b50041c0381700040c09404041440b9800810400350141410703054158402001801c441290035060f07142500801e05500314904100e049031074069050000f004500081901c5103400001c0e072010400c5082c5602040440e4003e8054400e0f0007642c8402e4907081c0c03901c2074069180c2c6405e40c2480005011804070350182c02c2007485801c80d02010400528184901035203030038005802090913112480349154010196656000500d40b2903c0c00e40103c1d84104000800810b42d0303001c1d80700d5841a030400205c0800c50f203503900c01040d6240100d8010841003607010201d8104000c90700 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 470443741 1250 470442491 470442499
    0x2030c040f030b01091803050403110102070e070f090b09060306060a0c020a03060507180e071202120108071703090303030708040807050f0610120f020d0327140933 72
    0x41d00209100100e4100350403140c02d50f205116405511030400011040300000401080d0305100c240040b03141d0500740c40d42500103004480203036403070f55030f01c403200700040b504980015208120b400d403555001601000500030071440a06000460000035278900004041c54000c038004554050000c0c41a1039620321a5006405004082e0301c03810414054881141e250000c0307020580781c1b038208400c0009400894138540410060b45d240c504007141d05104c0c01703c59403900b036028803c00c3c510075107044405008100230700040c9000c92a1009101d515400402d00503083c0d042401005100d85010048035803003d10361410400d80e540b00c1ca401c40b403074016000080e00602c07030070403c092000c0700080d04d9802404084c02c981d80c41c03a0b80b0b4128110341e6035441030050940e80d003080d00c003005007812000c00c01c0e03551103824000400602581d80000c055400c0341c8070039080c80b100c0d100700124101c5843c0465001425143c00c03005140c93340c0d620f1926044044405c11030740f01000c40c0340220350459060025104010 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 470444991 1250 470443741 470443769
    0x9090a0203060d12050706060b1806030601030207050304090603050d020f0d0507022701030213020c070905061f02060f070f05092b080408060a0c0f030c030605060f07051b06070602030c04 82
    0x264000c3c2079070004101107c1b11460203c000c10200740c07140c191f4060760121a8204103099100d401d00c0420b400151903541415006d0100f9800136034103202900c0038042550f0001001032850400c0e91601040481103400e64000c02013040407001c0c041ba6500c2079078900e0400c15900c1005101041e05074102c002d02d070480c0a4144500711201741100852412203008075288111040d441d0350800403403044010100b01c1e641b20101c104141c80d510b4000782d1780b0800c002c18400c07038444500201d5800103103503c5644016000041040040010080d006402050519050840c0510301c3e0010700640300307111840b88165015200c001074001c0f01e4203280000048030701c000f140980b091400300b001d03030003500503058680103a50024030340714002d101e034006041040d078403481c0c0360038002c070150020020019100101515004081060b85562004040c08500908410b96800301400c0041c00c0058100704100341c40b06007000c2c083c46a8504096692154210100594944405085000038441c2c0c1c0c1c40f02c02800700c18 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 470446241 1250 470444991 470445023
    0x609060406111e100510050303040302010c1403070c1d01140d1b060203040311240c12120402030c090c0f0d14180d0c0807080309011e0f0b030309090a0203060d 70
    0xc206200481c1c03030402c05110706d4035540142464a0041e01440f501640306020400241d07100d8041c1d091010300940308110a241520380300d0703095038400b80056506000d16407040000303202e412081c6610424840b8681e0145d410481c82d1290200c00030b8002e481008144445c1c0244403902e8601d618007006681384c0560306c0d80da0140070351207030040d00c03050310210308094000c1900c0c10503d0040d80c024549058000d00001d48200110045d045002c0f40384641c800c0d540221140c0d5032003002408410300b441c403007076085d01d01841090f02d81103c50622502800400b0103001451103040203803070b1400b0380002a00d490b120f0584e0b03450010b0030301e940c003e0b03510b0043c03034103100c01c0c45a0144650350f1007560609803504041d1140701035428072800c900061500c2c8003048964085408100a5500700310b4a0707002085000d09000111300508000340a9110685d680100803000304180c4640c92006105501650401c2558030006400030310080020703180c0c5070000b000408580d81c0d0030b01c900c1107907844101e0001e1f501c51 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 470447491 1250 470446241 470446243
    0x30f09060e1002071218031406010f080c15090315040f0204060812180103060302090f09010b3c06040f03050601050d0f020409020301060b0d09110609060406111e 71
    0x860541945540226000d0b80410301e80c43c003c0754026034022007411461001c481c401c0310107100829100c00081c00f0f40f280480001d87c0000e881000e43e007114010400e03075042558040041100d507000c0b0690303a002c034a5020054840002e1440084105a01c05403905a80c04c0032030304100101c03003a0105003070b0101c00c0008001c0004100c03205180262002c22019407a0703641305660300c40b80c3d4100420984103021800b51a070340701a100100304130616000c1361042d82c030750108203c107000b0360302003000c207118400308040e0a109120f40d94084000b180c0345072440011030300f40e0800b04800382c218900c0512444824415a0780000c40e0700d42d5020240688c0d0b50b440c2e0351640c1c142c0140c4c803800103c82c0f41c042c5000000300c42c6007584040443c0c81d0003a4954113014002d500304030041420f09002c90300340d500c1d00c03000600c483c01036010385985264408081500d4075645440302c50842c80c032241521070b900500c04d13000b490311007805840a031596420008141c80d040c0004c01d2609820082000e84d98402d84000c03904000 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 470448741 1250 470447491 470447501
    0x3091104020c03070515060913061b02061504060f0302120703080a0c0b06090103030531080106050306091b19090507110610182a08041b0506040306020a030f0906 71
    0x20041094410014052440380ca1b1a00f040e104542d00c032104c500881c0c0760102001c2d078041002d207e0300d000604a03112801c1074900c035000d900c0c3c00016801601c10480003010300d500104442c1070403a002c002160030310000300c0381080d0600010340075a9035020400d548070700800c8804003071a0014801d5403034800707855008100c0b040c0040100c400610080125005042c424280ca050b0b980c140c40c0c80e4100341794241c240d0007401c0d00344035074629052080c42c002c0e03c2c65420181c58026002044c004070307599040c9424107192a82c0544011080d03880108200400904031800d06120141200c00c41425106002c3c42920042188c1026003c01e2801301441006500818485522200f0b031003900c016503100303850070b228151503200d08065000c1d4805410400016079012103440b1428003102c174468400e0205801c083c20000f03417000d0201d0032103000d11080c0070780141c08402c010480300180c43c08074104004502d4074096440000e0642c3c1c4c000c075101042d640250002d6054140030402040481032508012002e48 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 470449991 1250 470448741 470448743
    0x10303082a302802090306040201030b040f1b11070819020112290d0b040213110c010608060c0423060912010603021e03060411030a08070b090105060105091003091104020c0307 77
    0x42d4141c00a0810f9008038000d80f8010080140074224540d51900107602414003050425070055603038100d002c22810b544651540c4e41032418000d20b1000c503079038014109c200c074031807110070580c05200100819500010500c0c01ea40c2c0070740b5218607402c0d4a01c011381d034a400c86045001001d0905440150650045006800071040002c80d8409140202e060040605100101a1200210500050240c106036011014030101e5500009101d43e901005080c90381000d0401d5030165110f41080162010402c207054000c1445078940d46030602c5d055007426188102c680c111811100708030840c0c03035a40c4100c2a9060b0f11000b0b8403030344010007000b0841d070007003145002c2280719107000001030010324240d00c0343d01e1020101400070800c7e5256511004580c040c151031444d81032241c1c4e1010b00019801d00c000d000c18621030f290807070351400c0204005007510b6000b03040604000042c0011210743e900d0304012001c50600d42000681c80703942d41060011015440400e541181c00000c3c400201c66001002300042 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 470451241 1250 470449991 470450041
    0x22106091606090b03040f02121b130c051918090e060a15180b04020c060f060315010905060f0604060c03020111030408030f07110105010303082a30 65
    0x580b1020159440791140c0681440c11000b4800100002c0003913440c82d6290740024040c4800c2c1103811803181c540743d06200c2c07006814000410843c0d0300c0c01e00d0300d03030740b24000c4028406101c500cd0b0084020454060746107525070040d040e4140d526a2801140c00046c50b280d03000400c00304c0b03519103101602401d03c1c00404a02c91143d240000c07261107c9116a984620500350300f042094641040603820a602a1103201890340d50349460784240d6440c8000c0c028864140050189403400b0b007240440c0c0e000c001c041e14065048200e111000404000322141900d01d2280002600c0e00c5580c0454411001d4041c0c035900440300090115095400402170801c5034420b500a024503082014400e02d680000d5400904514050003c5201c2600c1c02071450380c0031119140c23824a80310420203090942d0000e0344148c1c04511350400f1700420700c2900b000c001414000d00140c0419401c04000011a44030300d1884a142d00c40c002d0914498403810074030004100016090030020b03040c41e0402042c500d903440e03030250207 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 470452491 1250 470451241 470451283
    0x2130b0d03210e10020d2c0d1d040e161e0b04031e0203030d020f090405010602010c0903060b01020a150c020616021f1404030804110d0c0302210609 65
    0x1010b140102e0714400c10b004044d02c50300c00c400706103c1c040d401006580440d00e84464a07030b580510460fa1300000400b0000c564081e03000d18041060814102c201e00004104d81c190a03100d44c0d03100c1c0442540340110a441c0058414503040c44c550421201040d201120404000b0006030945203546020850110400740b0089035541c40008080f07103c0e91100601003601d0081da2042e0811010b02e4940b0310740040d05991070501d401601d8000ca0b413141c9103010b002003010a02d20180d003003c0c0308090143c140d0f070008200404e080e0802905001e003d01c002400c6a844005210442c2d20034002031840355407050401026054045c000005083c590f16084014441d600006411310106a18050301340d00740d801424840011841c0b030843e8205814103211441d03218241000b1404804602a208074002d5481c00706500307040c03909401101d0b0000c40d05105200c0d14244802007a0310520b404112603044549921415003420030079614028a0390341c8251b8086c4504000080e10049080307151041380328099a4 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 470453741 1250 470452491 470452547
    0x71101150303020a06050901150b0414040507081f1e03060e0c06070308070203041d0901110c030a112506020705010203130b07060902101d030607080402130b0d03 71
    0x88444101c0c480600107a21070070490020444035402580c20281ca0000810000c511402c140300000c90f50f48060484000003c0801145074100364950154600b180c3c140300d1400c0c0100c000b007165102030f1012002140301c589164040308a60340c000300074040b0a40d42151a48030349001c00c003203800d902c01900c116003019070002d200c180208026144000051180d8103100d4191412134403d10018624800d603c000c00000c2016840d011500c030301c039000f41c015440207107800c0c0c101b035003503e1000d0800c2d900030000b0310480b510760303c02000ba14500403907403a200307041840c5c24006600d0408650748078092007801c954071781074041c0001074080507580e5640813200c0d101e6407403004a0b503a00c100200c0469400a0500c28004d101580c8028007100c0d000c4c036800b04401c4201d8000070030a541411040002c40c01c003840455103640b0030000c20b91a1a0220060116854100c1000d030800c000100024803030000f0200f889180e1907c9d030301ca100c9042d005401142110784502d4094075804100c10300e59821190b88002c20 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 470454991 1250 470453741 470453771
    0x50c04090b0d172505060c0307111203041b0302010f1103040509100f0605131a0903060703020912031305010f140a050912031303080307170c070201030e161208070803071101 76
    0x440f185d03004004042d0755860a581c14519000604880b00300b01001c4408481c2d0070041040d203e18021b40200c0319034908103403800228000742003d0641c0c020000d09010000f60707812013a00000d0581a0504001480007403a866040d031103141c0186500074060700c24010552201580241074a541034a903404a030348a2006a400b070280b11100300c140441c4407424070454840c202008400006148850708111807500064203003c41143c1e2080000d6021400001f20f151203a0100d2a8103180c202441c03a1000c01c030341c01c030f00d0003100b400307401d040c030001741000e03090a4803500600a004520702c0d00b85851794024100109140e0040e40020b120700b40211451039a0750021003100c0031003414036183c103a010714540e64240260002020981131068090f1075000c00c100c6400020320400401041c9681d80c00144005030499000c6880c401c5580d019105442400407a40000e80c10789034002e202855540d62854101c1c00341c81113420007007517a60080148441141c0000111054440c004004e0252950401c4a2 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 470456241 1250 470454991 470455057
    0xc0c0307200607170904020423100c0f080a020f0a060501030303050705030f13031e0903020a08010203010e070c0203010f090b04170c12090a1d0403080901050c04090b0d17 75
    0x307407424105644000400c0b0704d25008128201000d8009401d041c0e50302c141c03580d1844030781800c100403010680340112916040c0ba0110541c0903600701750055000c20307115820300580c548001808501d0004000313004a000700200b42400d54a4421920703400034903d07000d4040e100c02c0c801240441d00307003004502d42d1070148d019a44540048800040c0a40d14807881a4111440e984250207114140060b102a000e00002e01c4030031030011344402030110315601c18011802c8255210f205641d00c1400103210300c07001102501c1d0850528a007200b80254076000080c014402e800000d0f00c101c0c5060861420400d901b00700c644905e008000000483d1001403e8080c2803003241920040d94000407807046100c40082d001c3d1801c40d03000f4200b1041903890715131042c3c041b070380c0750703500321010100c041000200755110030300c194032030040d04c02842070b801c00b840864803e0096009007000d81e516070300e45000d00e40300d041c03c2e02c00150308800d0b03021900a840c030920700c20354080703d411100280120626890300100e0701c40 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 470457491 1250 470456241 470456243
    0x70f0314010605160f0816142415090103060c080a060e19060f080105090f16030212010e1005070e040b1503060d0602221e0902030c0c0307200607 64
    0x90031385045802d8000140280e0150804c4800c9282007043c1e00c0460400c00251600c0d010904121814058600b08440e141080580c0000e156020324103001d08502080311060b6808042e01030340c1110340715203282e031020308000d040454000070444000402d018080d0071200d0900300e1511600c0c82911003c55030419901d1030b015419050f0b9030540401c1d00c05030300162080d46615a100005505500c034003100d41095481e901a005580d181c0060040081d000d03c00b141c0c040286000510420107000444840345e41c1a204c00391060482c400d400880c10070170b41101e90510410360aa548003138825071548020042900e40c0c00c00282e0a02d6454024203252080911b103e0b00103200103a0700c82c0a00c000032480e4401003041790411120b5001200103500f82c0094000781159a400c514400340c07902a80d403507401164082034000b201c21200859070901c1c1450903064030f00b1101c000d40c1d20341d07400b420703d10144942e501c4410f19100000b0180b050100034113141d4801c0300c034030b00f408074a0040041044068011114 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 470458741 1250 470457491 470457497
    0x10c0f030815040908030402012007061b05031b0601170303061c020a03080915070b0604050c13030308090d02030909150d15050603010f0e0c04180b070f03140106 71
    0x182500400d0103403512551042d1000200740801075501c0c04507094840c0722108562404000c400e100440d0381110403801c0c600b0003410504030041003802d034699285507520914050241c0e6038000ea01a075030b800d28644d002da4220044076030344c012518050100040304d082070070460090400201c0c09103520300300103881034182c05c011802d43d10b40c01c0c10800310304880c030301c07070030b0119554030001c1300585526030305000840c003e012070fa449070101001d01500c200f00c0c00302039207121003c0280c10000f51032441b5054108000752000185aa10784d10521300c070780301d9200c2d034000c2c2400500e000020941c1c44412140304201c41c0c815200401c2c10300750300b640d4038082c080c01c40d54003005000000320100c1d180f04a082c640100140791001499164403621413496100ca8113000d499200d1082203a141024040c1d07980100c7d02240801c0001d070440100c80d00ea054510400784503035240c004120040140100340504103030031015142650605100240040c46800d006c000402c1c1440318070603001585040d0503040b21201c0d1 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 470459991 1250 470458741 470458763
    0x50f010608030c25150801060801051f0302030411040515010e0405010807290d0c26060105160602211e010302010507030210090c1a0f0409270605040b06010c 69
    0x425004d140843e025440d81d04400392100014002108a03c560b141c2151500c41c0f04903075040c41001421403c0c160072480c058549180b80900310200c40e804003000f0486031031f00507100d4440d850100245a01f40b000d05910504003810700c030710b004100640390042142600d5580d0314445003400d21007620800d229007200740d0055802082001e038202c88010408041a9025014680c2a608424a034000342e441200c0b8558403006100b1142d0411054002c004e41008584034080d1050401080400000c124604000c0c0102d202641d034401407241e500d1255002105645030f0f2140d241c8048690000103030000600040790109208400a1091112a08808665000b140c1c00c6400540d43ea5004020490443c8034420304203880f03054500c500d90103140b00d4000c1d01e1201e460214410412b0b0484080c00304070100420050300f804c036218044030104c0b118600c011801090340c1e140c41840c3c1c0da600a841440c0260803e1000c10805c0700e5126a1203148907108101d4292280702c0111105aa558401480d140b403039 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 470461241 1250 470459991 470460013
    0xb0a21051006090f05280305071d04050606060d0f020c10050112030c020d02060405030105090a0c08010e0a06090c050603130605010909030e0139050c01030b0d0602070804050d050f010608030c 84
    0x200210100e41c03211400340d186c900380c1c0c012818070240c0c0785e00c03d03a0303690010442400b58504014400980290806201e0b805082a407622603c4540240c0703003511682c4006491a00351400340c00190941001074070454682c4010b0607850703150f181040d1000c446034502400032400742140084043c407190103554581001c0c0040d82880540b0301c41c1c05099034050dc3c00e010001c5ca42d6070901819101d070720203a0180881099501c0d0080340000c0d0707070700301d800281d0428400c410038000002c0e403410466000718010500f4050b90a00c01c10b20800e941065410800000410901884400041e64420310900c0108060b0f81e82d04e95040c203c680005000f400583c150050358119072184c52643c2c401c0803501b664001c4050200d51004c40d2429200ca003083c40000c0c18440f00138040280404a0002c0c000c0c20b0902002d500c60f400a21f40801014008003029404034080c1c0902100c182031b03c0203000c0c040c20419800c41c0906000380e5409980381d031400300c3d6080c20f001084860020007034803190200140100080400 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 470462491 1250 470461241 470461249
    0xd0e09070504060210181e050606040c02151b030106050310051e0112060b041e080f070614090907030204290d0e0102070206030a05070818070b0a21051006090f05 71
    0x4014008140c6c1080814200085004244400983d601c00d41004080114a240181c00c142009000701e110318a4010404981a004aa0586d444500729001e18650780c400401d00c12220340c400e1030300948031001c000880e007560030030010340c09404c0e042182c4101981c0d5000b080000c10240714411144e404c11484000e0b59401038207040158003582e000860700d2610340040d21029000390340302c0306030b04815000068030001950348480103400b400703000d0b11914000002095403052244111010050103140c070301c0d0f0301002d05003610a00d403c010b10100392400c101400801a400500030141126420041d45001b09241680100125201100c49041040c1150001c00524011864080c2950204440801659200d0085120304110344001803a07090049009041c0000100345040680c01421343c0c840c04440055118211a01c03148000da540804c90000c4a0b50a00300780c0780c0c542a0400e68540001c010242c1145224a04600c1108085540c071003084401240900c1441d1031022011320601c01c40c10 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 470463741 1250 470462491 470462501
    0x15010b0d0c1b05030a0e090108030a2015040308150a0902130b0f040e1810021e070605040302011a0f04020a02011d0a050c041a0904140d0e09070504060210 68
    0x850902c01c1c070500908a026084000080c02192940c000250901503943c1104645c0001303602039480d052150b040c10130042d038038483c501c2d142c400d1000500d10300d011000c00d0001ca0701d4010760076040e41c4055440303442090310344900381c4044010816031000aa00d842244210309039010b80144246280b52502c2d0f0b141000354400a413a000e0b006641801042c1c00080340010903100184131078142e40c2c2c3e4a849400750030064080d01e2900c0b164400140c0e02010100000c0e20104801c00301001660f0320125110110040c120310b0380101095004220003040c0726550748900c1c8164041d8000780f180b0b0a0490011807001019200d00d03600c402d1080418105081c40d170f0103010058440c1c00000b0303001d00c40300e001000c0070130740d07000c03028076948101107000801c0020301c0107540c44401981d01340300c08041c903034090782c0510514000a00403582000094148004440c07005d034a1040d40003a40d0b902c01d00007000401950003000c000d070060500030046000d692256084608450407540907008822003071620501070a = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 470464991 1250 470463741 470463761
    0x18051b07020315042123030108030304080906090a06020102070302010e0c0a0b0c01060515070501140402060f073e0306040b0c0a11031201080105072a150203040f030215010b0d 77
    0x60207546400d4400c510340301780c0b080340c011a031030300c80145070000c07070203a20710700c07030880e0301c1c03545d04090004008c646000800d6a0304250b00050098484418901182030307400754520b001c3d403122441000040702e540647c01041240d0003a402070100ca940c07980d04075911042d442e450750b00001054410000300d1100c0026000540c020400854890b80d83c1d0700144014070707000560081d2000015411040120034402c0320224180d030320007103a06283c03a070001031960003010520404a507000410004002c0c040a9100e482c0300f0540d0518084803440003007400200044c2c0c0d034003201ba00324002c402c0d4945400107140d0b100b690b120b2140a03150752041d4503070303620750440c0444070f0a00009482e032018152050020b0140054048035450040d03140826103030a5960103001c4400707010100070f0310002c9906000c2c0403003800380f96803100c0c40848207615220086060a0b124282e83d14030101c2072208104e8441c0380301003154000ea00b100c068015680410b04141400e10541d9100070041141200541c0c5681042d4459 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 470466241 1250 470464991 470465003
    0x1050411090307060509130614100c1209050312070f030c050a08030f0f4006150f06020d05090906060409140f01060f020307020f0a18051b0702031504 66
    0x80081c03804a450a4400e030030940200da40401c054030f4500b045084403003400150201480500c0c07920313811601c000ea00c032034114010f5004200618699000c0c0800810a99102d41000078004080200610803108c0380181d84c4030740283e4402d809003902c0c2405441d01d058000540c0381c950750150303500341c6101234490012501030050600074004035502101462040c640c80c10900c00710b01c1c1c070501d2010245030040c01d02c0b651680b4901d24940183c0310b184540050803c10008540e0307c452000c0d0340e4030a4500b818001c2580d801d02440c200500f070303085081000c545683d498480002d464407001e82e121900348140340c00003507003441a0055850007820381a0000d030b004d400c0610301510303001c1210591348603404000007121107905202030b0301086840300d8010000b510303042c00c040c01c100c50025141e02c1440c001a200301d9922038040a0769a039051258001c2c076044040c2100858400780349409482e08541020781c4200c40b01030414000c2ca00411038125036401000351090443d0031859814084000d48150340c0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 470467491 1250 470466241 470466247
    0x60b07030516021813050c041a04090602040f090e0105090309090c0a0e0909011a010e060f13120b0a0b1c0605041b0f03050f0715120b190e0a05010b0301050411 70
    0x140c1c081c084c0d12602451405140d2071402c00c0a0074210b00d402ca000c07a032503002e1450001000b2844191034001c3c00d5600c01103170080f9007003d00381000d60290060b5001030200300304d070303800000d000d0540340e0110032802c00950092040b44e0f9040c651075100e00074000c1d0076401201010004518201407402041c2c00506410000c00b29034039030b400b0030070300001121141c500342c0d5100c0d41d04200c1500d114904004581c00d00ccc0807080300e0b500c03601281e01801046c80031008540003242030882900c15070501d401504203036140c010031741320340e09091700c0590041d80d100d00610320b0b2002d02c00c014101001e150b8600d480c0070400801c1001a683c9660041c40014019140001144101100d0200074001180104a00540010400d00b10f013000c03414002d00043c0c10041d07520103142040540f01080c40d8144011036800c010076100800c45800001c4d2032046080c541c0a40d081240d01c602c295184c2d80c5606030b5030f001841d250982d072484100b030102d484c203014060300c020307080c00108968502604440c4541c0b102e8080642 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 470468741 1250 470467491 470467519
    0x504030c030b01091a1f030e0f0105191a090604020d0e07050a08010911090907030f12111f0c03060b040b030619030b0408072306040303060b0703051602 67
    0x21500586030012555034070b40c9001081520305038040d0042c10741c90740c400b141d1145100710000d1070311051021607404041c40e910410308240d00a0740811400b01c8904266400c0400fa40701e02c1c1d008000842c0c518400034444c0000509000c6030f0b04c00c4540320504d030302001000c02010000c003d080400103080644c0140c00300440107803da8075000e0740c804000184000e180c1c00d41468204110596141c0240c10035038984401800807451081c003003201d0355000e6a1000644d11b0344125641020103d4002800026030990800d081050150040000c04c14654600110525030f8200d281c840c402a00f881406061020461081030659031100c0200119820b001170801e07903031144100c0c81e03003066120b250031040210802c001802c00000d1140f80040848001d00c115056031788142c140e00c405000a040d03074402291000c20004000001502041644140b030032801c607000406a403501e08680841c00641415400221914032000351aa003d5040e161039091501c0c1071004003400f4040f407402e90b0b11480c0030841c48 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 470469991 1250 470468741 470468753
    0x6020d120f0216030905010201180c090e070b0a0509090105010c03021c020316060603021302040317030615070b04050f030a0504050f1804051b030a0803010603090303090501060f0e010b0412080a050403 88
    0x2d03004074131988414008605c0c0c44000381c21960b800c00031420340c9500c02d807000005000c0308408000d560055100203064022000c3d180e00e0550182c0107250724900c0010000d22007908803020304000d420440d89480181e0b00c84c1c0045603a0039552200802603400815042c00c4007003030224084142c411441140c1c24451034040050b8185040c400540d03416903101c03018029803d000945442d646140c510640ca0301e8074542e18121fa030080c040059081c0c54021010500681d00c442c3c443c1001d01115026075100c203604c0c101021868000d46044506100d4032110307a000410120030b50754240c0254a0300c03130500f403802090181d03068025000580c011a030750055540c810403c141140035a000c3d0000308412a110b4013940051407400a00314031940c4036180150004024108407130543c0c906203804100050103160640184c892f05400400c60350070a000451155080b10601040702e00784240380c10543d81e290140140b9108a000d0080201261005540403170a44001410b05c00b0052500c24603042d0b99840741 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 470471241 1250 470469991 470470027
    0x1e080d0806370e0a0216030f02030d091208070c051018060504062909040809010509030609060919020901031e0b0106120b0108090c04051f0e0402010906020d120f02 72
    0x1581c8082d0b044000f8007400702040f40c060340c0100c6031001180342481d04480452001d80f4120000c0400c8540c80c09020420710030700546009040140d010701c440300540c6040c80c60303c10040002d41c00038240400107040070b440350003885e0080390080003070031203080c3e00e011b080003604110300ba40d6411301a80c000c1400180e0b46209a0b071190f8090b2a000401140861814955294001ca00003a280917802400c40581d105100140c00c0340e441105140c1d0741d11a00010b840724050548050f6140c082c034010045a0f442c0400c15a106c0c221050907101071072200301f6a070480c1302c0040301c0603402900c290300500021716403407214420340c81d021510a110071a540c0d940c82040d0000d81289002038407100c6001c075036000c0c07800b800c100b0070001d0800ca003441c5072410030169503032081e145032486507451f400495103400c0c0d81d01c00b90030040000b2400f001010b1301d50752134960040065074104c0c0028541c02c000071f021840440c40c03001e48540ca540c0d200e0301c01500744180001d4004044003409541d802c0284c0300b0100807407210 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 470472491 1250 470471241 470471329
    0xf0a0219170d12051b0c150903180108011505130909030f09060c05120702122e050103150b060d020d05010f050904030f03020309190f15050106140f131e080d0806 71
    0x10b40c1d8404a4090249160308012082814894cc00c001400741c0201c0c68500b007034000481c03500d251122040100c19098060700e0b40564001d034130f0109450103140c1d05c03400707203c40c001c05504da62030a60f60782c0d02c1c01c8550010080d4083d0a68000d13000b20380d52260341e50000c1600328001010101010494401541000011034000c0d403401004404260301c0303060040301103200302000d6001c000729895625a01d200d252808903911085581d0711844a09641e601c066540d0810341240071034590407411000b200808003801076852069202c84001034901d480c01100d403146a142da908000304681d0740d020f402070740015100801c00d000d468132402010280750f9200400c0c9001d211049054400f0b81003c0541c03000d0a128071006a0800005024071a0021885181c0400c0c2c0135100d9551808074001403510301031403d8180400c01340110004002001400d00400c0c1000d40e41d255100c1541d1301d0703129030307185910b400d03034000f01e4940000035200385400c0008910346807001c064000e0014004d00303115104684510 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 470473741 1250 470472491 470472493
    0x2031002040e0a27030c0512030711070f0605070308040804052706030105011421100b120f1009020f0406030302010f0b030f0a0219170d12051b0c1509 66
    0x820111292500954803c13011901c240303810264076108502004070b1080c005024441e40c5030002007000410003030802c044085080040d01c9041c1481c00a24147c08800d0300f0a40f031007190f201040c2c034207960031210100c07005074440502e0701d80d482c2d900782c1e5100c0000b041510340d21428040040e00340c480803580034a8204c41012280e907000d5070b041c0e07a040c0c40d0300540030710300076894907005000d06072000c130301105901c0d0200e48101d03001c070100003000c4034007822200c5600d19001d1440c0b180112640707a040748844002c202c030034040080c0c403204005c0e03071012208005c0d80140e02030b09a00c0c10310540c3e079100c044020b0000d01240ca140c3c1760007011909640d100ea00c202c005030754032080303420201090300c00d6010305507084028154503203468840c0f075503801c0344610203803054850340d070305201000030456403030700030004c0c80c0c0d400582e80c0300807031005c0d201c1300c20010010204446a16140b41a04c1c5841f8040c400c2200359162020701d10425003096882e080744100c80324500c40c400d00000e518078044401c51088210380 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 470474991 1250 470473741 470473769
    0xa2007050309041d0c1507020432160819020a0815030102090901050f0301090203060403050a09150206070e0613180c03050705160f020d060c081b160203100204 70
    0x80c2800304451381441e0000302c0348900c503198010407601192984e02c01200301c4201c0c005210f2120181ca56108048000754003925040340503000c10f24400e9062803140d2109a02a160150484c0c8106201c03405c480f14034400a000584101440c0142003040d0410b0464180d4000203d440c1141d10480e40668014000b14400303d041012a00f0070141d440540311050b0001e40c14052104003282d0722400601859102d010450b0509132aa1000d50014588a40040403911030b4109820050f2040d84603040b400002010284c005c900b80080c80e4034401040c074036600503c1c03240d075880701c11240007950020460b8400c104014103004264800d41d440c024040080c8929a0803074045004411215030f140e001050504107000c00041b540c01ca03055910300006101504c1402c100c514001342c8031002c400c002540f010341d0208017018041c040c0c0c0329810280540c1c035003071959250010410300300e421500b40c44508002c2040399002c205031888040c1a554030142c02c55651161100c2c0c01c0e0240d800541045481965407 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 470476241 1250 470474991 470475007
    0x702031c1e0509090702160b180d0c090c0302040f03020f0d05100b03010e010b010212130f090b0f04050903091302160609021e01051204111f02010c0203120a20070503 73
    0x418031280c103d1090b0008010300010f846600310081030072300c0b84208000c2e0100708151400344031700d48034482e40c000038407040031000c003480c04218001c01d0b030081076040c91501e00c0c543c68a1b4040d200311001c1d901c01c82080400c00e0301d543d08020007588143d0215800c00c10003008680012403c00c000400d50403070340d90124a010f610030602d403c40303030402c0d218009a0704140450650340d03004900c0e40c2616010000071966000c01100d9120b83c940d65601c041a0320358034150001f210f00342d55201d103120315011102c9281b02c0c20b103101040292002a01c1c0203880e03400811101405180c0020700c5010f1000f004800348c20080c0c8198524103c464000c0182c41d5103450f0500c460840ca080c3c211001318610b800108101c601c00880000e040d4007904800032401c4807000d02050134440da030441060810f03401802c2c000c0c100056420b1984003881100481d002d9800c5c020f82d101340e070b400441540e0981003101460f03041c03581c40783d0090000e041016402550300610205c00002002850010000140610019a80c031400 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 470477491 1250 470476241 470476249
    0x30910030605011202250206040f0609050a080606102106030c0e0c12061905030a061406010903080d05060f0307060507050c010806031b13090b0a110702031c1e0509 72
    0x182030120404980304000383c11203000020126040c2040e00c000c403100c2c21b0401d1010800f20701c5550001706401a402c280040c50950221420702982d40c107036015080c40381e440603050713035903041510841c3d4840402d0480880151017003548001541100b650302c0124030214045800701d50343ca400680e504c4180b5030080c0001021401c039a0b4004250220961a00c0c0505044400c403440142009124510b50140d42016089640c19800540401000e458580c4580c0c0f505c8030041100d0f150401d203103a28000024201d40c0248081400c581d00000e4031450130318002601002080018521980005440c074040c00c141c070701b004164003826507520342170380c1c03100b060410700d10b0704512000d00f6041118040030014140c078089000c4a0000200300b0b003265080010700004d0855005503040350000b0710784180142801804c1650b00d00421500404100008400840c0003803403103100740c01b0f901030380916095640c0701c03007050f444444460301e85090070156240c0d400706810b07820b186019100040d404202e42e007203407038 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 470478741 1250 470477491 470477507
    0x1031a10020c1e010819110c0a1208060f04150f08100609090305070326070903170301030b040f052b021b22061e06020d110a02040504020303091003060501 68
    0x160790709002c903114a42e03c0c002482c0c014000d040755203280d240c800b4090090b0140d000000301858882d1040e48585440e1000350342d4490b910826113030810a641c080740741034014504a4060500500401c182010040a01c000340004610901451442800c0006ca02d180005482c0c0170b40001130107080f800d8190080502034811035002159200d140c0065400003e0300701c402c0325100792389410300000d04d4401d03040810f1a20380030a040088080c41e1f00030401c4c3c0759807081030706050740c1c410081c040e844101113401c03203494002400010315040d440301c040390104003171505111505200d4801c80350400361041c84600c1c030780904c1d19010180f8401308580603096070144600501045000200000c5d9800307013000800f448541c84118041b51030100c8a0700040e643e54100c030010702103d528800031800c03881c14110425800f48111001801103c6425038030a1103042c07e000800c004500400982c10540c007008001c000c040d10880e4184004c01140000d512030f442d0106405000b41c90005100d032407c0000b62480d0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 470479991 1250 470478741 470478769
    0xa03111302090108040311030d0908130e0f011202030f0102271f05090415080715080705250204140615070302060a05040305070b0a05060f0105070b0601031a10020c 72
    0x280148070a80b000d9a218103a642d000350180f401400b1040c0352031400741548209403a07404010300b040158030078411024010180708080c4c0484415059641c66801656a4140d5041550b594a00010002e500228590042d042e00090644100403c080c1c411400ca900c1001c0355141200450303961a070f0202c5005001c4803070b21064645d0b80200c0185081e01492180c001100c1303080c07107000304902c120754a4a1380400e0b000440c0421091080361164041640c03041c891207070300e02ca80049981186000e11814944d4020115a01c5960400003450301ba2a100b03490800300201855034500e050016984600031400c0581c0bc44002032840d0a01b90140051400140b0308508428010401000005e60026550794403110401c00000d20351210b16048855229019002d044e0f80001410310110038000d07400b00f8000c40c4111003d940c0e8184c07400c0103513000d004e28403010340560034810000300f095020b508162941d0800303501d81d081102c1600b00007008094070f03804035401684032121400d001d0906c010700c45101 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 470481241 1250 470479991 470480029
    0x6090d08060f0114041d0901050604060807090507020c04060b130b0a0c020d0602070501050705030a061d01090c030605030d050901021006081c020a0b01170606090103150e0a020a0311 80
    0x907180900108540c1c0003815010740c10814050400d140150942d13003620701402c400c06101024584e424a140d042c0c520903181d800040d4681800315034a0700e040d100e641c2c11101c00030003500c0e51310314244000d801400300600d61800c3d8001c500e0032005581da10310610000c3c05a00d800b0a490b041110442004c0d901c65820020000c2c034100000f00d60075421401440d6100d0b81115104001032a610300500a40142e03080204030398204000d119009801101451060309044004c001039a614200e000015494103542c484504215005110202c000e42114913014424180421171580d80c02c04a0300d44000c0c2030003000081c2010400d41003960781404501c45514200720309010546c100b1040c16250700301c02d11103107039920016042030301460080c04044e0b20180c200391440c02c3c42d17944400c0c8000e6920b0060b914480750181800003816441c22031400750580e50060132100a5820500c90b01006080c4c034100d50a851281010502c010703034850000c04051446804a4640000c00100b88403007411310040d01200 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 470482491 1250 470481241 470481257
    0xf0c0d0c030f0201060e0a090c0308070c080f03030105101209050a08031909020f010507051513031b050a020f030a02031209011119110d061b0809031e0901020304080304060206090d 79
    0x8546c00406450b90080b60b0400006880d49003132900d0003000e00ea0341d000410b90400030402c2c209100c02c1c00c0b802d004440b141801c0e42c0883c22443c00032601c1e0f200034054943e0190301030501c0d103c4e1a115400d1030300c02c100f103180009018030035a1945890070f01142c008440c0c0b03400010803c026103492410340d030010b01c0584414499607000340c0c0040c01700e101c1044107a04100001c620700c01408420401111143c0912066228034100707140140c141340110307003060f40410b0b003c1c2ca1104150081f8100d00c0c0005400c4000340c03048800c0c40d800c0068205511140b641d040c400d2540c0e503800341e501886140c0f030141f411902203a54850000001d010078074041c00440c890740100c82ca9009000740c1c044c003031201d260700c0b0b60100050740034000000c00b1a103c507807018051902c3c3c00d54409002c101410050440c04954403803010681d68001015600e01ca501000c520000750000300b0011200950050301803480c05005480c10300342c544d28014a540c22580c07100005920640601c00140000c0c06280c40000081c50a820 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 470483741 1250 470482491 470482499
    0x20a0804032d052107020919110c010506030c150d0f020f0d02030a0510050a050f060c06090d081006050405120c040501140111010216080f0c0d0c030f020106 69
    0x845000d58400a030503941207080e070885042c80c0e122001c00c1042c241104894049007424850303510505203418481c5400c20681165144004c1010703107882a500805181c40c039914406085511414940300b842c091b0703203950340031000d000c07004060048005203200000392490600f00301413510407082009030007001810508070110108104451400550b4940071481811403c103010080c4681e40f618506102c2c041203603030140d009070300114017a0044900c140035031740315040d00004541007441140c1e03102101000c200100d0500300c5000b000590028081e506010090b403180b0b007001e030101e90038032164001002c02d02c01141c0014106422002082200580c40d08045015145201b51b02a0700d1051420700c0d902c01c9100d00070400c01c804290060300c01d004950f92000d151100d400005032403400308011012901c075180d414800d0b9413036420034007001f441502c0d00c3c0d207482147e0380c4040c21075079240b40c6c20000e202400c08100146441a84141d0700c80c903080d0507a0a0040c0b0080381000400110790421500b00 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 470484991 1250 470483741 470483753
    0xa02030906040b100803030f0f0601110c01110307020402180120030a0e0f030a2001050712080414060c09090a05040209160309140105071404030507031e05100e010c020a 74
    0x56002e0790048001d01c1c0d680b40c52289100240c0c142c4c1c0141034901c800002c100080b024012610700803404440f80c004143c81e444019102c00070b041182038980d0307000c01c100684542c0b00c0c000c1d0f11030550603481541d20700f4000780c0203e001d0381d000e0702c410a58070031540072007078055901c2000710f1030250741c03450880d0880c00d01d048020740302d11a1064100401c50740b02e62050b0716a4410070000001c5100800b04c41c06007415140c810800c600740d00c01031308c40781d00b0070403080c05950049045a4143e41c0c00290015101c2c011301c003c2d0781d00030b001b0300103841c00c00e0b0b400c0c03030b0880f0210104546030082e13022050103520380d030b0400104485800d0080032440142c0c00c1000748001601c0d4100c5441d0041401a504126078020702c5088000304864080607040711402040302c8d03510641075000e1406016166034144160019070074802d180d00c981d103c014120f902c100e80400c0400d40c1c4503560b88000030b00207000542543e254584034a4803000039140e6108550307172413800307817910310902c10400082068009488100e80070f803181 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 470486241 1250 470484991 470485003
    0x30b010306050601030e010c0206180c01080a02131d0610031a010f030f060f030c051503190207060e0303150901080718061e0305010c050f041415031503060a020309 72
    0x801072a126400302c0d54a07800703a003015841503501c40081080721a003101c029034a41e02503491800d0700d803046554685490380400c51410004042c1c462125541f070380b0000f10001d40c4207146280107040300220104206809118402c00c008000070b01c80d045013440003c100c4060790000b40720b0180b528190b228509610a07000c04404c02c50309003802d0300d8001c0c41c04000d0f0042d180400710340c9651482c00b48003080030307260302d003103101070782c4c00f4201d400100d03601c40c4240541c43e0480c2080281150040c00041e2021031220007004070760050000150a200313403903540400703440035460b00f070f07040750004010011740400e1440c6000c0c4440086848107101e51508482d5911b4045600400039400819651640c0f914082d4110702e0080000c2403841b0620f8040740d041c940542d20301d0004603080d509200344001028415411380300000c580f119032034541880c1c02c1c0f03c0152022840201904810404c5405a1018040d00a148a16004154000d120843d00308060410b10700400c5040c0d1140705106110303a40070b0010740c0c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 470487491 1250 470486241 470486243
    0xf0c070504151202180112050105060616021507061505040e01201e16150605220905251a1e040b030411010f02010b010f1d09040f03080f01030b0103 65
    0x110f01d90b240e440d002141400700782411950909400c02c0000034501d403011125a03040c3c0c0284002c000c25207420003004064403800754141c9501c24404014401b501c0c01e03101142c0c10301c50850550b031500d02c290703891070141d5031504010360368031007181ca040115040034002c1803c03a0040b1002044410f10a02110850b401456050340f4540004130f4104255041c90703286100141c04c80c2c0090f40c5032903440c1d101c1c0384225500c15013154441030036400070341e00c4502400340b8815a513000340034210801e080c1c22600c03850303220404c10041c60703030325005110042034047c4512605030303000c0e04100075071080c680070b2400c40391643c1c0d1000b483c0700d03180051070014200c02001d54440c01c041d901c0c44010402d0410841c0b00a00694104401c002c40001c140010000880c041a07510b250a8072903805010032000141d007214089001507000c9000310381003c10007840384110100610748500440c01c038a251102141030b1100c12102110717014117a060150501d604104400d9101682e454500300a6045a59a011603101880 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 470488741 1250 470487491 470487509
    0xf060d0203150c04181a01080c0304080a0c1a010503071d060d06021e0a1701031a0702010f0e030310140a06030c1e0c02040506060406050f0c0f030f0c07050415 70
    0x80410100010343c81103034001e208050002d540601d8040780180141701c00d07020383d8100940c603202140594000c07240a0b20a0240c600210704559644c1c44200169100192010800c4020205034000610441030302e000401c4400300c1c52015810407090614090460b00044242c00707034400c80c07842d540d043e100c08079841034043d44d5507084007040d49441d10180c001c41d0362000321010b115100c0c12941d04198087c22010038030f59103030058200c0203414216160000c4c00701909482a9111110100d262a0310031034209071a80300000b03040c265210403000b02c03126508242010b800004c284070f000f03100722800300094a01c1701100308400508000080c85000c1d01d1040805258441c162180c0241c0100c00c1d070341408110080c84c40060100e41c40082c050520740c50b04078803e618000103d012403c00c90281c0e03080d15004d84405141240c1c8850618250700500c90079115403054680094801c0c00501c05010451440843e00b0340341c0816442541c240651500120300440c50451110100c1c1d51004c24502180d005030 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 470489991 1250 470488741 470488783
    0x203030a0c02040f051906170a1407080307030503070e0621270d031406012109080f03010314010e190501020913020316020a030903080c030c0d0f0e03010b06040504110412030201050f060d0203 84
    0x2b88002d04007119a4441c0c0030500000ca803001c00d05403c0401944500800e9490044d146451001c0000c3c5000d1160030215070f01c0701c2141c200c0007a0b1110451500070031b02c5c3c4210f03541564480b56150740c8007084040641207400c0140314080c080c0e018000c0800744000441d45c0f001034078085000030b10241c021f0340300708101c821032141c054410500d51f002000301a0400c170441da40e0300001120304469802072004840c1c40208601142010300188101d84101003001c0181030400c0e5400310551001868030000d503195582000011003517698010f201d80a0f0038200c0f0003584a1030000005c8500114001401d000e5401c0800e449000a0340002400d050b40c9e4480d010350785030340314001014a0340c000d00e81007400c0c0e40305407072604125581040d040f0865055075a11900501c0c00ca9003810700380e0f51100009600f002044c00300784031924168100c0d192123000b041025041a035100c0c107d080d4408000420f50242c0d40d0b03001400b4000454201407a0301c024142c40c00300c1d98400b1540460b595200340c5031599000c000907 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 470491241 1250 470489991 470490023
    0x608070b031b09130608010501051503090c010e0102070806161e1b110d050f071d041203140a02030f1305190c1205030c01180203030a0c02040f051906170a 68
    0x80c800341d210b0b00301c4403413041100329242d00c8058003c11080c091a0b1042552112501d072488400d0100c80c480c030440009002c06110f0f01005407074413000e40f43d40c28150700a2442c0030800e01020404030303201c3c01407401d0500c544a80c803c0c0141001508040d2059540309400c255440305400c07040c0003e040c0640f0703080001c40380c550700f00f601c4030341482c10300c4583c408000e851240901400041c01050012450141c0c0e40440e42e654007056441029994002a5180c0000040c04140c80b0070f80703100345009908000c9400b29600403030394180c0004030b8100c29125408000e00c10f480d406020013036885010b209044143c02640d4448656030281300101006040303405402c02c080101e16030000c0010111401064028584c034500f85840b1f4002cad500780c1d0040d600c4e164100360201c0c42445060501900039025629110320920102d611000c1001c1c240d801540784c00c01c101e1442018482c41d4440c0130802c841c1c0043c0315400400c801514541c0c4c0c404e80c00e840c0c49d807070041c5088a0100710b60b4070040c1c0c4002109840d4440d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 470492491 1250 470491241 470491249
    0x518060d060203090604150e190c0803030907081b0d0f021504090c02101406010f0e0303040f15020705011b020f060a030603021f0c12020118060608070b031b09 70
    0x1980380281007500100c180035144000290060041c0d01c00c2803608803403002841c844045548000116a0b01d41c000a0855010351141d10341d00c00d0f0310b01039198032040c980c4640e21241307141d006039440b1003150700444080000c04818041091811109180001e40e14045000205110f01c030341000341c01c001880c80354008550b990140000d50b040080b903c562203950300d901c444c008200e00640100940545480b101d600700b11072149140541503521440840e440c0d0000440e0386c2c00940708000c040c0001030980000950b002c00140006080d001e1564520f01c1c1091040250034200070320000c00c1d03510403241800141c0c1c2260813a0b1681c52011007402c00c80d03032140001040b0b4607820040f141c01c080c0005001100f80e40c5504280c081e01d0080c4e89400710009002c82c06544540c3d81c90403900010080485080015041c50441c0c11083c03441c4008252510342c0084a8400b05062108440c0e035583c0754010414aa810b07c5030000400035070320351a041d80341c400c0a03202d4507c80300018120a2000162030384150352 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 470493741 1250 470492491 470492509
    0x30603010f060605040620031213060618060602011503021306030204020409050a1b0f12110318100209010519170109020403030806090c1801050405060d051501020304051806 76
    0x201c01060060710383c0d40c2c0014250382c5c414000c035000168082c03003005910140749044840c1c1d0f030b100002186004e043c0b80c45019940000b81480040e941c5400b003000100340c65004407806000050b46500c10500e506054a0448125070301c41e400390790505140741032002c4e01000c8481280e405440040100204541d40b500501080d04000d512074404a4003180c00041580500c0c8115000700301085407121200480442d078941e100c44200084124800c8034560f445004c00003180c2d5602c800c042900c640420503500507800845c0d110041001224000030a071208200b43c0166040b100000c40c03405805070002084c0c0d211381c2000c203001d00d903200d06100003644248698600c04407031524450381e95840b0401c500281d030040c441500050042800701c0d03003a242c84503001b40120a4559501e1a02d540710b405020644d284194075418803009000014641c0c40340b5005000c25250804006502e00d00001401150304030390302181c9c11544180420b002c240c840c1cce000c08040c80c0301100500e905039a41400115060 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 470494991 1250 470493741 470493761
    0xf0501020c030d050912070b01060e060702150c0d0f09030f050708070b04060e03010c0905090604090215040302150a05121812070b0a09020604060f021515150f030c03060301 76
    0x40b000103252030341201c80380d00441c01002454180c440b12481004100304a021f001009403080c3c05100040041c20700924800f0500c1c04064400b80c10318a2680004407644000340100c1d003546000a9050b6440c3c400b030194501c02052070134a408200c030103070802810324099000040582800302c1c0543c00f840010841c103030041444408a892190300c800350164250000d20400b03001c0b92031042c000003280340c18040c040700d4111075610400014601000c01c2027000000d0202602700c0e568807040d01c0540c0703501601440c44480000229680d078654410b100000e19a43c11602c00d04a051043c6040b140e840b038202c4074044106402112141c90f140020740e090400707c100070f0290303c20380381026048010400130b410518000c20410701700b9540d00e8030540c1500d4040c0002588074000f00001d11146000b18411010f82903584125212544015202c0002c0c0c0c20650760220645c07003510408800780b4154404003408509130a01c141030144005084031140409007103140400d002000085044d10250300c15070701c0c4 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 470496241 1250 470494991 470494993
    0x203030705012f03090309040f09120503091506090a021b0307030903030801050f03280b040b010302120a08040302010c1401090606060305061c0605040602090901090b030d0c0f0f0501020c 82
    0x14a084044036400c0310090b01c540003c518000708820b80444002c2d0940e4400c421349005507180031031010030400200381c841040100541d654510202080600500e02e0208403991282540e904213840603034901104852032030701021100080091a40726014a03a0b080387c0180760160301c60541100c0121007003c803840794066803002040000034554850311380803c480c000c0e00e0300c035000e90320380f018850541e9910a80702d400d40e00c00483c0001d0200090289140480900c0308010424020f0ba2018007444c005c1d078090351040e44100043c0158031304440d80d0341c58440950010806100d190360b898189010310f2202a05102142c2900d405000c2c44048490301880d00d440204810112442d00f00000c142500072480000e2518001a1003410072140c500511015603076040e044032803660315030014190061007111155004d2005e00c056807194510030303001e45683c9001140f0103818509151400c1280008a020040c850f452000800c400c0610074410940081640e0051211400d2282c0a44194542d00030700b = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 470497491 1250 470496241 470496251
    0x402041e02030a05060d05031e1b070e010b0703200a0b071d03030405010207090b0411070f17030105060a03020d0b0a0f05010e0907080f1b120403030f090816020303070501 75
    0x2040380c05a009500c0b89010010401c084e4680805214075480740c16001042640300300301c42d00700c1070200860a14441c07484185607103000f00c011700800ca030034100307444024160f010340400e00a180c0911445030141c00c0c6020141d050246070303100140f12158580d1410410210003000800304030051001510554106001170308a0520b040000c2c0001c103030505440207881c0840c114401c038600030044500301c82c416030050410740e041c0400c7c0c1000b0840c050141d0352141e520000c0c01038494809001c1e1072214000c8100d00081c65050400784058541411044107009003040103000c9592003205803406200d03189030041c0c1310b511103181c07000104482c1404607031241805200007403810440c20204140c950030383e220f481c4a502c850038490503100a8404102189a11000400c1c81d8031088100758007541d000c03d0302010308941c205c940c140350b00550b103211442048404000903d9094002d401c030321880c2c1402006919101d0b1140c1c50305001d00c0902c0382042d004c2c04080425580d0400544600d190000c0c02080 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 470498741 1250 470497491 470497541
    0x120501420e18011404110f0d1407170105272514030a0804060309031b1104110a02060703050a060b1216022e06090f052401020c09040204 60
    0x901160b00140000c800c1d0308004d107020540020580700783c00713070398426800c00c1c8001da13901c100f2000704c0d52044955001045021f400d40800c0f041e2106800030b100c03c0c005003c0d0241000c1d40420041a984000c40140c0e041c1000d0010404034240303041d4030144201d08180c040d4414074509420110b0301503d0080ccc5900c000d5203400d14940d003000400840740c06c002d41c010145080c10505880d40030400f00903240240600080014600917000b4821042c8645441c0110036540119804c10100c000c20a440d03107001d00303d94165508192080141c0743c42c2c2c400006040505800e0000c0d969080288407500309500c501c0406c40300501038001c08094918a011251941d00481c8411421101180c0d10720030225150f402180b10340c000f01d000c2d0038150940f1042c5a100c0c441126410240740141800c0410b55a500d000042e02e200520841e0741e411101c050114090900d00100380c410112003006a01d80100c0d01c1410009030f03000945803410f42c2050707507003811943c0e55000180003002c0300d202601808824802004c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 470499991 1250 470498741 470498761
    0x3020423040c0e1507050309060f07050c0a0b0a0f02070b0a021b04090816021f0c020f2d040b030d080403030f05132a120501420e 57
    0xc858010103480030001d0201030401180c9802440000c2504280084840b20710191144020b203480ca0180d03084901c0d00d1822000314900354451810390a0404000c9a11010807901f0b00c0440681241180c0d0300d421f0303a04000c0102424881e440c062828045402c1104031028000d0186800412141035000d888202901c006915503000c020098140300041c8500d448500d4240b0880044582280c0c9282c20513010114600c07403d10701040690f803020b0862500a0070105045440c0b0b00039040d82e9800300c6100192044c0900812000318080c4076035640228086245600194040e41070418a00d05104031381078004a001480c01860f5107400d030185035242055076400c02c1c0458000d600c030340d0307040000000c0351030b50004135802500c602010908c00f202e2a000301c0d1682e008118089a8090a901803500300040548807040c65840b0307100178500c0c128820180102803140c1039a4500114000203c1c4070b09150074141c503200c200141c00403a8880050000314420b905034540a80703155840c1c0b0304107091004000d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 470501241 1250 470499991 470500049
    0x10201093f2a05150a0212010f080c1e0409020a0f060f090b0703090b071a04140c010203040e0f040309030b0703020d2a11010e010501030b040309080619020703030204 73
    0xc5035030003014100b9110980812801c218410390400081c03c2d0b150951800007400040181481c0307412074090200703081300001c02d0f0742030303000313000ea0380b105008146130030481400c00954918079480b8483d02c1d29100503403007029510071201c1c0c0b011180010701628510008500b142240c000c071401182d50400407030301c2c80d0400101c071240c42c0c20380c035039403c0b00703550700c01d03a440c42e120360b2200600260700c02004001000000700506032152103040c014180100c1c030610861060401c0707409803041040384500d00d0144400748000a025030003031000c0c61405041804103149110040c20034001c802c561030024060502c503101d158042c43d40141000708a00300054018060341080d41400e0510b4a005046025665010302d14030300301031100ca1520420f14115030503282d62468444d503142075502c41c14603800030b05c0c00b0b11800d03002e0b40c4260808441d41c1058140140301040680001900ea40040140144d0500602180404607031064001da0b5881041c0303800c41c06801240d0150702e0782e9210901c010404807541d200 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 470502491 1250 470501241 470501267
    0x9150303080c0301062f030a091a130e090c0603090d090e010312030911030d2006100b181002030c010507140a030e12070f0b06010201093f 61
    0x40044070b44400740703980110710082c0308450200c0c0d42c074010f04402d1441031086840c410302401d0900c1c000707401207100900319030000030a81c0c00a03581c96028080c1a00c00494681034078101d10300305003400d0301d45c0440b00c00304415000d10710f030080c00316000032040c6200b00180441d1060140c402900d90500381881c541d9492201e0b182d002081c0c0d2240f002c522000c068008504a80e040500511000c200c000180c2c01490060f10030f80d2041d207000024a0a40c0702088040c448110654503a081d030208555105581d51040c810a00715070030090900c038012641d80309a0701560b0344840c105650303c04101c0000c20450340b50030045d0304102c0e13a5a1913400260040040c048000b5840001e0110b961402c01c12603886c00c501d6084a4050f906201e8003101070300c03d40c0140b50b496002c80c201c803040c0b0010310305110103400062080301c1401144110b40108602444181d13005030b02070000744400041e50f6100004c8031800280480d8440d00301c1500c54002010680d40f50300c55031045c40340010300e244250002c4c122070031020 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 470503597 1106 470502491 470502497
    0xc1a04020a090204180b03070608061315060305040b0a0c020607200114010314010209060a080a0207061a0a141008092b03050c09130f0609150303 64
    0x2004102420f42031500c81440748100c400d035802d94401030546c82c0a86c01c030407810410150808042c50b08006d040781c0c000d20900e0320740d1a1600800c0002452200c10100c50310003e0501d4050744158056030040c00c1040700d55a400c0078410540d00700c43c02000060348010300050039a88958149004d601c0e000b4070062007480c40c04101403d40d07289148030405064034000400800c80d561807807a00c002c0e42c6400139030030603d02500051240c0101c2d0340c03d90a0000c00c5001030007509095048420340d5038400020000c2500d0111100d516a00c5d400030300b401a0030f80740001c00d141c801032806c40382450303000380030031003040305100300300d499440c00343c60840c0c9403080c0c4000b4210400f1421251101801003481005038440120700101580c03070240c0000c08410040002e01c015031160902c5030f060a070014008250300944c0100c80c0010070301380d03120a072040d181448009044e05003141c25000c5078001c0c0e03 = true := by decide +kernel

theorem cover : BRFrame.Cov 470323741 470503597 := by
  have h0 := BRFrame.cov_init 470323741
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470323741 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470323741 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470323741 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470323741 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470323741 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470323741 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470323741 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470323741 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470323741 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470323741 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470323741 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470323741 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470323741 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470323741 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470323741 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470323741 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470323741 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470323741 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470323741 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470323741 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470323741 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470323741 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470323741 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470323741 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470323741 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470323741 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470323741 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470323741 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470323741 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470323741 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470323741 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470323741 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470323741 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470323741 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470323741 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470323741 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470323741 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470323741 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470323741 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470323741 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470323741 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470323741 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470323741 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470323741 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470323741 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470323741 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470323741 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470323741 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470323741 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470323741 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470323741 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470323741 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470323741 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470323741 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470323741 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470323741 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470323741 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470323741 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470323741 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470323741 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470323741 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470323741 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470323741 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470323741 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470323741 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470323741 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470323741 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470323741 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470323741 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470323741 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470323741 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470323741 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470323741 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470323741 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470323741 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470323741 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470323741 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470323741 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470323741 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470323741 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470323741 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470323741 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470323741 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470323741 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470323741 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470323741 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470323741 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470323741 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470323741 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470323741 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470323741 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470323741 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470323741 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470323741 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470323741 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470323741 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470323741 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470323741 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470323741 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470323741 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470323741 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470323741 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470323741 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470323741 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470323741 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470323741 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470323741 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470323741 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470323741 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470323741 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470323741 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470323741 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470323741 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470323741 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470323741 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470323741 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470323741 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470323741 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470323741 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470323741 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470323741 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470323741 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470323741 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470323741 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470323741 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470323741 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470323741 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470323741 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470323741 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470323741 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470323741 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470323741 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470323741 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470323741 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470323741 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470323741 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470323741 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470323741 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470323741 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470323741 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470323741 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470323741 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470323741 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470323741 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 470323741 ≤ n) (h2 : n < 470503597) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
