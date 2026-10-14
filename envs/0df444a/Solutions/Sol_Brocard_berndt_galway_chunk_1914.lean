-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1914
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:08:20.353025+00:00
-- url     : https://prove2.me/submissions/0c320aa7-6151-4e00-bc76-f5416b9662e7

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 344064748 ≤ n < 344244604 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 344065998 1250 344064748 344064757
    0x6020c01080612030307081905040c060809010e01320103050a0201110c03030706091b0b030a1a0d03050301030c06110601090c03020d09050d030b0906030a08070311010f05011706040b0a02 82
    0x103603c0000c000c10801d20340c0040001d948214a5510740120500b08084021058100381d102c0c01241407d0004100000d8864500c4074202ca0f0982000d00d0700e5110604814050b00013845107004079071070310500f01038600348030200d0304900345684c0b83d80b000d00c0c40b001550103003c142408041e000785c0c06900300500652043d14408905400c90381583e070008200c600085c21540901c20550300742d61520026402d00c000c6c900d415420010403841d26420034a4114151428007000f4214034916a940b0513844080f005580c01001018000f04407054108240c84d003c0e049400a01065500072507030100410f0361070180b09011880e21901c802802d0700d03840e100b08030019004e0b64010004241c1c0900107180c511409003d06075900340f04501030018415007a000800700c4104040b0b89100b450004207010890728003080a041117500042c500d0743d259040d081c152240104191014220761802d0881c04240030141e00c41c0e4143d80a1024480450f001e008403e0342d0f5160596000e0719200c1c0354004644426a10340c001c0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 344067248 1250 344065998 344066011
    0x110c0a0512031909050405180c1e0402071a0609071b2301050f060303040f1509030c0f031104050903090f0f062d1303080906070602030403020a02030d0906020c0108 72
    0x302d140420f00400000c0e209000c1c100c041c0407a9605400340031a00e810b011300b42d4000c000300c252090040c410300401e540c644400d82e00c140900c84072503d4181511b800c08031403505031400303003041d0f680b00f801345898151800040c022401c0d043c40800410110300d052100d090240c1021740d10144814910032002c048481910000c8401c100b00003e40392020343c0e070040d402d900d46c03242d0f0000500342c0b600808010103510024202407094008100c14408100ca09042c5400c1c0d07018030303400744d074501d040100c01e5a42840607000074008018255000544800b442c2c01c40c01521710400803010034220390300501055443c04c0d60f401c01030303030400d00c8010310340d003005000044c2443c0c0017001180401c038014040b841951001c3d0144000012126048490320000c1040e0083d514a4402051030403c41020415155542d400020181080056061425644c0300c007541c80d9a90040c801b15902c0c03c140c48d001c0d544904000040307000e8002c4103400d00138580180f0380c03101121203075009086c1c40c0d56200e004560515004165 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 344068498 1250 344067248 344067253
    0x20306040b19062304060602030a1103092d09060a03020906010903080c01090203150f2811180109050a060f0c050a060c1b1101110102070b041101110c0a0512 69
    0x5080303061140c080d40009003035100009291035209a074a01c0d40d01020700d8a05e004600300001044580d5002013180c110710505c3c5012902810f1125443d41544640a4440e1f0302c01c000e004c200f441c1ea03030703039101200d40445412091214076071640240a0f41250882d06036a000488501c100054180b408155a01100c149840311250707499591310b14007030b0002c034400e100980d07582518804606080080032071b1a2410304c1c2d8200c9515052072500401e80380100b00c110340850100003034056a604c041c1901582c0c10814040c441c041d0700b03900c1010241c0006071088c1e0391850066889520354000c01c45102500c90291203030480301d007800401da0700a03003081c6c4918200125070440c080407600c2480700c0e940700c3d4070400010440280c0341c64000d010f140205c442c0741d11064441d0f54a00012500c1c0080c052510003804c028003503559602c1c0e82402406076541c044d150701460010841001400c034200a0954002d8981d0700300011401e014a5590b0000c01006421182404060265141c030108031004603291008 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 344069748 1250 344068498 344068531
    0x1060e04031b05070e22212615040e0a02040203090712120201050c0a0801061b120206060405070908280c0902030615120612070b1606060e04020306040b 67
    0x2c1c1c43d8a082d0459000c4200c541c0c2d040c4c01c1c801c0a003010080b4a031051100180d01052506580780c0604500110500580c500c00703015490f90240c0c0907110419440c200554400c0302d0803500141001868403c59040741c180b07691020102c120701d0302d48100d5214012880046c15051225070030711000750f001401c41601803064104c0000d005c40094916440305110f0304544400f90907041010f4203460001e0301e1030060400500c450102aa40001186c0c116442d510313040ca4170742c070400c8488680001046003d00f00d880400d8600c103555800141250040a05603070030485562a08412207500240e405200350682194506501009003441c0b011070040007056000e591000950301c0d8805039a0325402020700741c3d0048104403003860b1140a151b52210b00c010301e1490800e030414005058040100342030711902e04010034046401c400c1060b10301800f1000166551900c40c1509000e14840504049030904d051910110307078900040c41c1c4c140126030150060886440f240c1d150036210f00e0040480710b80c002c2401 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 344070998 1250 344069748 344069753
    0x906020c01020403030302041502011808130e090a0209060a0815060f120a060b090609161e0c0b0109060305030f070812010e010905240f0303040e1e0901060e04031b 72
    0x8003c1005511035140180e46500d440340420380384518102100070340e4500000d19548100c41041010515808000140c0d915518000b04142419036044610f8a11900081007480100011200c5186008540c0314255a80e848100807002d0400d004082d80c2e0b0b00505140b0110018804400d5040b080007426941c0408000010a441d03252840e10400e50b90b000203908003d0050a225449402030295088222890880e0110300580340c007400d00405409600c6c01c280d119840380c0c159a174190038103560301e800a0300340c00000348200e02c110740c29600d0300255800000d40207524841c440403642c1c804042d6081046c140b40c206915004140c05940c901307420031803031603d14031304200580602010041000d56504283c840340490300000c0c0030070150003180c000d83d007200400c40c4840500010440c2c0000722034070000d0200e41180a01d40c4440d00c0c80c0901d40a11129000e030403a0404807200c0c2c100170343c1c0c49980710b00280b800d0340c5403032080d064001500307804600440e108050001794000c0c603890100c41c404a40c0d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 344072248 1250 344070998 344071001
    0x40c03060b0c0706080906060303160602070f081b011a0f0a0b0f19110705190302030a0f021206040b0c0706241418010b09030f030706090302061602030306040906020c01 74
    0x102e0440c00182c000200501250b500281c5003508103141c44018a050700e092000710303a4900c961000840c00900100c615810803415070100c0319074031380c0401c41c0d05500c68146400c11303503604204503011113482c42c0c6a030315840300014464800369400180545510344038003130520400000036600342d070300040f07014000320f19041c0b14801403002e10400142c06a440c1c042c000f002c950110501c0750b51040090b541e40207411454006611416144200c0b12242c5c161001d458074200c00c819540000c0d05805205180d4042c0038100c0e11121303546000783c410070811110014000e403128000c503401000d0325000004070707405407042000341582a110300e9000548038030051000318070800c05c66035024240303d40c072070074040800c40300c01d210310801c1c0035103880b0740a42501d80318072401d0340140590302000c200031803202030603603040042001001829054942e146664100000506007614041d0050310913500842c0310030541c1c1d00d00442d241c2c400d90203907041d9201c110420000d0810700106030f50340c540134030241c20342c0c0c0c2c001e = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 344073498 1250 344072248 344072257
    0x106030f0b0403020106050f010c11011e0215010905010e0109181e050c040c0912020609040c0215010b07120c03091a0904050c0306090103081308010612021c02030c040c03060b 77
    0x25101c44070540c5001e103402030950341180c0015019032400d41019466980101802080a0f40000380c101c1a4496074012949100e8000f0425138112035484a0102c540d008030f0981c02010307416007c00d1260f03032101c10180640b03800b03109a03a4841d44920041000c4c11490b480301c9649440c000103104016169220071264450f440c064041c81000114071504105040209507080301c1c0581e800d111075020800041c00124042c4112852048004100c40c110f503074210444840d240010400c05c43c100e01d144000307544510b041007507030101032401c001103110301622003a54903080e44400c8081c00c00d4564882200d0504044c0c0c012001d010441303a0100d8070001c03030642c0c01407050001014544603003654040000381c550161510058a03001c0080c003030381c0c0d03c581c06818192030f04036241c240d49565600f0b07480000300f180c0d0700c414500d510b011004103042d03888101c203400300d500840b000c604990740d8110400c0c020280080c0254550303c4101c04c4c058038142a0002c104003905401e001400c150707243c0355180617038031 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 344074748 1250 344073498 344073503
    0x71205040302130c1d031009050f01060f061107080309040b0103020d0501080616110c011b0503040803030114041b200a0b060306100b03040201032a120b06070f080306030106030f 78
    0x21104401503085600094217280460000c1140740301c040b080b40400c2c0c85011904008400d2610342c04500c0c240042040b541400c00703000f00c0208025503503113000e000d05403414010400003c0340d000200003080c0000a81805840c1000c019501e03001660003000b00a002451440d8180f41d0280600c280065041c89014001c020b41c00107400c482c5020480390404000040c110b03c00d011402c140c400e00c05900080384105a0001e080041c0e1450788000300144009a1520007020b500c000100407824450200166048a03194914151290740600800c170503542d142869006000d60825a98201071060004201101040c0140c105001200b03511a04181045c0c2094540e08d80213801d0210504042150607030008500852000c15070174019a09980d1002401c080d0415460f00d05051131010b401150140b0028880080c0b43c0400171114060a030a003861044543e8030724150025600b410030070100c5039255408164040d041c034250b40c403110140c00240030140c15641e22400800014416070001d9481070 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 344075998 1250 344074748 344074751
    0x3040f0213060e0c07020306010e0f0f0711150910060b0d0905030c060115020d0302040e0703090311101a04050105011d0105131d090331030609080c010b180402010309061122080303010b07120504030213 88
    0x1619180c14352801500e0413042100300d150071000c0040e40400810b45840d900d030610045803400c5541005840c602078000d04480b113008800000880c01610303030303500724501e8407602a1564403128041c1070741207008902c03c0054205480d400103900604c2680060311151190402a61080320804080c0c50400091040d100b804d40e00d030f0b002d044102180c4070344180c1040890701844698105000244000c18100d003106413010701b08448900b6a00500907207510007030101c4100405541d604401980d403841c03080201d41d9032452800301d040d01c04080f088803161180c2c459142c030200340c00000b550300e0151100740f410121117200008800544240528400540650380c1c6684852098030254216944007400f10321404c10100d03a1014100d00380c0d0080e40c400e8090a001a042c9003d050007006800000321990403c01c0024245128400d180304980d0081c8800305000007481cac50360a500d0383c0348000c0c0507079031030f18406100c140001071000004122030705183c60032500f0030f5500d07404101041d8054003144c1d480c5 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 344077248 1250 344075998 344076001
    0x1140105011b05060c0c101b14070f0b01060e040b1e0d140d02070909030c020d0f052b111510080f03041a03040f0213060e0c07020306010e0f0f071115 66
    0xa00070841c03000c8201f02044200207456083c8038a000042007100300e8030a1244440034140c035401443c042d5080d280d08a0112040f240c02d0340f50140d0a20024010b1002107142d110441025080600c42e10b44030940281501d52410b00500d076801c4a840264a5550b00c140c0025a000004284800b40220020300c20010101c404910740d02a04052040c0c01c40c2403c2450038a10402003070780702c00c0c0c40c0c00064050300c80186110b42c5007400c13026075020700d402801521402c07200e002c0b4021401900141c04040200540111042190807140c100c2920b0140d07091b68040d1312606a030a2616400a0700000850000000240e80d9010036051040d0341a05d10703da5040494104001e520148120000400314030480307103140780980e98103241540780900030380595103400c050440941c482c0d010764040e01a0390316080041c9028a1031041c554440c22080f8001d004a20000524281c1151000d01814603500c25a80380d540f030411003006400e006040d41c08002d50154440e5410700103102d560459440c2102c0603299 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 344078498 1250 344077248 344077267
    0x110a02032a01080f0c0a170709091d070302060a0306030f111003110a1d0316031101020c03060c160c03050109031701060c060b0f12031b01140105011b05060c 69
    0x15290500401c605220510701000060000741003140d51015000d4142600c448990004460280300301d9071403026400520180200d039074000d4404002c40c0c410302c1d814010284d00040254604010b800c00c50740980c00031390b0a000601c0c0c1071014025040151400080c8640c0c0c0e61074a000b01c41440c1c03401c7e0751801400300f0750300c550f0800b00c917004201011800d0611581ca501282c52000e0300c20b40b10980304021210012003826400d00b80810010f100080031a12502c0507240066a03e241c1c07440210f4010700454565109540003003a1300301e119070014040c0480d0b40e601001c040d05030f4418100c4400c020810241400002c0e01d04800d00080d50180c000001e902c5039510380541320a003026000d05134020a9001001199400801030610b182c1c00340340400d240801c9808120118070f50307841d459114060010350300490388000090080e4441e0408074008039103205440d1422100c488a02107440244940180250f5000700c01d11b00c190344401e200c0000040307268540f542000c8040d10415042c90000862815 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 344079748 1250 344078498 344078563
    0x11060324040204031e241e0b0109051e04020403080307080907080606060d0e010204120b010f0e011a09090702100b01050415140f07030206011a031006110a0203 70
    0x40104199421481c2c141151034130246542004141710340c0d0003d030ba92203810807200d1484600b281c4a0010345440c0007000c4079200d8040c012001c6508059402104d80082d1120030b806112041c2c0c0c01070311035490180c14a41031104400304d070030042e0365051001c800f00700c031501d640c401480154010701a068072400c0c00200105a0000a0071404070750380701c200300b8010454042101c0d50401412500f55581780c80c110b60030b00241c0880141810305510200340007991030711241f02000b00d54400d0000c2070700e0703a891784550b0100c2c076464000d40000400c00401480030b0600c2d05946021103516000341c504261a8000040b46040c080321203c0040c0c00980d0002c94036601401440302070302c4242001400c0030309000c6044840807504400c00200000d40610400c0300110904076440a054121040d0740c4480c14240a981c0b03030800e1103500d000e18032042402e5120003080003070b6405500940211041c00703151620844400c054015a07021070701510300060010f036800c00008a040425000c541c4030320400084800 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 344080998 1250 344079748 344079811
    0x1030b0105060a02060606031519061403090d0309021f0903211d180a0504050c0a06020d0309080f0403050604020a09090807030c110406030b100f050d030507110603 72
    0x180200403c2c0114a04981c000c43c09550101c0140c840a8403651900d002c803c4020301e0300c1b038031501b2903203c0010300001070b203000303144003a1902e640306c0342d8545100b0500b2a00e0f5200482c0c400c1400e0300007440c250707520b40c866002041340c035000030005004400110b0744100c910106004585c04201c610804004102c00002515001412003240444d1101000c1d00508015011018a84442c03030b40c1ea2605490384d510b4120000100001007041c499180440c080d20041a0540d010384081c807a9610000035490440c0710742c41070710135030381c0601580c41c40301e4800d03405040000011501041e05004900d105036518014100550041006080504140c0140110041140c100075541402d0021074408100c8035400c80d075060303600d803801145400090500301e102010006500c0e42c051b05081000060042da03148450058400d07103800f000d290f41d40e1400f80308020302442040d4014a041c0c00410206e070207400a008828003580070380b00d41d81404400601e89500440d00000c3c840b50030070800780d04140408018 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 344082248 1250 344080998 344081009
    0x3010c05040b0a0806030703050601080a050714010c03360501030f020703080105060307110102030a06080c10120b040209030a03020303090d170406020c0c100f0212040e010605031008070e01030b01 86
    0x158500750601e521000e8520071400e080d02400f1003400402c0041e24200100402103410409551655071a401043e8545c00c0d8240152018800e100010800c03501321810300404040584890b2000403055500b500d000c091901c0f0400740c68a4411004402d5181000c2c4414144c44280c10410751400c0c42c0026040b16156080711724564818455907000036000b001c00b9055032821101039460b80e441c2c00003280c00046c036011408941d4000301c00c2c00030610075074004100b40d40c070110964090a00e114180021424288465400a0250714101c9845102c560100d001c03c0005400549442c0480d00880d14020005408400590002042240000d4240590180c80320079282021500c2d00c4005c144103200b0002d00040c0101c2e40c00500105801c41c2000304188200000e414040c50305502e40000d4070480744070462a01502911544007024039920f02191305a07201c9443c0092964240001203c440d0401842072640c45110710000c1120403040150070024446140148015070651900203012201039000 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 344083498 1250 344082248 344082257
    0x50d050618010e1b090f0622030f0c060203070201271a07060c050a0e01080c1612090902090d060c05040803070c060f0e0d060f1506090306050f010e0f040c03120201050603010c 77
    0x3503c101e0b60711820501c0c1e100004842540c8c541030050720781c1141c0c2000303000c038242c85001920000108218801d01c02c01107030060b0f04240002d07a840e0401da13102c8c0b183c0c210007800280031075900511401079800030350034480d200041d101c0064135044000280031054107042600321005c50708600b00245801101d06480080c5400350900d40c0112014201c5e5029003d0b00341070000250004981a5950064503c00341c040948401e01151600380604440014541600011011000030a600406000b1a482070402901c200003445050b21030780c000341414205d1808100080000040c585401c10240038414080e8800c02c00aa180080150081c2c65000f0560144001e000c00400340c0d90f070b030b0301c03800c0142c503040b44000c10041c0c00c1c000c40d04020703d1407004801c091710403c0404103446a0108582060b42e104d100c04004503200c0c440a80c000410901c0f4071104050540c00003196261111051600039201704141c106131511b0723503940d02007400421010130040c2c0d51901001800d241c2400380c00c0b403044c0f440c02d1 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 344084748 1250 344083498 344083507
    0x603020306030709060f0314100207061e06061d120105070f021c080a0b040f11040801051b250507090b09130b01170f07080303010e16050d050618010e1b 67
    0x1040b41009a44009880311050b030030340300c0323414a080c042540707a1788041900f19540c0420380790420017414801c115004a4000030742801c80132006101d44416201280c982c000201000c40b00e0f00096030394008925004820304001e0100042c090241c58040d5126840b540900b18842030000d01c1c00c0b00f803405500c41c55921045824006400c0300c546600010181c101007403171042903000c030300a040f680000700300031803404004001c0500e90708054000c2d10b0f00207000340002d0310740c2407600003065124410704900d600c081040300c0e03e02001c50003883c5400d1420480213080c44451703c0f40c40c00c00f04250b001400c1141c889881030390ba454001c6aa607400401c505071204070700303056240c00000348014015480b5880140c450398580c40c004000b4640010300300d0040380d0303c154070303284110349941082c031688503000090804203005054184101540c0c00640e13a0f69030404080d00f1986002e060b0240c045071300040c0e810b200c42d1140d01041120784c0601500c8903402201e00300140e02107100d0952143c0028055028030 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 344085998 1250 344084748 344084759
    0xc090c03020415020d0c020405070c0b0a0e010c021b010806011b05370318030c03141218040c0e0904030306030203100614121e060601140913050a15060302030603070906 74
    0x6c92031003d058054a00198035518510123940604c54a100500150920030401490880715007002c070091802400a20451800780d50507a940c1015000e032a01e81c1e450040590302310351045a45a6010005241042050391802c4c2510080d5080510039a400c0c1c103e1110001e00100441c0400051182100000c1c200d01c90072900702060b0034281c1004082001c2c5044c2e5920002d04500c920000d0754104402444d6a0b5880c9810b0303d1403094046801101e000384100388810b00b01e88810741d00e0380125545c018440e8502c0c071003004001c10700c2c2d0105200b07100200340c140a4035103c4000491040e4800d0310006151415401010300e4042c00b000f007610408d05200c0140326aa400c4c4c2e4070752002d070006449061407103401591203030030924903070380210003105104424104110000b490310b00800e000e03201d4440c645c002940e4070446100e0f403a102d80c0c1040d071400360b034503031044e599129507840007007401c00207048403c3c0c24a103810040194400d1002a801100344000d900d401d11500000340402c9208100726131910 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 344087248 1250 344085998 344086007
    0xa050108060d020a2601060e0420041b0201150e060604030204021b0a121103030f010e04050a06051003021903051f061d0403031b05160c090c03020415020d 68
    0x104900d002c0c2d207000d580d81c011520303080380c0f902c06070140f01407000520666808140e0011091042d1104560a040d00021311091303c103207003401184c00640c600058402c08144441c1c1d0080000850381041c0d43d01e460080a0383d0250340322449070200d50000c80c000c61880b80d0440344044030740052180304e50301f1061200c02c1d943c0808840480c0d5065501580f605142c00d443c00310301c151280c6d074250f5802141078920030410517035054001908a9143c2040e4092410300952342e80c04100c41c03030012400c0790001800480c0e404082d0a5103c7d200300c0840e0b0702414169036001c00d4941c1600c5808074024400814400c520307121102076a41c115141103158150728546031190b840c0040d1410000c500e038449000301c031003d001e0704894081c0000d0401c07610301001c920143e41280c08203c0d03080e0000381c503100070503a41588651100601c034406907980c1c2c3c1091080d0310308071002201c0107406c4600820601c000103101d421070041030b03840e103610780f80141c9441c60400315082205e001c00c041c1c011504050a03003044c03650071 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 344088498 1250 344087248 344087251
    0xa0215070f030c020c040f0903080a0c05070f1b0e01050a09150b130905010305030304031202070209040206030613060902040801060605040f0b13180504050f0a03050924040303021b0a050108 83
    0x78940420780c00301c00f400507070400c56003081c000e03046800c00d19403000d1440c00f0303041a00c00c0c1c0e11959072604a5941c5120b010101c03103000c8801000a2410807003003010076044108a5003450280c00400702c9515070000302c540b04092503004080031100c80f001080a4a80040d45400506010b84c06120880311a81012101070890103650500c5a010601c0a509481450300da80505480c5008100550310380c2840d0343e4a03001114100d0000340c015402c2036104069000361052254064400c2c01d80d44c40765803c002e078a0b040240003039000f80100c1090101d605c014026400207145800b401a512420010028290b41183c1c02440c1880800c01c003c000c42410601c0d032001b114842c0c03200684402008400c0d982e18040c40d84034a0070310001810030071240005500c40c41c0242d21410403034402c44a4082c2c1d00752144000000603011030810b0009045d242818025120103240300e101845124800000208c11a0066001940140d00c8001c008000c1070705900500e10420f403c681d420070740c03450a00000c192200 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 344089748 1250 344088498 344088527
    0x70e01050301180207020312030a060b073c0606031401021e07020f060d02180a06140708070c03030f03050132010e0307090e100c0f050a02070e0a020a021507 69
    0x70022440f5007850303503040d80d001c164020280c500c05845082c1403059134206807800c448091074201c0003d003d1000c241101c100c10350000910691075501d20454841c440010300c542201d008400c60340010003030a5482d000303418410303140050b207030b4151300303041c0810030308140c6241d0160700c1003051090034a0803a2031013100d145c01304500f9565882a00c0415440d9500f43c3c811600039101040101d100500d80d000340014020100303007840361341642010059900d0b114170030f034008241020340f400c070303180640d00040030600d019041040c60015580d0fa800c0f0341714501d0f802500001d1150a41038021541802000c0c01070000501c0c1280a0104401c40360300f40c0c1c4541c0e0000400d070441041019a0f034042d66040034110720080a444030142d40f8002800545040b00384003c0b01d000700c0202065214161141401080d00c60b075900540741001407041e60340e0b41c4104094003e6103e0580009030360f503a840402407142140a0703000d80c94201e4a0303000f0b4507015040d109070101041040c100040e2540c0088076805400 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 344090998 1250 344089748 344089769
    0x10c020a1205090d0b1f03020105090d0f05071d09010e1507020f01050a0b010e03011107020616060608010f0c0807140a030b090405030c0d0206042f06070614070e01050301 75
    0x25020006031102e00c10034040f203400a01201c05201400030030014144034407a0412581107200b01c4030103601c80320406010007030100d0000e02c030708240f41c01c003003200c030100354071500007242443c003070391255407605100e81c3c0030a098088000040d00400e051540740c0e40c0100d2080001d0080c1800074407000c2e02ca105031261072510f18cc03024001351210340300b0018140c0c0c0c081004001c00c200d0414494000140000248544c04501201005103c5040511444003485528945241814110740c02c01406501c0b1071500d5241e1480d41e50580c021542a124120040141c3d10000542e5122003150700c040e511400210414401035604210034a03400440130364141f034800981c035079142c426100940050140611180d045000c460404c010040000003c1c81890088000c41d1021042158101c0e0342d0682124010600c1c115980e89000740204d0808101d0f240c814011102807200039540440e8058011007001d03a1500d450304880706001c540180405d07003250243c40c11103101d402813000030304144010f12840c0e4550 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 344092248 1250 344090998 344091023
    0x8070f0201200615060a02060f0a0209030f07050406151d062502040f020c1903050702090a24140105030925080d0c020a090e15012303010c020a 63
    0x1a031007803007200d4010200c4040e199a11044005059072070760125040b0034880d1009104e00d89614152003039038500b9005500401c1180d072034001844040e40d0183c00300036459024009203103259002e00460b01075a020b030000340b2a40345800c0400041d549a0790005c0350281007000329480a903404034000c40701c01540c80d291020006c0c148081480c0e07114059000d40c00343d690721000030402030419042e407500c1d4000c540600606070809032040482c820401c403c041540510541c000c210803140444203214080d08120b41071281c0c4c0c5c5c01058070214100d0740e00082b2640d030000c0081c852220500941e50300d045c2c20320f00c01c88a0600803120f500300003148009040c0040400042c148181c1000503c220400e24020300803868652000030000d8212402903045502070100b100d0010703031040c0707011441c3c90b8004100000c080e02d004900802044950080c0050340500001109540c1c01042c500380200011038020f5010401200841020030b000061503129174107048125205560000e508170000350490158501c1 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 344093498 1250 344092248 344092253
    0x6190c020301021303030e030d1e111002041d010303051b071d0726010e04060e0d050405030f03032401021504031e05030708390307030b06040308070f 66
    0x5000088009505600004121200724001c00903441102e02ca070321070b11032041101c401c2544a030f00b81d664800000d5140000c840011107680c0b101c10104020303003040806400607001690810188480320340c44190000390410078014485040401180d80d50b10b480c59030b5046a4008083e441450840300744c0780d810000c1642c1580c1c090107034400130700c4803c0300419500580c0304070440710300d0200e0b52080400d60081a2003c84040c18030084883c4a0101c1c81c800c06a0030150554520b140c0548103640d400da5071414600104003c111001103040345480d425100d9280800b0989403880001c010500d030f41060061000702c0882c000d0080c000c21143c0145007092442c400100c0c03400290080c0007082c0f9540c6810b02c018150031103001a01003400989801868403070800070349091100380d5208002402d540001000c45130001580404401004454205001c2d00081c0c1d003050b40e481c05030024010000020b008440f80c05100d10801550309076400d42c00c0500d181c91b5003100d8090300c140680744070003c8295204 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 344094748 1250 344093498 344093507
    0x90c05150408030c160f03080304150608150a0c09060c0f05010b100e0a06030c0e0f0102211c06050d0b0a0b040207110f0103151e0b07050f07140619 65
    0x2d08525001c49443c0c00502d140c50303645024418000b0f944020090020840d40c00800e00348055036000300d9181d01d55212550707000343c2e20601066190030181daa48012030080e80c24040b6100d00fa111500d140a1401c1203c45401200c182c502e4207802e00641c56810080f141e04a1100d2003190780005880c440d004050404a015014032010380d0380c040801c510710010282c200100010300441980c044448548543d800d50859601c141c000000c103c0c1010340c01d220345480e00e00b2005001c03062055619000051141002c81e9198515205041d6404030f02683c003083d59034010455074003c1030060045520b00404901d2100c21032b0b001400400c040c1d0b0018901e0381c0140c10040044402030400c660700e907094100300002709a00e00c400d03446941c491000c621190300c240142c0000c0c210450000905070b1800c24040c55202868080c070900c1903901c4000508465135002078905140200040d01c44000c41450490070902d003074010f030700e1140c04e81d492008a80c407828151000603103001e001c00044042d0708c1d420b4a = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 344095998 1250 344094748 344094757
    0x114100b160c0f0315060506090405040501060801020f0a02010b1f0804050c0306010603020d18030801090905070305010207050604020102070605040f03170d151508040f0b0c070c030501060e0901090c0515 89
    0x41ca00b500300c42000a080c02a5100354044901503071212120307000007030702c3d5030a0f200d1500c038580e404903041c0540c100510b00b0b5407145d40c000b4812000050080d9403000a242660800744283e200718030003045418010390207024000300d074003044514403075119204e5075200c044418100400c0c02c12507000700103810130004002002d40c1010041c2220910742e5030f02c500501a500900200089a051481c2010500b0059201d80e4001e681512901c0c80c03a820031600500800d2500c0301079490384034402e070000201d331080c401045054007400280242d4602800064501900d51348008204a0204410480e800c0442034007404d0301d0348027006d412000c48a000c620007030301820200c1086a46490042c1ca00c04454003001c10456002d940d054607031403400e039030591784190102e6000e00182da0060180001500075012540d11080321440d041c144081c50300d8000d0940c07815001181c40e0781d99820184105103580d0f601e283d00c001050024080d00030300d40d40e001c510680e1703440f4082c0150020b070f4141d80304a4901090f43e = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 344097248 1250 344095998 344096003
    0x2a0c06010e071b08030712181401110301030809040c0203070506370c1e0c020d02061213020406090b1c170d1a1002030a0509150c0d020114100b16 64
    0x43d481944141000f25003540161050804110421403100714034015000d0750b012090390031100c0509004c940c48100001013030601c03801c51035507206065281003080310007442c060350140303190986800140c028481180c2101e1070020540d8001d11490000a00c0041d07110b034061040201c00382111100c0c941d00d00351001c606c0141050800c0311205601715903881e804042c1c1c04103555103034140714800d00c4540c6174100640030001c000031800d610380360150030a180070f80a11440600704500c0c1108110b000003034200140d54590744658880521025840c0a0091402514a64a042208400b400700040e15141000031034588807018401e20000d02001c2961216114217a9000c82e030f40e50001554940201800080307951900d0351080720b900141403100e0300714031401d52a0021490820303000015103184d001011440d0340f003e282c405060b00c0c45d8150015055000011008054800700200081e0940b440c201d0100040c103002400c2004440d42c04060700102c520001013280da440741c641c0d407051040b9051a02 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 344098498 1250 344097248 344097287
    0x9080403060c05070201090510050703180e01030305040f050130090803090f0106140105040b030c070602040f050102010c08240d020402160c080a11060f070b2a0c06010e07 75
    0x2000106411400071302402e4400d80e1075202140e00e600402c40280105800c2174001032041c00740c500000d000301140e0b003070f01007404415103441d40d85217441c1210320000d030021000610080f404118094407141d00e10050502402e0103401d0300c081d60304108a00c149901d00c501000c0d0000f01050181d00c01d64080542c5641000b0700c0d9940740380c0307d00059950743d00c600310810290b1901e0000280d4908101c40c410090805954061805227000d0040c01280c20180c43c865201d4000c02c080c0b00010326501c000c200400ca0720341c02a561510b000700180c2112526071010080c4109401005280c0c181d0340c0c840300070803035619150b48100501c3c002040365602c04910007508540b00084c60340c24020b0550f000d003591882107a00e9054640ca42c19040c0d260885400010710b8044415000c06041c035080c40980860040d41c03c11905014041d2202c04040d40306803500c140c504000c81042c180401251611007002c8030380344201d46400345607880541d035040b051040c100180d61100100b46220310031719101c54848108a40c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 344099748 1250 344098498 344098511
    0x306070306050d0809120a0b010807060c050303060402071406070c0606060804030c1403040f0801051b0a080609060d120e040f1a0d03112406010903030e1504080d020c0f0a08030304060908040306 85
    0x816181a10080c014040ae5104c0c1200003c2ea1510807226103180700d038400c1c051070564031a0014880070350031070102190013010b46241c1005041e01044005c3c801d40c0940d8500c0d142d90304034103084045401540100040120310401c2002003504100503603d010392144055400700c1e50b40403201d095020303c0d000204040e004804c00620b205054000307a002c5c0c00c554a1030808905a170210b14a1440380000a0000c20444400101203140c40b8403900e81c4104054444e16918901c1e5691070304014000c982d034404540c0451034042e07079081501c941d9416a00a50007009003203c842c0c003d10182c5420007510f4445c0f14521001005c05100c2d20b9500b14280041c01140d41400031740345500514030b660f41118011805090000c1c840c1c3d0701c600d44510489030551603ca10180542c018894101030180e00b101601d0390401002a0b0204104044c61031500e503035000d081c502a4031020041d9042c001d000180c8140c08040007448001d80c04402c0300e402590010000a030710585c1d1400c1d00b494006d503800507001d02c0c0b8100 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 344100998 1250 344099748 344099753
    0x92209080403060b010203040303172706070e0105093307200f0a1401170a0e1002120720011107031209050706210e0a020306070306050d0809120a 64
    0x140940705980c442d1405201c8001803200480c0e072030103148006400910580e821003d1280d54242142d0040031204450a0f59004810444c0901076060070706060b0f0b91080d01040356a5901c000a07004044c001d18009203003104003400104090810b10360801185400790b0000940c031340c01c5000c0d1030300c0c410303d441541c0c6402e5582010040100301c3d500c040030300042242400998038081d0b40d0110b50010080c01003d000741011441101142003021480c144403a90f4002540315041d02c1c420741c41905054000310301d8402e003025460a044481d680342072824014048110801e14010805911141c185020301420000b95407140046122401d4041c03d0351800070080c281c0702105c0f004043c41402910758244030040f210150089900c10310010304103800488040c015240f05003049455119010000d4a4400601c0502c2089900c0c0d100000c18590101c10101c0840c00c05000d21070788408103003410401c0303c3c50280032860241c0f290030005d11404000079860303000d03690101c4045000030b030f42c002c9400c1c1e4120f91 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 344102248 1250 344100998 344101013
    0xc060801080d080c0711043e1602010305060619020d0f0e090601030b0424080d0c0b010b090a1806090e0102130b07050a1208062103092209 61
    0xe0007484140d002d50100103a1260180881d40e0048004000d200e02d0100701da1101c001220042d0341040d842a144c1c0030402ca80f6001603140182d811440700b8a801d80e9042c41003002c40030040f02d0410500410500c50030a904440340c40340f45a207502803d0100301640d41e407001030664812940e04d4a04810300c0032004501507400503202407804000d84030350f01d00085440c81507070002e0340d01850540c8445070500003825075101380c010409250380908081051000789030700441800d10a1f22000000703501800810180004000d0980402d0190400c68250011a10354442040050062802410780024104120740383c8807401c1008214440042c600c5140e800c03984000350130780d0b02c0780d0791205080800e0a58000d80c18802c4400101000c0700885016141c141c0301380043d00840030549071402a9801d0342c01148a0300e005030400c900c00d58405681d0319049081041c50716240500c2640d8440759440c0c154006000000c9406d100c0045407040c42c59095810340c4620a4108c900d803140c4a41040000070801004 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 344103498 1250 344102248 344102251
    0x5100e0c0603010e04120207053109020a0303050702220b01090f060f0e0f090118050c0a0c08070f050f07030507080105101701021e0c0105090109120509030a0c0608 72
    0x20202661040c108140412040740428011102950144404a00052903401d078210201a003801070b03c5d1144e03621000900d081040f40700c803d001b01c0d024030a4100e040b84440d4a420b501c1d0b10b02d681003040440300d4000c00e1412000307000050034894001030910a560740d41d400e000210100c106904811001e154424000d80880825140407942c00c88000c190040c80700308500c2030310725581c1d6a40500320303c207608035000104c01000e16003000a01c5010209a201c0c454800d0180c01e449001203d01d050410300d80301100c000801d42407180a0034003422805561160140d000c2e00d411294441c0c44018a080c9551040004800107041d0300c1082155103902502003a808100d0b0702800a0354010744c1d8403040c01e803c2c3da1049034460000c4204c01d02c04d00c1261494015801d00c450b50400040c203203807c411032401030a0b100104440180300100350b418800c2800d0007059404500c040090103001826980c00c001c00a8100400041c00700c040740118054504100c0b2400c80c580080210394004d640e0003028050040 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 344104748 1250 344103498 344103521
    0x6090f0507020a051011070203010203010f0609140a0e15040905060601110105040f0f0507170606040612020123090913030801060c051906021605010b031006050a1806030510 76
    0x900d4001404180042024000a9003100c090600c2401c41d00150b4000c140f02241030100d9030703043c01600b015071024400f80d800307041e001c03150401a90801c0c4000c2c08000705a4050314113211451244202d82d212511030784215180e9610185264481c100c001500c440707940407041c1c1151410b1546024018006a110b00910080e07d03140c0ba040c1c142c541c5682030340e004503409000e0b03001106003100000c0c9894440c4148074002c00c02d482c1b546865009403d00d100e6a04081101680080300f070102d04c4c0b40902c00c1b10020704240c800010700c40c16650000e4560142c8013140e04802407068064100f082080c2e00f03e070b419200040c2200194a0b04500c9805204210881500001c40342d000200347c540c02034069201c3c541e04840203040e40c07007111503848040b40407140c048556540a03c140841135811007014140d2178400e40000c100403e0346d1052500d040788900f181c0c8102411301c0810041d0783c55181254065510007170f07820f031048469030b01300e00181501d940010020f1160740655045040b01d079201060684 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 344105998 1250 344104748 344104751
    0x10902040507030917180d03020a030e04050f070c170c0102040e0c070206300c430c0312080f010911030609040201110f21131e0906090f 60
    0x100c6a8404a00700e940544d4020708400d25100e01118646040016102c01048003a41c40440b594070400301d120303503031009401c40140e88407000c40c0c402c140c0c0045240c0c00806058804001c00c2c5840c58001c0744408010704907a080c025003020721030501c01e07552107680201c0c2000902a07642c070001281c55000f940640700c0c2c00000c8194030040380943c82120119019203070001c05103070a08204504940201d0546055500048850301620303000e0011100075501c41e4504510f0a0344034130104003402079140180b10f220115080701e1003c0180500c020103c140e0340a10710130401030200c0c0e1440c012a11480c1900040c054840c47d03268030400c513910064403846422141006411a40ea40c0020001d031241c0901c5040301110500000300c5600b804400c80342c3c0704d8014075000701e403242110649400c1407900c5103551120741140380404115011480304075140d60421103150b00e4251440e054803440e8005000c0d0b441400c03c840e6079134413648080403050001c0c00e10801d0070080303103944110000c018500301d4210186a03 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 344107248 1250 344105998 344106001
    0x3020306150a170a08030a0f180b09060603060106110a1e140303130332031e0606090d030203040810020403030801050306061305090111030c0304021503100b0306060405030f0109020405 81
    0x560340b2022120042d512034000d016522a0b035076a45c0d1281c00081000402e0381e92141443c005680f94040c103a0078406002c078401e042c403a03600702200c030500001c280e20309945c085c41c00e0110315140064883c5c11a80b140c078052640d00890300806085c40b106407000380030b510f104610036480710781c0c4440182d0081c0c4a4004001c0d804000c1030015207a006c100d8241e08941e901546513404039008000d145020f03140c1050725008030490321000d0001b01400440301c15a20000310810010408115020b81100e800a01e64106071a00c240003070841e10802c141140500d0b102d4100c0e008041c001c005640140528205464040241d101500002d400c83d200076000241c8403c0001164100401c00600440c0d004d000c01501900c01160b000140201030502c13510340d9640e88103503080d40084d202560040c00c49050701703543d03820b1500400040d4550f034003070070004500c104240510340c00c40d991500c04852040c1e00341512641e54030000b8840c0d020300d40c05036406010321014080c1c599010350005218600c2103404002d80e = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 344108498 1250 344107248 344107259
    0x30e01020a0209011d0f10060804021c050a031b0203030f0904060e16090902250c0f0b12010e060108070e03150a0f1a06090f060d0e0a0507080a1a1003020306150a 71
    0x4203a040d1010714841d9951f040c180705580c40b0300d030b8140d4094005000d0750483c610f2001d1000006003100710588560301714401c0d5208066010f000041203420b4040e0850943c076003500000c2d103d00c02c0c01d146541c2c241c800114041541c40c0c07500500000c0c8000784082690f032800c0812059180c080521000000e000040c00ec20030f04030314802d5903000445409048042000540c506458003d400c009882c050048032000502c20a04900f080c00781a40e40300840c2c80d1144148421809041a04100c0240b0b201c4020041c0e141d0f400b100310fa030300404600d0403d0300080d2a0300400c3c103112294014a8541d8442c10812841d44400d400010052989101c01c2100d2004c01c3d6401d000c0300c8803440c5903680b0400400000c5403914107208040900140104401d24141e403181e1300c07204842c20941000041c1c1c204e51821828410184907d100910002d400342c01c0d0445a541c43c22050800284a0103424508a01280c0c102e400840101c01540e4083c0c101c1d00541800000001140c281840740b600c00d03400c100340482c0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 344109748 1250 344108498 344108521
    0x40b040501050603060f01050105030403020708034302190513020a120c050d2309010603020310150927030815031204091d03040b0d0b0f0a03030e01020a0209011d 71
    0x300c0c4041c2c06d021402642050011156a480034000b5000c41c4221540402c81100074001446000c1640c1b500041043c0c00700e600030f4000703416090f03160500410790304402c45003c40100049541d9811100c1000071014010040d0b00000d5681095400c5294001c01d1000e125450307004003070080c659190040d0301401103850209440c0c04002c20300c000703030042c0140300f1402500d42110030581c2881c221a80c0919058901c21951001100c08100b160b440f01410019400e043c0a88801042880000d000d03202c4280881d422a070f01c02d101d0700c0302c1c00d17075996481d000400c0c8905a40e1305604281001980d00405403d0051032000192451580c2014441c00081c1500d0300040d404942c0480303400c924241450801402d0041940d01c0700c0810388000b00740590784104050000380080d00f401140310ba242c480b00305500007103602d2104403901404510032600c00e42da481c0d202500031a40d151820105019060300101c0c1802040c0c00004c1d004003140d400032400010316040c010303070740012440c95400d0b552250380f1500d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 344110998 1250 344109748 344109751
    0x3060504090507030210020a06050408091017010b0d020708160b09150a090203010e1e010501120305180105040504020f09030c0118060804030215040506091e120d1103040b04050105060306 82
    0x1c0050f031002c141000181011101120119100d0040e9414410f207502c5140503510122000c444e0b0700d03000500e4810794684480c50202c0b04210f444c154401e101c411191003242c01c418051901c0580300415144c0c00c10445404603000c0b2031b8000c034940d8517014101e940c456016000f01088400844580005175820b03030005140f803003140796081008540e140c0c41c07140e0004000018050360503540380e0700005904001049142c07550221103140e1701c800c0780030034030701421281e040c0c220b00300c02d28504000c4000b20394420107540170300086403103035211581c5810068a4030701c9281d00c4150802e0020514280050480001d003148481c00c3d8140c0d002600d83c140116603144002c480743c03002d5101402c044c04801d100300c0c24103600c240f01e401104c41c4e01c0204c1e0240780440d201281c00711802d82c800070400c03506410500112a20000a0020b40031006982030b10f5038441c00080305503104500041200f5000d512190008042650701d440300580c5d80c1441d0400b084011800c4500b40c40039820300003c104a410001500c6 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 344112248 1250 344110998 344111003
    0xc090c14130f03031107060f08040b1522060f050612040606031b05040c0e010203030a0213050a0b0310060918090302030d0e0d110609030f09031501080d0306050409 72
    0x20603212000e00c4209103950460041c66a00100d01180420382c40b9520100001540c0a5100c480e0040100030403989085c103140c0042c0b04106040801150054018a00c19003007a884044044c00d90340d8032102c1d0341c01102008034541c0c8903201850300041041500168426a0202141400110746a049605914036144101358001c0020062034003c201d00ca001c443c1c02621500b40440d4070341e0390361610410034150030210400703070300e04e9001041145064400d10340100078a0900d003a40b4054100040e4490000901d025152a00020303003110582c101d50300c91000d080000c041c070407140e0310307a050015181c104890001600151610104500e4001d0300350744115400c401c0c030712018800c80d103070690140400b540214158841445a007501207950302560310211a00c1000701049034421b08010305000c5e100c084c440b20360b045641403062540e0f001c01100c0307c00c410303142055554601c04021070301d0003401c03003c90080760100c0f80001c07400c00c20206152211186a42d8203100480d1114100070840303401c0d1000 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 344113498 1250 344112248 344112257
    0xb0d060f140103180c0e011404051612060b0c0105010e0601080c181c12140c0c090402060405060c0f010c051204021302040b0d060305160320030a140a0c090c 69
    0x7440d400358442c3e0854a2141c064440004003445569a18800403d0300d4205202498980c001803142c210031b00d4000000c514225803c2c052810711440c000840c0d848905101c04000b80b40c1e500807410303059030300f110000f802d50707240031903541c019880300030300a000038050080005019804101c1c103620411000b4017030044005460715008803039100300381c04000b101075242c1118012051481c1c0341e1400d0303150100c25024003c40300c0381c5120464010961011002101d030480d1061048142c010000110304000400540e0302c40c800e81c030342d80000341d510b000c0c5510066000400003080c2c030700d82501068403405d48079118001d00812601d62400e5030700b4000c07295030303500030610100020003602d00f906600a001c1d0f1790640040c5040d440303010440c0150720114100c0591504d031a01001080800c10002912102403c090740140341196544003c02d404150369070200c4aa64050205907a410711407044801ea003c42006000c03442500c082e612901c1807074083d0b41e0200c540000184124560040000c80c170981d545 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 344114748 1250 344113498 344113529
    0x6050603010b13020a031d0102070512040b04030f0804090c021b0306010e0a0b24040e061f11012417060c1e0705070603090b0c090a1202030c0301060b0d060f 69
    0x514021740020b140b841c01c141d01c0307200201d081d40c44220341e9640301345210300240e5106131908140307103811300d00d0800c10411b440c1040708100e0059448142d40c1034a0b03000502c01040107407414404114001c981213007401a1034542c607800a81c2d000610040c158241c851240c04203d605810540c450409114030031202100100140803030a0f10350000c690b202c0d00401c1e5490320820710301ca550038685840410034101c0307400542070025000e42c0c20000d5000350104c84200c08607024103000610800c0d50340c0340400b4481904130030213807124207400c541900c2188840300a100c0801c440700700808000740c0f01c1c005040e2400040700d071240c1404164a4840c2800c21035551401e6014090b2454131038035680d06107100d52041c041d590009109101da40001c04040e9400708014005090800100c5005408101110310400215105444120b14802103511108840e0082c2d016800802d003071000304814145c0c5940386c54808500e40c65100060f000c5031902d620104080d80c0c0354084003c0d07503d401e000b1089443c10352003 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 344115998 1250 344114748 344114779
    0xe0601021209011701030309180207080a030e070905100f17060105010e0a030606090c03050106021f0903090503010c08180f150c04030c181103010315050901110403080706050603010b 80
    0x1411548818504106900b41005400725008420f1b00b0880c00140c0c2c0307880c00c11090040030340740107484a61100c2140360442c10355070341e2154404d1550103414191203108042d07070304105200310341c002d0401d00c0f0309014a00c0c040803070b40000101030060540c41c60982c1c802151550702880406004406a0020001d80c0d08100040d0340c000624420194040340c44a408400900b060007a1001000000340c0414000301001018040c2c81058000b101194495002c509042c0c5008840104180800d8400a04d0000e0350404403000401c1e0b805c0a501982080e95181a240d40109114070410208074443c07050a0181e86c1d49845840e09600690260310070955400003580b00403a10360840342106115150940d00d03603928110083c1507000d12000a51000f8000548410340580106240684011807566040d80d40341e41e0700c010410908029907a0710030002d46181425403100d101d841c5040301031500d40f40d170791410b89000d52007458110356803030507c008500903040500910225510003403900c4001071090 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 344117248 1250 344115998 344116033
    0x316030f0509300d02011b0c050a06020c100c0804060609200f0903011b020613120e030a15060611030307050307081905042f0120011103010608040b010e060102 70
    0x660480e101c0c403400000005540f03010031034038059a907a50000701e040150340721002c060345110b0203210180400308100600040000c01c0b04040c2a074080310050316590310945041c50b0044032101c4a0b078141c58415042e689507004000c5500c242d1081e032042c4211034403001200259503035900c0d032001120742c4000d141224000350300500716841c0d03041c480a007400001c000007402c0d100020b00c13440008100071a41e0818075814170803660301003001610122030362626504d03900d0050141c1e503c1420001c0100c0a43d40c01d90f4140403060300c2c00d8010006072880a0440c2020008100c544504800304500c080c0c080031201c1d0100a0360700c19481d41e1100c2d030460703880000640c0c164000814100300c0704040c8441c04400c600d03510989004034000c0b215519054190006400e686003d01c5140c120b6103903245055406a900400b000c019800300405800080e400c0c141e000e01520040400c18812039001c4004a032507603001c02c813140b096000d104512001d990f14850408400e4041e90040e0058104070554801c68023034 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 344118498 1250 344117248 344117299
    0x110607230a0507080d020415080c09220c09141203040e07090b07030504051003021303020f1305011205011518091a09010504050c010f0504031209080316030f0509 71
    0x1d60411034a412015a00d00c9815404602e6894030030b54081018428151694603102002025052880307050405408140d00f034050842450b10440c0005091202280008030200214820f071009222180c0400e402400d0a03007039000b80301e01039242c007008004510349a40c0f40600e580702d507805946414105030340190b14080c0104640c06010b0300003030018490729103100030608540a40e0396561540d041c042004488000705d44018201401408200010000c545140742142ea0446201030b410780000080340d1480d400c6c0d1130301c0c84410b10b0180002010311120440c0003805108000810440c1103c80ca210303081d0806003e410b04520602d50011441820340d88594056405111184d56180e483c0c5003c01c0c800360200d405030b200765101c000b8842008010054800410001d09101007030504060000780310f4042c510010f07100068200005090502441100010740000c1c420749980d00d08001180f00d1124509070100c000541e04060310140e030348a14155001324500074080100601c0d45580100000e55 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 344119748 1250 344118498 344118517
    0xc020613230a0c0305150601030e1b01121a030601091104060c0c0e0a0c090b03090d08460506010e1e130f0b0f100809070302030d11060723 61
    0xe40c10b05640400d14050211004500c1440200440c0c0181000f1072060704000d007003a810316013130000d146600e00d80841e020314200c4140e0318443c000728512004895440d0010015010ba6203400030051040c0045100d4404d21041a400c40d046640e035405214222122043e00c204c01280074042400707210320407450400100d0103500e20882d13898481c00e584820300b030f0540e25800b80340d07a50aa100c0386941c000e01004000c0074420542421403502d940d40c0c40e180d1144200000c10000c1d200005000290503400c0200041600800348000c10b5140045008414bc415500003600503070182e041c0c480c240303500405109402c182d544004c1d4030101000c0c01965195103c1c101c18a400980074a6000e889607091442d50080d0000003046140c5092040340c111403821300502d00071031200144503c0c689454602c42040c0b662464620215030351348175900e040c14440c2d04020351500071070b0b04107103070583e00c004614111404030090b181103480e9000261011488030000c0e080c40c0d5094040e100005104038003802074a503 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 344120998 1250 344119748 344119753
    0xb011403090601150c0b010f06020c030c060906070201110a0b091902010e1201020c011b030f1103180f03070b0f011502121c050414010b0618090a0209040c030c02061323 74
    0x38821b54424030702c00d50903040486000031200c800c121407941081900081d5001ba0040e016540c010300228104d80b2404900d28025000002c5480c210b911a480fa0030a100d03141f82510402d5482e807070038000b02801030342d070b8417450311901c0406c2d04546130f5400c00c0c407000e42d4140c44c0c0024032102d02d400e12000880340801c40340303155400c0c00001d0400c1001c1c000c40c0b529800800b115050f04140c01d90140440d6181050b5144052070281810900c0e8118000c490300000d00c43e00300501005075550310b5242c030302400709180a0f0700010401004100648603560b000d9100d543c00d080c4260b882d00900c50415481c0d012000c0142c3c00104200d03c0c85070100c00030176156050142c01d02c0542e16200b40c1d4420b039001030302c0865500c2c0352100c148500d84020b110710b21101300103c1d4510320b0022a05040c0d502801d1142c0a41e208407010008140070110f241c2c1103510403400644140014490090064018400e0703130564005402400f00040c5883d10800e000c1480c10742c018605014000b60303044140401060701d0305c814103417 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 344122248 1250 344120998 344121017
    0xa18050406091b05010801060201060806060915151314030d0f091e1a0307080a0e0c15070506010b0c0a03030e01060b030c07060b011806050c0a080d0b01140309060115 73
    0x40f4440050800941410703158420325142c84001050381105078004000c41e450704009018400c0d000c1601d07a0005412600305e00140c44182c0c6034004919a8102a6840441c110340e41c00000480170203841a025005816107801e50b071000564016510086203079410f40180302c20703000b15409408201d500040c146050000305d42c40d103460241c03800700400041c8841d03000d8003041140043c003005001d02144841c03201070039400c3c0104003800c3d04030040c00c604807960700c035403160740e006000708a85042e007040104100720039040440503403419031004000b600d1078001d000004c0f901d844130340111944448440014000f903060b03a1411002000384881049880d501c4000014541c3c00d00c0e00954082c500a40301c1d80d640d40040c1c81e21000701d03000042550f05002090301c14194150000307140c1004c4803550f00340550744425142d001c2e424581690300040c01d400300420a0035410000e580807403a8800c00b03885024000d800070390165054002202d48200d80d40c4218014401d008010107850031075001030400000d003 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 344123498 1250 344122248 344122253
    0x90e0706210f0509100b06070c1503020c0304060903021002010902060306041109030d051c06050607060911031c11010501030b010312110d0509090106050c1b0d06020c0304140a1805040609 82
    0x1035030030980b11001e041d4000d41c25000b00e0354152081e11b180072400c4445074034001c203a54494802800c81c3c403410305102e421110a80300d00b800b030380440d680c00c400031007625983d50316444064240b505130300040e8050003203c40c4095030503005115004030b11390010105404d40d134030034080101406504040d4105510184104100b45d00c0800c0442a2448030b5100c2d191075041400c2e603813810780110415840d40c241010020020364a4000480302c85a4102401146003001800c1248401349140c4116400d481200c12107209010b86015000b00d40c181641c03003030894174000100c1c42c280c0f0000e000160813401070030700420000d880180c0200320040242412883e8945036030701c0c10300b0000d10120302c0020501c001801c040902d0b2400c0301902512079401c0942c00c0490707011000e42c2d509600c000c0c0c200040c58040006009680e901c031005036440d4070500665440708940c48164407a00107108101d840301c81e240f0344580d58030304000a078003a6035200c46080e00480c034a03c1100083d1102803c1510380e1507441146101 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 344124748 1250 344123498 344123501
    0x170106080709050117031201050d08070209040b07021623030f030406050306150412030c0519081e071203020a0c150203090601081b0f2107090e0706210f 67
    0x1090302c004001030070f43c5400f585078442003403540c03030610b6a0001c104a84901c141415284d0650f02c042c0c6480c1c0040c10240b07408070003841480000b03980464032070200820000407200140c4160f040d0f90030303664854641c8103102c00340c02040c0100c9101c0c0030076510180c10782202c0444800c909000074200d070b1140f01c03202c1c4201d085900c00d812040010303000104100710ac0c14004803e40f49000c01c0001a03280c540b0301414040068a054002401c001c0350040880c10b2050802c805003010202c0352040401c03c05034640100203600a5a00743d00309000d001d544034111841500f039450094010820390480f08500008030300a600c00c240210a010403c0003450114020b4021000300302148100180e0703c0c1481d6444c50303e03250050780119095070002c2d2003071500020664440500b4a4240d8030503502018240003d17400c824120288103400100d00d0565007079140001d0020100d80165400b000394096200c401600c4211034020a000300ea581000c0704c400c03503110408400c0705a040400002c0c103200c03d05501c0c0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 344125998 1250 344124748 344124763
    0x1207020604090e2103060f01050c010e010c0f1b050d0c05031216030b0f0604050607020d050d05130b090d03210c03020901170402030606040506011206080d260117010608 74
    0x5994060a00c2c60f102d100e12135440300c0301d40c030701890345811450b1120000b48079051004425042000c0440c1385103540307038250040b0404000302d00080c072445001d03400041201c65054140b0002070000c031400154040c104411100301c1d03801c000a00000150444280c07003001030500d040b0b03094401082265941808412014040c0a001002003084403c0d00802829078a00c030740e40c10300c581c00a0b4203607040c90b544c05048504940003070728000d0319022035000140e5282c18000025080d030081c0030908615035409401004500d2803403401481c0d4035100c0300c801c1041d0140c044000e40213214903000802290281c94803441c150b41021152080c28028241d510660307040b0100704010903000b181910a075a0003003850465003031244040740b11464030780c0009a4802e03014145074000c45c0d135000840c1b000e922030514040740b80c0ca01002071018642c3c1e03081e61503a074414444072600050b007402c40e49072825452442103c00c1c0f03000d000c2800b481d0342400003d082d040644101d840340c03590390340c2002480010074071400c0b = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 344127248 1250 344125998 344126021
    0xb0c03060d0f11100206151302070c0326040612200a021f0b010203090402032a030901050124030506270f07020c03060f040606050607050a021002070602120702060409 73
    0x90258811039002c1c0700340e00d0013242248040d9003006c020421521701441040d0034007074044a00d0484040401000d1001b8421b904000e015410b03c00408030500c5901c0592801e00f0710042c0c0012450344965106003494007403405090000b82404190030075190301c42c0c02031009521204026a042c0e0150340c80000300f580030002040240c3c0002201c210b091080c250000c0302013809050a01c048103a0b000001e40b82d00ca009180380c4201d5010010841d09140d08018943c0c8600700a01e25254503202615440c09400c2152003500d11f6081000120390050b001c00301c02000c400c40c40c0011a03a082010f0260003408004140980210701c481941800c484100f00f150524000712030030982c1801d14032650301d03a5600040105095503c00c80745c2c6082c5440016a9991240402d5420100c030b0300c0381c4c904200502807640c0003661141c008580c407014010045003500f4618400c13076407007803144c070380803400c1c0d03140c8001c1c3c0304d03800168020100001700b42004600811220788000e100518082e01c0300b0140c0d0440b03890300d11a = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 344128498 1250 344127248 344127263
    0x3011b0c030306090608100e12040f14031b1210050a0902030f031306120605041a011701080c04020d0e0105090a03020f030708030a09020102210319090b0c03060d0f 72
    0x5440074940c0601c100c8024056143c41171280c40c0c107000070745c0d65402081c4040030819643d8000d0820080d000c0c442d05541881801d1060707a5141e035842e041407a42914011080a202d01a0703018070305140000f507a14510b10b08804445441c10900c003000001030760080c4e820618000d440c01c40b40c5845651096500c1118907101c0002d0840d620b005140c642407840c02d03054840e80c020028014540000c81d10341b03007140ea9616100381c080c001100d110307018201c02e91085811a0030304201908604031200f10704685002a81d07400b410020a1050300c52300c05080c403413001c00f80c000303040d242002e0901d500101280502c0c1100842d04010700d42e07130700e07085400484400d8820b402c050220010184c2c14000b01d403401c41d100b0019410301555850f018182d110140c043e181c2260303181c045c1c0341164001e002d03208685110500c2c3c600c16488050791202141c1c411220b1040c042008200c11030900c69900c140c602c03503900032420310355681d80e805d00700046501c040c00040e8418500900d0380001030b1992100021140300f45003 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 344129748 1250 344128498 344128517
    0x1020a15051605030118050711030307030204090c0503062227020f060316080402120a200a1404090303022802010506180f0c1c150506090a060503040203011b 69
    0x102d034402180181d001000700a0204010044050003d2400c0d005510802c1c0005880d200c0352400d450208020781d41c00d001d030001000304072840760154082c2041341c2d00780d039061000c034103000400c86e60791008444060740680c641760140c45c42080200c00210342200382000240d10f55070710344240320410721030b40403c11a000000380f03481103062856014215140989205d4114107105483d11405541c0c80041c004201c030490002e001d664030104100203083c166030980d007501042d4148100c54100d0f50450f01040c6450441c0c2180354107107030815070f00701c50500303030b010405150050030040503141e148400d900b01038082c44001806450603140c0301c0ca000c0041051a444640c0150190949800821280c80750040c00c80110040c03030002c00c2141c1c007a10f0100344210a603035a20111601d8090480401722446010b01a28102146540311101d64000118100f20301640c501c20008d46103c0c0442c1241c004018190801899001d0700103107802c80d10080010a00c9071b83e0351031420084c18500c1c6403000040030102e = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 344130998 1250 344129748 344129761
    0xf0709060609060903060c02150f040209150105070818120d08150a0620030d0905061321120c0302031504050f06010f09150905090c0c1b01020a1505 65
    0x205403002401c050410703160851910801805520303081c8809001d40b51512000304102e8400d20031005103505910010f10203060a28804c1c09138001100c00700e000c4d07880302c0045241c08038192201030519405075190792402480341d40e001d030075070421000803405410608810030035546803080030f252200141c00402111051b100024007001c1c003d040c128920301c1414640d0455290a00040c058544c9810960080310b88070140301600090118000384500012504040310301e0141c00c80d0240c14010b03800c0360400e03200c065001e840160180700081481c6403c10600c5c4402d042401c40b01c59040c0b440c00c200761001c070854140c00948a00602c403100082e400070400c000380360b0003034900050040580d0708101501d04281d510058441c00340c00c060601241c43c841e4820740388161310a102421154010400345c459005c000f5041407100e0140d41d120b10802c0c2c0006c0ca150214400780c2c0c4203605e50000415603c005040308036001d000c03020340716046000d034500280110700001d9400380c0c032850507080041c2500c1d103813 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 344132248 1250 344130998 344131001
    0xa03030903090e0405030a210623060f16140706020106090501080d0806010e060c0a0807030e012604030512090a120504050a090e0f060901050f010e01060f0c060b030f0709 75
    0x2a04200410703a4181c0600000c900000183c41c25400681000804801e07056900e10f108c842c0307000310315003441c10300802044041d180440b05950083e192442c0c2d804000040c10054075000300c4841d45030014040c040d907803110f1681c44049180d640101107480885c88004441402c18117150421000340c1e448443c10008004144100d03130040c5064006071120b500300342c0d0028000100907021604001307256850a240d6039903c8201c5d070f623003040481155202071652400c5407041c0c208080540210707801c10b402c00629409542c90b0f01002682440b03406031307806c1e21a140c00f800040038200398100b020038002050001804440b00d070055450b04000c02200306249041c5e8600c8400b10000c0081010603c0100440e884483ca03440075112a034a01044e04507034040035034074094244051210502c01c00c0103102030080c06610550140e81c4942c100640ea80c2c0f00e084072000d10500b03104202c001030b15800715400080c81810800c82d40c500c1382d900809c0703000324140040d217000404210791220341c0050504019a0340b25 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 344133498 1250 344132248 344132267
    0x9150f090609031a0619120203121204080d09062d0c0509090c0706050f071701140d050703170912062e0e0a060905090c03030a0c11030a03030903 64
    0x1c1c82c0c0070080600f141d580c2d43c00044000022030b002e52031080410803e0f0307500c1e240441d440300c0180c6204003055803442c1c00b2040381003c007000c4e4000e00402d103641807481112403c4444169016514031904e494a944800380c0f58420309002c00920703614144100004c059002c1d00c1101c2e90490030440400c8524840700c0780d084543c0e961224650311f40300001039203941280c15240c442c2e00c1115101c00a589482c0500b082d072107540c0e0024080d901d40000c12a01c003040300c00d002c0c000c0c40d07035580313080761f0001c1d04240c42400310083c062410003801c0d88540602c14901004000d07109803094040e900b11556a5984102c110744d40d480341020f510021a107240d260405460100021a1a00040c1074906040d4185000d181600629002100740000d058008800b503050b00f20003400b1040c40c5e10858684079000500428040c000c130b1104a0030000403500070200014141c0c24010000c026510f002200c1800303680c044c0540c0011165109a00b20441180d40c05000d141070300e90180e1000b203060300c243d2038020012402c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 344134748 1250 344133498 344133509
    0x10b090f030d0f0c050a14031b15160e0a230306130803130803010602010902010e180c160b1e06011b0308180118050118020d0803060109150f09 63
    0x10140b0b10050003540000384100508107030500400c456082c0c1003003410304861a401500c000c0c0c0c2004500007140000006000c0a075164205000590000c48031980712822580840000c25289003c40c007410b0308412a01149410350800e40300c0140c0700000300307103c3d854643c01100080a50341149500f11880314850790501c1085000d4805032078802e070707a403484000d40381001e0301403000032001400c00b04204060054107a00504441d480c0e69682030000d000c0c00d12607004a000036124100e00c11641010b000f130040400d85402003011b1ba65840c82d034040d013078001108401c4190010070300c0f540030070701600c0140e01aa07154945462541045501500c0608000d45800d04101d01c2c0707041c000c04410160608000150700d0b1401303a010351a0310070912000c3c00b12074001041c551030100b90418200c2880c10018003540315200a2040000800c402c88481103042d1010f074011100c0c0c0e8038440020090381c011584000141412a001d42d2943c04000502c4d1480000a0104035040c8140440a400100c890020310 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 344135998 1250 344134748 344134753
    0x1606020601051822050303040506060a06030e0309010e030102041e03020916200102090901080a0308070f0c11030703231603080f0304020a081006030309080a0c18020d0203010b090f03 80
    0xc0c443c000246290040c2414001400a001460920100b2403800c1d111504201165100c0c03d10b403d0154a81c0d9081e01d40f03074030851900c000000d03c6400390286124512019002d11f00b03010840c0010340e000e1094109040d410355081001040080d034018090441ca071007000022280341c25441806021100549403c1d0900141194805015401188091022a010310324100ea00200e00007501a000c3c400c4120380c4001c1c01400802c201000290381031905002c1d81d22503140f0744440d001916289140301843d000508525041c00105448a8206a20384006401c45540d6036490f10b07148013004400410f44200c0804013000414564100403810410121b0b00c0d202c1026861a9100325151007148241f442040b0040300080c259500d8581c43d0300108007800980b2401440310403410020441d0340811000304081f80c0010428100c00180030305002d030301248219040d400c240340f400b1030100f510542c4400507003c01030300c48411100c2c005140207011108a003911100d08108028801c00440119806603 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 344137248 1250 344135998 344136019
    0x504051503120d0f11070201050a0c0b0a0c0813050c0f0d05030a05070516141c0609120f080402090a0509120a0905010f0201050402011d010516080406030b1c030e0a0503160602060105 80
    0x160302d07031700c104c0d0005542401c02030b6641103114803d5500c1c11404c0d602624103043c400030410400714a40010349494a03d0f9502069981d50540032803040e21403d902030419804440420035504001d100041c40500041c4114408007070b41d55168603507408500c0313602c00540701149041c20401c0801407c2d80130141c080040b40b4a6040c4511070409509a820380d40c41178510704000b10700e0800060112055a80101060129060791704000d641035600300846000540340c8241c8403850382c4104107150145c0e6004083c030301c140c0c885074644405080050002c100174010054001c9103152201e0090200c200a610340c6000b4a19000003d440f002c40940341100b564181000c100050381e002a040c56040c40c09182282d411249100480701d50084410109100303010030069001e000c0c2080240080354819982030004005280910008905458503402510701000203403000074000c0104040044000d00f51025055a07040040c1ca001c1135882c0082d800015144280101507051200a024010540d09030415 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 344138498 1250 344137248 344137271
    0xf05010e0a1406070f1e030909060308190513080a0b1b03060114210108010c0207080a03121506080412090b0d0510170304081908040504051503120d0f 66
    0x42d110b0112410310652000900b0420405a1040e0086064100c0c44030313604600d400004a1a0288143e02680031030701c2c0013000900c00d030003030003448143ca600c6012281403c0805021075282d0181d034401105000007400710f50040e9084915500c001d00c1d14200600301c1d00c0c12824040240e050282c021110038158404000d11540712008076900500c0038a0580b0b44019a85024441c901880e541d019415039041c0c400b039424922010024142e07080d038402040054683c15003a80d4801c054030801e1301640005000c1c83c08207024540c5036081d2250311b280440d8850705584a140041c000c3c1d040301000c29001024003040c4401001600102c0c441410320034045804c0c100540411b018002c03403000d10030780314400107000f074104c150088010000c406240850840d5008140d413640c21034014041903110740410324003105019003e031041150814101458142001c043c0b002525009012000d190700d034250803015038034200302c1042100700b8a85c0f142d46a2034140100e000b030740c0b41100417510302410100e08402 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 344139748 1250 344138498 344138519
    0x507030606200f0601080102040609050a05181302040c05180901050f10020f0604060617030a081b0903061510050309102a030f0b0405090c13020c070f05010e0a 70
    0x501410b046484120311900d03071240b6181541c00d44030794801d4000c01c40001880c0c4c5054010f441525080d4131400400c0b40c4400a00c00303805210303c240c0394807111403600000c1c0441490021030300094002c1c0c5007151981c00790080743c1a540100721640000d000010b0b40c0c03440480c40c1c00013140c141c3c8100e603040603070351402001030600b95000b1902c40c400c4107251b10380c8540324000c0000c008410102403c3e929145800c0c10000e00400b454070401e0210028040450480701001c02111900001c1c3e4540c54041d07200c404c0c0c00480c00c090001290b4036682c040000c200b00c0d603410004207101c0c1c41341e01c00810880040c10140450260142508006e000052040c0010340c0700104030500d008190020000303600e9068a603203012034015440c0c0340380c200024404410102e030301d07410000b05c3c001e01d40000c0c0a041d2421081c08211801100e60706000e80042d0302ca1005440d1508075014000f40e00c80002d8100b54071009000c0c02d140c2c19900140d2482c0c050b0500300500d5810400300e8040160480c0c0a10720a4038180e0510b8 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 344140998 1250 344139748 344139767
    0xf0604150b0c01060807030812010b0f0d0f0e3c060f09010902061603140304082d0c03030103050f01091e08040e0117210d11070203030705100507030606 67
    0x10401044000b46500c0c25800440180f032440f0444088544d641011641540800b1460b0501c5c40032000100b0341c130700745904580f148105846034a10308000e02407580028402241c030803061644910165004030410400074803003410701050346004a1121f000741d0420345602500c000c1000220380c0b44c5842c00d4000c50259400320000898030341a42c0d071703401094010009648000e40c03115011564070041d0401c0c0101602540c800d403101000050540c41a04083c0401c0358010300000041005040c014100380302044200c5079034400391155139448084c0e40d1543c02034408008242d0010004000780942041040d01018181008010100e840c0d1680c89540603108070b44506000661030340710401020320100d6000300f080c1c4401d0b196650b10340004000d907924080b02500c0901c20312404d10742801841200012092091018514200100f80060017400403025503080000080c0815409624140010701c3c6051050029099500c10010842c04480c0007510345010940f80490502c807854000c01c605 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 344142248 1250 344140998 344141009
    0x2011a060a081e1806011d060d050c03030307030e0709200c03040510120e07151407020310020a1b0b04080306040213060807020c0102120406030209010c060c080f060415 74
    0x2882c0c0da14040000045031541d015041c40d460541081140d90120350030140e13a0789543c1c1036a640b6640c034036010b01d1007044610700758a5000280e02144191401381480d0300524400d03000d55008005038070000e4115003040b6015000710f6107490012141110a02c031000150842c03440030080308070640201803844699607401c2c0c0d9100000140c47c0402103003041503070018000100090b00e10070b100d0701c4c001c00480c1d59800381107500d0f003014880d003a00c003808580b0000351511070304c2e01c44000c10705a4046841c3c5d00c500c4070003c400c4000300054009a14144400c0f1501c41d40c044c805651420400001003409803200c8210200704602440a00010145031105820603000490030307443c0e40f1541d00040003485105040ea45c045804480028140e820007038151140c20150207940d03141c0308550041e41c984030850030070a241c480070082031080d14000c6d40980311141040c50404006103003503031703807008481b030f1322110700045054001040503082003010701d5644960165028800e20349070202c50003281d2890b0040 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 344143498 1250 344142248 344142257
    0x910180608060c1b07030807061107030c02040209040b18010f0509100306150b07060605122811220c03060602030307030c1404090501050f030114160302270102011a060a 74
    0x58840c451110110501d00784400c10550304000d9407447c000495510480040710034078105071940f00c10340d0411060761101505034a82d030b2130701c0d01075a0030040294016072170786a0280c0e0f20345050140c2c0e00ea150907400e1980c40901c00c1c802d154102241e0003c0c0201d2648041d10075a0300c5000c0100305043d0340380080440b41d2040c1c000ca1810f002c40704d0707070300120100c2d0003416903c1404603005042c41040d8202c40108c405c15101d5200075a00c0c001d450f80c51311402010542c44a901d0940784e862040750850f090005030081d0000040f82c0d60000000b203407258902200054804807030350042140c45a84240a0a0810350804100d8240341c1000a034617804000c11a909066903103c83c3c00d0182e000f401d0304050301c100c0d111100d5945d0340b91200074000300001c1c0105800741400507050b10b400e00f014031407a03e0100c481e80642c0302941d61900507058131100d0010400c1019024000c41d031040d02c1c2a00707012a00c00703410303c0703000056010f079000a086403420410024407000b0b148040d003a0340c454200304c0380c4184007440d2 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 344144748 1250 344143498 344143507
    0x3060203250315060315051c0803130507050105090a060e0307090609200c03030103150b06030708070f0f081317072409030207061b020910180608060c 66
    0x1200700110340c4a60364900100220034000e40341c0c035856482079402d190207041a8031415180c050840c101c6885842c1d50800242d00c1c80d00703100324135011039000304840111200c074a076401c030f503518401d254009403140c440c1808030354007880401c0000d10602c8044c4c582072030030505202c0141c00240c2c03000b145203c0e1a050101090075808603440c144024805040b901c4d409100a80e502e008950080228000c03148070510041414040c54900d102190710044490000354110307400c54480711a610030a034800040655900c900b80703000e80756070000d948101d04e651a0580c1c81d140c504000f4180d020307801000810480315811039a8510380054034a6080300140c4951124072215242584d0b502c0c0306400e52200390320020400404100a85c01e01101d12082c08024044402c00c150084e01035034582003004000d038000b11300601c0158406c880c02d81a107601002903c0803031aa507004184000800e03505c00703807000ca084c6403e001400740646020038001c14100c0411015140c007a2441d1a00c2000e0100e01d4030b03100004 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 344145998 1250 344144748 344144761
    0x306090d050729180c0109031a09070f0e01060e030307030903060e1504080301170a0312050604020d0c02060417040f03020d0f0510020301080c0103020918040816150b030703050703060203 82
    0x7140c1002d84160b100703041005080c40002c04d108070308400700e000c3d01c91190000c2203089510070200340c011250b00c80e102c442055400c0030030206505000304420f48502c0349510000f42e030051100d402d0b0040222064143e0554142180201010311141d5200d0082d4020429000002c0e400010b01301203d811030400991401c0c0707254400e0500c02d108866042d036450000500061005040085040380c1103410a01c000b60800500d060f10340e000980d01402040300f2960758100340865400107584084020001031a20052003006003c5070036000061005a0080d0200810006110122203d18840200d40c3e800c0c585000760090254111303000080c01081c1c190100020043c4044c01901c4942e40300d030503591580c3c00c66895000a4009209603811442080c04016180d402032003101ea03400800707000c260f03401801038070319070b035200003c3e204a0f2141d401f00300799240c0c1c61082c1e20b01c2440030300c41d0000c018070000c2c94040030700382c924801d007051081d081800c0801c00210000b6000049a0340040096103981d501c2c07 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 344147248 1250 344145998 344146043
    0x509190b04020f1201080a080d020c010b0a030819080105060403140f0f24010b0415020a021002070303090f0803030f07090f061e110607030f0902130b0306090d0507 72
    0x403030304a401c02c1c00800e11031001110240908443e03880c40c1c0c4803101580e615895184d4811213068043c1854104100b071a03610000d0340c00500c024000d05002040841c1088040744800b005a0310a035400c5402040c140242c140d58801012000404d1a000b4625414800007488512651200400c40d0b000c00380030401711101400b00403050751407041911509411208071030b17295032540264100d1202003610210b00d4540740100b9034183c81418104074102802d107401d0395850080070074a0300035445000d007800300603903903400711003000303061603015040d114554a40900703021115001b11302c8804101d2418050100c001064035071010401c5c1d001e07111a142d2041c00e0341d02480c2d9401a13580d00c01c9219010802c1e54014082414024080b080305d0350310700041a04803221310805070300d00d0f400e0300540e001c40c42140c401d420010710003410600002c1c05040c2130303001519500035034040c400303569161081c8078001c0c5810f00107950700c507900c0005003d46241c2200010300500c1105030080c0503610885200340351220a = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 344148498 1250 344147248 344147261
    0x1c0501061b0c0306090c0501080106020d0f03051e01140109050a050f2e020102070b0c13031106120a050a0e0604050601030201050d0b032b0f0905090408120c0a030c0504050919 77
    0x4c0c0042201d00d08608003250410032500401c0e000c1446000001045840050301c1458811165204408441a248114041c00015000300380820841204e4080e16629580c000e00070415070014011180f0060000f40c034040603a4000340c440d054601007007140d51606181e100d024001100c1540302c0420101e0280450110701041038580c01ca1500c04510313607501540100030700340c041c000e41c111503510103001d01d034580300741c0d0b403e258030000400302000018004240041090802404582082e00d000303503228034203104990560030207450350180800e61070b9900c2154804549840506210f00d0143c0314141d4641040c800241017100010b000102180580c0c40050150802401d6403868003200904110f0802c540b548801c49002d03414007105010301a011446020074240c5460340d500303203080c0800141c8400100260b40340c08081000c1c40801100e0f010041c440c1c03040980480d107030303407001e0300007021146190060320611400300000d100907600d8072811a80041c0081c2e183d58032403006c5035602d024104 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 344149748 1250 344148498 344148503
    0x1202010e030a0c03140c0c01030c026a060b18041a01170405150403020f070e0c030a0e01060b1c0516051204051903051c0501061b0c03 59
    0x4601032502d6030340308004100702c600a40c1d44c201502c00540a10b0242e220340d4a422640343c0c0071071180d00d80b40d4065004511a4201c0d8015038408400780907621094007910b060400c8c18800700c418001b0b24840d40740c0504800081e9806144000800f41d600d0001130b42d480110044211901441d2404580340c0d0300281c000e001d040b0308090f00c2d040521500002c3d800c2901e5201c0c800c6003010b01020801000780c5008242c0c40059480b03145201c3c128544006504001c3c00c191000d004207225500c00c024041300e020b000714465401410440784496050381801c0310740d04810703140c2c011542440860602c42068035005504a04c0028890309294505030041c00e03aa8170401000c03502040900300c10103810300d00340c40c100c1001c00070b10450b03a84042032800c210b5662480d40c00b0560511143c0306007040d01d0101c582c007611070740c116605000e0000d02250480422070341280041c6001410161130780c00d1051900904101080511107541072a4006d4000c000b5201242803540f0003520303b80600c04640c002000458 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 344150998 1250 344149748 344149753
    0x20a0215041220040903080a110f04080a0b0a05040b040305030a09170310050102070503060a150305010608030304140607020a03111002030c120f100b090a081b041a030a1202010e 78
    0x31850725128142504840340f0b08109021942c221030b0504190080543c0c450341035503441810f0342d4001c5400003c242c2c03072002d034104280511200d050222954020005442c00c00c0c000c3c282090340385400810618010221100b4a0400d800d00000405910819821682c1401c00c40d481e90f855801c8580100b2484501410b40340741c1420451090314010021401030890882d49070040ea11038005980e40c81003486aa900341c0c1c46000080e4600c0700d00e92100300480150310b6000b20440c2e43c1d440f06402d541071504800d1598100000b0f02041200241c030340d04e11031001d040074010618040b10080d48584085001074280040300c00b4a041c1c0e050180010940c4da5401c50046460b030800f910b0162040d088110b84192502c40140866202c1c0e00240c01c0c2c41c8125a140104201c503410300400900c0350701300e509001e4201d00d04000100c1c8511091011140b07000d502c0400345c1c0d042c0708600400043d00c0c14968949007141c08280c007070b0400c0c0c1340410700c40e18951b044a001241d69002d01e2040380106400340403100c190 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 344152248 1250 344150998 344151029
    0x6090312050a090b0a0c020601140a0e0403030203150414190204080114060315090613050a02060d0506030c0a1a0304023736090606080c0112050403020a021504 70
    0x700d0b015440b03542e0341401204108421764841410030103c4400711449400b50740408010843d0340c110f50002c0c40d0b20030001c0c002041503130744d4074090802800c06690803008a038001c03081106103c900c1d01074070307140c60048a0901070195030b000d0b042d01c1d5500150403100c0800c0c0c1c00f100c65580e803d80390122401425920000c204840a1182810198400340d400522130701614010703121160005151034020b240c4640038100a45982d04c0700d500c110344822044071540240c12404004d80e4441001e060040312544010030107282000c00c041c10a01c11f030001e5442090081014008844c0200488003424000100103680392110300019000100a511350128414030421120300e000b0400c1d2194410301c10305c0680e880558540080b0403c9642000a440e41007200031884514030002c03001c683c44215801d03038005074680c1c4540f6130400f0b035030f107540100130f41d64080c00342e0652550b41720044900e500c103090020041ca040c43e039002520b64102a102a100e00d41100d0f003900d03094001000c84009107058005101c81 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 344153498 1250 344152248 344152261
    0x603020d1a152b05010303030f1401060c050c060304060b031c12020d200c0708060f010510051c06140303070c06050a0c0204060902042c040609031205 66
    0x10350310002000340c0c42401c110280c03441c0000c900c54600d6201e001410710300c101504007448800c5800400c810b0003148030000c4104681e200f40302c100c140752440508040b0741981142400f40032740f41c103880c41c01c0b055840e14404514006d02200705c141940c0c441c2c44c00b104c041e1220304210345001100c68205c0c0d0b0190001007440100140d0b80c2c000b419800c03003541514807054146103410b1406100f0049500400c0c4c23a07401040a4240d1540105900c002c20703500041c503d8003400d5000d1a261581d1504200031100081c00d2103100c104216541c0200440e2004058518056009003240310341803140740e000d001901c60441429000d00f0031f4401d03c46456003000820004010548040e1030b6600c10403880c080c0580300041203040101c106c0d605d298000340a018041d103094821506e560003130445004100f00c4860440041c0c0c0c2d0ad00400e4014081d80d0343c003588030350911341d0521a07a03070b603038640030760507441035a5134103140011480c501e601a404c5400020b150300c40341008e903403d50080d070030014450301d0141040031 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 344154748 1250 344153498 344153501
    0x1f060806180a091b0305060c16051507020106090e030d1d0d050301030c1406090108040303061a0301031502160f0213022a011e05060f06030711060a0b100f180603 71
    0xc2d0f640655200c251282014071214a0000c507800044c0c219000080001d1b40b40a8440091400005072500c601c408400398440c103040c00c5900710b005805e00038900a004501d0340c24001c120180c01c00da14200410003612030f41c680e50b4400c4089468225840322880c84424441c0314900c01800b95a40c10364540c1d2001c410000c01c0e680c02400201c6450400036004600c0c1440c030100300302d00350000750405190109060040d155540c004000b02c042540b680d070041107c101c00d050b07904004c807044808607101d504602d403420440d0760301c041a4500e1031061180b94a001808140d480b003044c1c010301d05e11000e0346076002140c48621000f0801b15554000650191403102ca120f0301c1800f00d110103001002c20441c020030500341c07043c580b023621040c02c0e1385403106081c4800345e03c601c0d00700704020700d005401390302800400c02a4208592550120b0740c600340080c2070220600006902a411400800c81000ea2070002228840701c41c000404000c4980d0000401d07901504241d90008520403000207100e03039460b8000d0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 344155998 1250 344154748 344154761
    0xe06040303060608040b0a05040c030501060b070623060111010f050c0910020109150c020f0604050a02100e010f1413031103150115030207080f0c0705091f060806180a 73
    0x280040e10b400c00010f4210320410901d40101d03072018151010380c0b40c8140d01d5019217805042a070325841030f20780020008600344aa0030041c55550f10030364444500d82030a0003100d2150400c001189400f1501020818806450320f0307010800342825141402c00e01112401041291107240310680f030581804410340e81d090151003032100c115240340004110820032400c1e200c1c01c240c01000071029400d002e070f52120a82000007405458030407100395070342c400c0301d80e40b919070b041d01c0548207a0032400da050150308001d84104c04c44805414050301600b8104002055607200300812810000c4070384440c0840d02d010703401c80794424070f8008410040d54903030401030148210122014443c2c455001c091580860301c00081d0304030354801c050000c800441040c280c000e9444a441112060020000032512050b158040e00e00b02c6446030040400d64206028032604100140846000e840040300550251080307081000c10342e4071034540340c6419220783d0041054925000080c655410b0413504001340907041e5071045 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 344157248 1250 344155998 344156003
    0x6050405031c0b030c0f010e0d0f020f1005120402180f0106030f0b010504030206070503220504110315040b12010903030e12070302060a0b01200a03030f0536010e0604 73
    0x146052202c110807610405180b60701340d00000301003440c40c509030352580c044103418140641c80c14812130005603240028682240c001c01d141a60500f9030800c0c3c40920050002668010140c2d454150041c2c09030045141d11003400703810000140864035104503444400000c0003060b9641c0c10803440400900d402405444006494110200c030000610f024220f02c60406850b01c0c0c3c5400d0560f003e20003240d11170ba206035000e102c1040300781070742050f1540c41a503070000341100d45242428001000705580c8241c562020b8603a00b8000c0c044807480c0799003000462441242c002030080e8404003c107070b501c81c07102c43c0740050354601011802891f80641042c108205450b0076146010101550341080313025080c00a001a071100c0c002808040c03040e8030140ba07008050510f088032501c089031221507031404c0406c070300040e0088641c4170304040c0c050040b9600b41c00d51444c01d005070310b09414880c0d20340c0548020f20010316200c00c00381030f6010008080d00580e445182c024813401508014260703807100c059604 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 344158498 1250 344157248 344157277
    0x40e011e06091116080403080a120e0610030b0a111605070603091e06060533070803010612020d02160b060a081b0f0607061d030a02030405060a1101050718140a15020a0605040503 78
    0x101c0c52a1a4003080e13503448dc03115154490205811511080031070940101b42d0550260348032081501c5204c050003820745140c083c600e86035030024500e4038038207041a07a0301c401c0525041180a40000e48041e84600a1a00c01003800d101c503842030a2040117840540e1005030000340c01d4a41400c0030305524010750b80d000d01074814050f4244290f100010503c0307543d00c05405200140300510004d44586060f007100c541149000d820300480100c24802c9a0000804111812409600c40d040190079480d865103c44200c8208a1030740c074041e03442c3d03124106132582028006100f04441d0850f41c601c3e880038890318020700420f495006503c0c2480003016500070a00541c04980801682c9000002c1110041d003100d601441c00e140ca85002d00185405c200030710350034014007082d03150b0603c030309100700c91040802e56500145002040f982e4141211150040100389010620350044c0792603919541e42150602c204000c450046828102d00f8205035440041c00e80b0304040a00c024440004040c10380301841040 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 344159748 1250 344158498 344158511
    0x1091812090f0e011a0a0c052506031a0907050d0e0109050c03031309090c15030501050a050a060203040e0c04030819200a020906040e011e06091116080403080a12 71
    0x10020f50b9000074402c0c491025048044802c4000d000c030080c01074402c2c1c80c2000203150000395102410070200c80b0092048140d2251070504070409002c2103c001c000500302049900006c10801428515040c8440d000354805030200c1d0500d8442c004840051034001810401080404c0c0a5400f07010b50200a5909200c2c41894683d01e1170007004840001d80301110a01d0190f01d0701186401422603180295064811180002004559080c2c9101801041c0d81c001696605110800c18404038a0b04814020701c08400c003485856000002c64040c0e902040807000030703036104c102485262065401c01050050086040821002d800c0242c1d010400280c0b10f03580ca00340714401301c2c1c40c00030341d06288141c3c81d440304e40804007500f0041c803440e4100030080c001140074030181019909641642c00000045c0c15004a83d000540c810f114100261009000c01d1006021348460070300e0340c1c05440502c1c0400c03865000000104030b001c5089400455102d0440e070384880c00e20308080c0450703c507250320829041c2801d1 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 344160998 1250 344159748 344159759
    0xe0a05011401050603130305121e0106020c060f030c040504060b130918060207050a05031b0f060c03011703070204180b06040905071202010210050f01080d050a0801091812090f 77
    0x14142c1e080a00014196960980c0062040d40c51710400d80900408001940c5100f01c280080c0307100e5400d442b82c0c80080d6000360710200104005901031400c54124001400f055070342c00044500e05440c0d14240c44d140d4036851b4a00c800f61089900c05030307100b03160120010345160040080d013000c1041200912125540f04c0910098500c1004140c14075890784103480009200e40d0301030442d46004200b00e840102156450f40d1469116501c04c3e42c880311a40383d4407d00720400c020300b202180c68800a442c2030b040c100c2c03841c1041c1c04180107405104241d2440155065000c01c180d034080e54000300203005d03030b075607072010b0f2410b82d036a400c01601c0c402021400156141010b010705200c0b541d10400902d291498411900020b45032440102d0443c0511490002d05603081d01039980585070302c50244c00b05500d08201c5929022240c0c041c0c2081c01024844000ea480c0c00040184c1102c1c6110380c04513001c588840c076100c0e14554407800600104510030780a01c0951b01c070000034150307680000d03062001611030 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 344162248 1250 344160998 344161031
    0x10b0a1716060f030e1608060105030127031121030f0601180e0705040b07050f1507020606060a0c080c06041e0503031f080f06041209060509010f0e040e0a0501 70
    0x203000c2c00c408102400301550341a8441c1d804803001c020072405441200c42c003c0c0080040200c1076001003400d41c02540140281d02c3c00f031080090600c0001094546001040c1d41070401954000300501072085880100c2c1c2021018803200040c10108202c0c00c4141c070300c40c09075420356001139a400e00740c1010318002469650240c038103c101d900041c03140c00741840c6021001c10107018000d20f40c00403c601440001880c10400740034000f101d01c60409058900002c9410600d461110840384240d07440a02c1807003250746d000700e0304039004042130311515174a415400040c3c07201000100f004200500000d1a0307a200040802c0c214021489030003651041d01000360007112902440c1000b5205d42c1080000c14110401800d42080310600303005d6108400740e4a444050400586210201a070303003008040004100321019064215681801c100d110141403000003440c5004800da075905209000d0103400707400303010750b1581c40190b400030010310541400c201116141c0402c1ea07412038140d070800c19481342c210301e035 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 344163498 1250 344162248 344162293
    0xb06041d010911090120031c0504110901030215030601020109120e030f0d020c010e1f0c1505010e0406180c12060f020903031c0603080a0306030203060601080c0a05070302010b0a17 79
    0x16500c0201800e500c00d2180c0080311b0714a0075110760b200401c00210b501c0c04045010b034841030051400241881c1c03905041c102c3c1c0300d040f00c009103d02122030041c001a9101080c910884031200502904d0b6524140140e0042c0b104950182c040d8180109140f541f1f640308802001484064060710721100042903440d50b142c4200b10b9007400341e00180c0b00540c0c0c1c0c1d4480c049000e12000010200c4c091450f0425060519201428031400040d40c010420018440360803411444010985801c02c02585000511000050058002044148c54442800303031480400c1c4c18461107500305114650b15039558a140f584018580345c00c48405082c511801c0710b0a000703200b540c90300380e00500618a0020b0380780d02021224800e03040513040a40d034050100c0810a404090724402c44d946c0c80000c3c6d007034110300400d03240c504000c0c102d904004107031003041000303050035042c3c40302a030319402c201d500c58600d8942a40900080e864242c0c1046e03042c1d10028141c0c040c200c90103403804901007a112030f48058000416040c01c0b = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 344164748 1250 344163498 344163517
    0x602040915060324120213020a03020c07060e0306130303230a0c0504080a030e01020f1c1d0d060b0f060d050708070206040308040201140c0a0c1802090109090b06041d010911 76
    0x1184c20041e1140fa422185003a52000f0200e601030720b06c440019003240c0082c58a5000a0b50200b452054410308000d03000180c0503a041100c1c50651590000e50f031444e00070300804048005002c03040400d4020b4102003051442c5031550030284600349602210500c044849041c0c2c141442c00c02c040c40c0e40501c00312400d843c04140a408061301c1500c0980d424400b080b0440d0451041c0242c0b01c11101040c0003440c60900340700103400c1ea1486100380140719222030901102c040d0044070b001c085a5841c1d0480032045075200f0f40105004550200142c1a4041c000e049031b00034100040900c0792521690005108101a03141c143c207940701d0520480e5240c104030ba000b004107810b10003041c0958010451964600620700c001d07860f10341c0103050503040c103401941c03c071000404044280a039050151591400e04080b90701141080c40c59000240986800d210340b10011355600043c02c00c035100c44049801600c564807089400a141c2d02c243c1189103800d101e00c0381c0c0e1030324242c03490640c2010345044505420 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 344165998 1250 344164748 344164811
    0x12060109090626032226100c02011d0601050411031003030503340809030f1c06090501060519020304060e27070207030516080a080706020409150603 65
    0x221001c00b540d440f6140d82202c0101444184101c12150aa003d00c19041ca4840020307405143e01d440071600c0321550045846421080c40741003031b04d8044000825041c03400e40b96901258030399141c10f041e401488510141c003003a101000800d1310705000040c4460480c1c1050b00c0422203040e025170f5442e02804292521050500701d11020004248100080c64210106010a50f200c0c040d02200c000c051760302e0040109042c2881441150b019040420f03c3c1e030000841000d1441c01d0019509000d080c42183e840c04d240803005c07001030f1082641d13a80524080c05405600700b1540d61168409045500321071109981d10b0b201218680c1e0641c40482924200e8105840700c01180350150208445c0142542000701d0b4484c0c0b12520300d43d40c021240851780200003640103040c010b400c509103c0c0c20960031999000d5201c81e20441048903410014500300b0301a00500855121503103403414102a2086501101c0744c941011180034410100c560028100c40880c1c608000000c01030f41c0e11480310303080c0e086111451 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 344167248 1250 344165998 344166029
    0x121506070b040606050406030f02030d0c0308011205100608030705120f03060d0609051c0e0904050601030308041a0403020304150c020d02190314070f0f03080307030b0114120601090906 81
    0x14106806654015114210101300982c580012804071081a0700036215000f95002c078801390b08003840344a042c45802d00d0400c1401d000c0da1030150103510188034001c64405003180344814414103115401d4105600c01c3e061065a651384000c0d0b170b883c0c004c074030195001e001d2600d295070030308441d070202e5550000b0701c095030381990344a0080050011107241d061720019104c8882c03000007282809040c2c038100103081c41d152500c251090081407440b0715802c1a018200780c00500021034000580c807030440754185801540340d9110b1900e100d01d94103054044070004901418002010b801002400994844141c0c051400300710080c02c5030305010303010300650812074120590003d41407110369028401c034002c042c440000c0c0d895030380109072018a442000d42d90801181800a1500100e100f80107200414000980e41c1c196107940c200c40c4400b030002024166507120700d00a41e405150703803038105030000d48543e85680401544000c3e6030b80c100d804a0016040f0200890f40005034030a80064425081e03642c8504c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 344168498 1250 344167248 344167253
    0xc0603041707060f021908010503010e0a06020a111204091103060f210d030608070503120a08130b0702010212250305090102040f080d0f05071208130b0c12150607 71
    0x495011041c01c1c2c40346071300c41072241c1d004041c0d4002400c00e2240461407115056a4941c01407140c80706800c890b01c240d0502d610301403150000a10800d040350404001a591108900103458020300540410381d1801810b0042c0414194100a44100d9803000802c0c40500741d001c0b843d450a1000702c0311603070300034000d80001c011410b090f0b1110700c000070500120216070003000705551800003103174440c0e00020307220380c010b1003030910601141000341020380c028545018070060202c070a01803a15031a007041200c0000820080b0a0b41e20400040d82100b40302915040a0380024040d501a054040041d6040b00114107114440e01001c0e14114072414040c0e0186c00d03e00c1c04801900b8040c0103921550b4003440042049280c000c040344c010011040104400c80c0c14400c05814220403d83c038000b408410720944000c1600f0540310b0013540840d03c1d0086c02ca6a0b40f00d410418890038810107805041d4030001c200c0100000780017082105002041c0594503501d0f0ba0004040c12441204c0c150040b0050100500 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 344169748 1250 344168498 344168543
    0x203070c0e06010c060216021201060b0430060e010c0c0213020d0e01050a0b0a092007050f0609100b0a1d0c07050d1e080906010e07021015080c060304 66
    0xc22000515204089880a403905d8040c1d030440c40060b19142e0414000c0c00031817074802010203091403003500a01c102481c1650042d80e0380550b100c0d511418010803111030582c0310102ca440c02c1d03008a20028519100a820b01d100104281c80c044c496641c0303006020b080190040c01c84440d050750082c00700c00f804001d01d0b11400690415441080e0907a2261142d15440300203002e92840740401c030380c000503a14030201c20054941403d50240c64807510f0071a0803240020304044c401c8034a0016294542d0364400c0345001443c00c00c1d1041070b05928020b00302444003451022868a552421095090000f07800540404c95044458071800c05000c1e56403003107207516042c070190146c1c002245280e0310300781035461716442d0a0084003100580001c0d0302e203c0c0030303e0940a0440079880c1080c0c45c07400f4280c038a0000b100340d13502e82d010b006da85268065480014683c6108000d8036030351011074502032005020859411900c0040d60151401600940c040345e40d2606000055910a64115580b0f11201e00c3d440070b10403 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 344170998 1250 344169748 344169751
    0xc040b07061e0e0a15020c0a12022503020f1f0903141b1003090203030a05070b01090603080d0b0415170c040c0215040804090507020d0e0102030f040317040e1905070203070c0e 77
    0x654498084c001c7c90858079086c0284819140206c002d20010b2200200007400d0a04641d42c1600e4500c07944000120a41c44420b0001900d13415221180302200355400503019516070a420507101d0030103103941c84078580c846000c00c122071040722480e0001c00544040d6032114010080e080d00c02e081801820014505501d01c10715050407401e000038490455000301e0b00b1a80000034110103c2c0d0001029410480324a503018010070b82901c0400080741503a0f1238403c14803c0f18081081d1540f910b401e0704455644e90700c01d4440c42e8481c1c420030326681e62995042d80303c410002800c03020f07004100131952203090a024890401440b0341c0131300545500b012480a0b214400745c01581c8000d0f00340004501444984103a90195403560002d02038121584d00041c0b0130098980601d04541003070094600d05101c3d04207817820340e9072240340d4001c0404010414090380c002e643c410b440282c0d03804140034080000a40c9401018005c1c0014071050703850380310070791392489901d10042c80d80041d05001c02c0303400810700041d03 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 344172248 1250 344170998 344171033
    0x60106020312190606081f060503040f06141e011208030402061305090c040e13081c0e01020d02030103150e03030c0903030903010905010e0d0305011802030c040b07061e0e0a 76
    0x503c1003050b454161004c480071900000d01059040045c000c00d45107040c450040100650880149a03042031001880e0340409040141504092403040341007012a4008a4602035101054080b525280300c45c2c0441402040203c400360702d070400007040241c087c0c07407441c4855030010b9505180d502d45030f00b80070a642c030060045100100301d99001c00c1c580c3d21034202c00d01450769000340c41c0c0c0f82d500300454030103140005840d58500c0c1140c4800b01c800100b041d4250b40c2401546c5641d481c804a0540302d16000c0c00d030004c1b4480180d440000c2d5180c0c041629409141601d00454098080c001e59601e804103c0e0000d080c003085540c0b092002815003600741c8003c00389908080c0680e402c012417000806d0940e0b03000d00045496035107448400741064004c100601c201c02c0f2601d000d1240e0b501d440004403a2030403005404e85100d80000000b03c122801c281214010041c0701e003526a15044c50074110010102807402c0c112040d41d2140b000700802140c01200349680040d0040d08180350540c3c2c421158003c00c00300c1 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 344173498 1250 344172248 344172271
    0x71404030602030406021201060e0904080a02010608060109020310171504020f04140402030c01030b090a0902010519080105130b03030306090402011103040605210103030c110105041a0702030f060106020312 90
    0x200006220b80061400b851048501586800f03015622510007603050304520704000a101c440b00c4a9900c902459802940243c0495958640f070981240940115000084903204100000401e00650350045115204004080c0081903c440704100c1c0d84000000741e043e6640300c850300307000381c2e00182101c0f50487e1005000e00703d840300c8071003c201511041891103100d0948001000f0540c2814044407140b80302c24a42000006071034400106004409010144010f07a41c41c54401164007035021a01106040340c12200503070078006000b080c000090182900862401d40b800209007603074052581002c40003809141103607680000e21409080081090303042003030501c80c15110a2040c0001c0014052a944541c1e582d121443d40d024001e40404001034100c944000400109900c036810400c0c2540c455800c010041040c40100c41602075500311140d04845204040070400000c4010a2280e20a40a4484014481007081c2d1242003d20505c80075030800c1203040c0100c49182e1280b540310621400c1e = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 344174748 1250 344173498 344173507
    0x603150603051f06021f05190207110d0c06020d0207030c0e0603010b0a0b0c072301140910081f0e06060906040b0d0212010f03080f0f070b0907090e0102040b030714 72
    0x102410f000c41e940d200401603041580104819061031820b0b5002c185009001e100c036090201c01b2080c001c6500c00401a415400b00d559010043c04400c10172004a00030012030405240e0709190344200024030917840540724110804000a001041c43da040303039041035040d041c09286c0419400140f00040c500c50b0701d5507880401150a613160305004001c0c089010001c0c0e01c1d64035219040f843c0803143e030400c141104040b0745401c100040140c1111240d002803a20f850403c12a20300b62625000c0c908804c1e41c003130103e141d01c80d51198000c07040f41c46400141245803550360a005c0c03640031940307140142d00340c0c0d250200003e409403c10784024000b091f000743c100b41c606030b80c1e1054110755811807481a610140c00017040f1040300d1843c10030fa070141800020040c219840c55030f50702c1240c404d84100d4640c01d030700410300101101c041e0051301c0c0e040c1c1c4c00075051700032480c1c2804015140d6000c0d000740c4001c0340c5058040c00c04840f0501c00d44090750240c0d4a4585592940c00e41903c42030394001000c0120b050030003 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 344175998 1250 344174748 344174791
    0x13030c0227010609080106090b0a1a0706020f03070801060314040b070909090b0105151c0902041d01051801230402040603080a02010606091a0a030e030405060c030c07060315060305 79
    0x80440e0b00a00c01036403000034032810810200e09495140c0d0001f0209818440910615a10700c54200211140c48807864082101c0004810450043d004040c00142c400b054003144844802c00079441801c150b9a4140e50307a0725040c081d0708481001c100b040809255000207400541c0c05141250000c5080c01d1031104241c2d902000000d0301c0d890380c0103c41c42418200100801d0030702e40101d003110380c103410303045060070f43d4801e14104529030710012508440c1ca03000ca013400d640395948502c4e0076004844016a40b0f480681e40c903806410306907089000c2d080a0690784075000410720034440c48028440504840142184004011250241041e64800e607113060000020380040000c10120b403483c3c0011807410b203002c0b0040c0c1781d0f00c07881d8080d015a07a2503130442691003805c1c0c01221100d00701824002046a01c040c900f506e98040c1e0382101d50080b000144044200c40c000003d415410130f6041119403890f11080d04400783c5041c0001c5080700d122001040c130805000303801099102e032a40108003102c0b640c12 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 344177248 1250 344175998 344176069
    0x31501110d020a23060408180d030c0c060e030d11160e01030506011a091011010e030d050c040302030a02010c08070c030312050711070b0903120a050c0613030c02 71
    0x1040c0303001582c0000300b41c000b0040700b8400c109201c090100d0855111300c0340e84606440301e10050000340311000000d1350301110004800450485400584140501941c914001c0c000d904c2050042d90840da80510010700705100c5d54200443d0700001c4c0c007404508480c040c00b81c65001d0307002030392255800740e560300d5410030f44405e00c00002006a140700f142c495155040440c00d0030300603000509400160782c0e0218015496504452000905403080c60042c018500111035220080c4251100dd5003021651289100008003505103681051000c00903074840154031100d034480c03884001d4040d002a048000550300540850102500980d10309281400c00e0b82c40e00503403100364004a01007030300c0750f04000944d1014030400b544503603141020507080b05c0384145590355500601ca03c60320000001005400c54606200405607440c0c0d02415640720040e002c4007505ca6000f001d1f1405c0f60b8401c01e0002110f1a00c0c1282010203e505070712007803421240c540174840b0109001d0410f415a0751500040703111190310 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 344178498 1250 344177248 344177263
    0x90e0a02070212060f0f1f0905010f080c030a0201030902060f070303090b090f070308030717011811040f0302090a1409010e19081606060b070c060f09060503150111 72
    0x2106006030354400a01c10098061401c12110803c0d40c0020100300142000041a54001640f840c45182540d10344500790050b2010489010034000039010000303247c0b5450b000b10307042c1c030001a80c1c070030500e8a4256181d65078080742d4445600d58000721007400554000d074041507515001400092420303a80d403c000c407260384220380440000380d0342d059400500054451140e0007075201c0d4050011882408101907a0303a089000c00b815040e00000821600c81c001d4802c41c0340e810240c07680030503540c1e483c0c041100703d10504201c040c03001d0034440307268248100441203d00f07071040c2e200142a0182941c09002d62100c000b07254407085651140b0344000400f910522510546014002007400c20004580300e00385040450500c8203203603407040050000f0b41c1c00040d00c2c450074080d004503a49408070708101014290300c0c0c0c071040b001d240005060782404a41c41c4840280c81d05a11101c0c08180313240c00446a0b5880d40c0300d00000100d0503c042180c1c2c000d9a405441c0520701450400c20b5003a0300b043c0c40e03041160 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 344179748 1250 344178498 344178511
    0xe010f1719060320011403040b0a0f0b18061005070305030f1504060305060a0614011b1b15260703020c0a02100302041d07020a03202a030604020a0b0a090e 68
    0x4e0394044419071b800004004600390082d021811420969114094420003401c0c61140e43e03105d51603003850101e0303640a140082d400410308101000d0403080f414440e20280c0702c240c0908405034805100c1c900170000c4804199140d03942510f075584400103c0981c82c1c0241c0500341210308407080440da95a64010304d0059800340d800b800d070a0400c0b0401e0411a04681e021200031243e07881610300907a00b10001031500300d80f280c1c40000d050014900700003216082c1000f99450050b1081c042044502c04071088203004107600c5d0a64202c60707240b03038401242c80c948134880c0403808900c00900740c14801c1d00906100c2059101701c411440240e8005120b81c1000f00400d00065408601000510300c040603c81440c0c6107070301168854142807000944070661184090207100d00b42042160041d82000c29040c0c00789050705a4442d1101004100b502c2c9040c1201c0381c0d004001058594010700d0082841030040d0790003800400b019140822024654100300460024088101c00025000c11501c1c0e50038030034003 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 344180998 1250 344179748 344179793
    0x20d0c0b07080d0c03060305030405010c02120a0b010e0901140c0d020d0e010e1e1e16062d02100c0509130e0105010e070903060b120109030e010f17190603 68
    0x204002e03c0ca00445001d035400304105414040308001092000c002c480030340e01d082ca000031510785035001085101d0440900903205105008990f014042e1400040d410f0707490100a1080702d40720b800f4030334241c640c8105070082c020610b034080b03501c00140d00028005001240c0c4c0150402d20019004800c90340c104400702d0017070f5101d6684841c140018071050b8110214119600141d1210070341c0c2c0c5075501d200084c0000d09030441102c040b04903400300140003090701071568601e072058a400c8001c3c05070408039a581c1e1001103a0031100c00000300300d03000c10540d065542c02000d07003004d10100400038040d03503140311040c480200400350303103921800c0d420030343c1522242c0003142402080714078900b106c0c0c05921951080c5054000e00407400da01038881c0046a421501c003250401010700003032099450000c00003003e44ca050102d508250f0001070a0380ca2010907221300340d0782a02c1c100140c60492090070703914494013020000400101d15101c68018401110100050040d113036030303d44041c144402400381009 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 344182248 1250 344180998 344181007
    0x901050103030e030106030512070201050f07151b050304111c0f14010c121109062802030405060901030e0f06010e01080610030f080703021614010e060a0903020d0c0b0708 75
    0x54009881e0500340f04150000c00291340f0395101c8548030400303c40356140b0a0800100d003800e5a116000761030304882e600038800c1d581d24881c07501201200d400e840c01c1103003908042201c0034020804032000c0300745074035440e1649199590340c1c03580302c514500000310f41c0c091902031250307064105044071391507803a01c2034181d1117a500b5142005541c3c405a030900c41800d078107001c04408819407250000d07414040a01d000300b0061590f8040c10740e035000d030041c0c2c01d401c080c0c0450a000343d201400c111400e03840d800c5644015140c0244400c0b6100e11070340c0901034011008100c4405103501ca81d122029081c941016118940071580c0c007541045030a03401002d10309850001800914014023070541c000704003400d40f41003a403441da101002c1c0201f0305c0d4090600f40000c40e1510600d8000c0c0603001c0000900c5000814460311111001c4032500440616030000710082d065803000d052040c120b80b01c920040d11400d00d050701d9a400c0151850041d0400c840c8032540b80400075003180d52801078441c0e1846000081e466 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 344183498 1250 344182248 344182253
    0x7090b041701110405010e21151602070b270a061e080103020a050d050c1906090905010b090d0305070f0501020304061107020901090e072705070c1a041104050901050103 74
    0x79100c0c4000703c003c42d21400c10003003105070f801540c0880d030050141c3e103819500e92010704201c000351400d09045041c0c0240300a403080090f5840d04140301b00340700c16456010b4194044120780d038803502d0045c0185004108418a56401007082e42c0a600c0c0d10100d8020000c261500855030360401e0f40d020002141003420300c403800c10341c54810f03020008020328101100b50302d960000740c0764090a00c542ca01648840e000041800418080303d00300c44406020001071601c9040c0c1500c041c442446480c0004403d13590108244145000b264100e0300c540d00c429007041c24140c10041c810400110880c01d00808200c07180c001042782500180c402e01803000182c5138540390410000392407140041400c201000c00c500340050399503800f5641500c5032500002100c1c04101c80c058a008015044003402c1562810f0713101072401000d80d0303004071b40c180719801c0c06203441315042952079440540c0b00410258240c138420941d007981c4440716a0090049500503540701008000c03804a0b881503c0000241c1d4480005005 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 344184748 1250 344183498 344183501
    0x50a051b031b220c0e0405180c041a03070603140c0a0c0b0411061b010b1906050f16060b1806030d1b0c06020f100216060507090b041701 60
    0x10034825405401074090907040046030309004208244280707088403a02e48007030051160800360401411003000003582910020f454001807945003482241404d00066982215108107100200e490b401001e09400c00130800010f040e2694203000100458003030f101c4039983c20480344004005948002541c40101485202081e01c028803030031803c1030802854141e294080c0c00c6101481e0440d8038507110f43c640c2d140c60400c4c003c0015040da0303c0390b001b00c0d4844514521641070089012900000c01c02e4078894000d024254000c1e038849440908411070420900340500300422884443e032914600d81040002e40702114081100151806981d030118180c00e0b04104043c050f00c211402d11103441c41c40c1110000e07a590000d5490740041000d4007100c2c1c0740d00c154000246558a03440301301080c00e80d46443d0700a643d2800090300f090030344074001040d820441c040c8210ba41e014191410486c500d5200d41711140070300000b801610800a210500141500d00791001d4000341c007400714641e1801a1502d2100e0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 344185998 1250 344184748 344184793
    0x1207020f03030c1b0a0204020c0c0306090c03071802090301050103030c020f010806091f030b0906091e03040b0c0f1b0a0509011211130c03140f070e040f09050a05 71
    0x403030754410028855000c101000b40e4061503e8082d0f24001d159074115000e08044504000a42042c00031070107030003006002ca0141d08400069081396640d59480c135800d540c9401c101d08280e050b800014040c80036100d0032134401035801a610000d40703010203010209085441c00d90040c3c3c00988480d00420862605081c42c411240c02443c2102c203a040c03000c0003075400a0007600d10070154410613100c0c008454025907850003950451451682440c003164810303210a001c88840d0001c0c014502d02d00da802c03400f0380d0044500c0034010029414642400ca03003405551109101304803900c908910a80030850030032249540500412510006151a00500250300e941d17801c40e0748180c01344070060041440700c40504d2440c5821081c090050549440461321030011015200c002c503080451744c00c0382e20b07016041502242c034200703405141b994030000f41028108082d164500000e010f50020185850503400c620303c000d01c01c3c0400120201181e403480e213440a0100c0031500b03a00304100391510101c01c6403010 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 344187248 1250 344185998 344186023
    0x213150c0b01060f1215120605011509231519081803071707020901080105250e1002070b0a0e03070501030b060f0f090402030108030d0c032009030111120702 69
    0x105814840c44001a0280400c40701c1707164005e685491700072080e210000f0140080c0f01d0a5a515a02c03070b42410000301602c800d01459041b1030001545040303481c49220101c0448041401c0c0f071505030000307401c1400c401c080c21300c8075074821a80c200203042001d81c00c0c018042c03040c18248a05403082d01c03000141101d50010001501c0e0141e49a0341410000c0204c00c4802c01c5503c40100144090181031202c818055164040d401005441c0040340c1c0000540c422401062a07081500c940e0346a02d01c01149100d441401d40001900000100c04608100001c800b0000580c0141c4242d903844051024058100f080704200103446088510640e04090100f170380605002c1c6400e00604e440768022403618841c5007211203400c0c80c0002c0f030304c0c3c200e00c54100792641584010425135803541d40f000956503a0704881d0310141118035181c1981c83c0c19000340718440d0700c42d19a000300e16045d20024113194050f00031141254055480e2a0380c5c0c0040000302d00100344d44a240343c4559194102228000e190020300c80b0345 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 344188498 1250 344187248 344187257
    0x305060a0f05012001020d02130905060d03050f030402010c080d020a08010b03040807080a1119150b0a050f15030108250f0b0307231803070308040501030213150c0b0106 74
    0x1402070380d0f4400700500b181001380f4100720710b0144035184c0303a0085c0b0030340c03d0380e6040a2001c65001e007401e0188000030b08883d503203a0280680d0710380da01006552902c03484000e021600c00c01c0340d240c0d05d211600c003441d8810700506118440000989400c412036000510f0862100d5000494544094000c0512400f502c8071180c0c8905516041c4d690a1942c03048407806400301c200410703600c0c21a482412198089440001aa620810800110000141541011150440c24014004000203e8810b81091640051020726028504018400c0e41584c0050b516040031040710903003400e00790040114005c180c51002801001031601c12007102c2c0313042031000f0001d14003000c400c01c00d00190042040036200198040350f0340c2d45448000340c2c2d00c0d482d128a005200c00f00580c281c0500007064024006440342c91001ea0383c0038001c1741c100f645884c4d0b14000100345c004203020600542d4401d0340548915450b2004c0c00b01603039190706415002524400540002940300c1c001403003005a0312120b1760041c100c6061 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 344189748 1250 344188498 344188529
    0xe030c0a03051621030b04020703020a02100302210a0608060907360614031618060e0a05060102011a030c0904150c0503010f080d09120606090204060305060a 69
    0x111500c5665680c0c000d01000004a203055140b10103050f00c00c18603900c01e01100c03000002c40303076401c1c1000c42e0b03903400b1010901e041190303515420180200c070301f4540d156000d0300c0707600065401c001c05c002d842a458020558213010801c4100b80c5000150401c0c407040d0b840c0360b080d20740010034005641040d0080201a00b0000c00e015030484009482d02c240c60501c80f0160901107032840c0328103c0c0c51000409010031090180c1284007200070380c000d60035981c07916000075100800400f81596003d80120100000d481c0440c00c00c0540558800352407038603501d00c004240305644440f205d0b803030700003034510010441e610340c2400030759a0244101c6500404003089008e49181d000700203502e994116035054081d0006a0010701041070f600108501035181000810443c240402d0041a94100340101c43c84007908600102d003940c00080c001d810301307840e680c5120400b400c1c40381806009000703080844078036444400104500d84980060301c003610266030009402d1402030104110454254020102e407040300700c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 344190998 1250 344189748 344189767
    0x402240c010b0910051509150a23040b0406140708040305030d200304140f0601090e0c0a08071a09060d0f0f050c090411070212060916080a11120109080306040e03 71
    0x10001084100c03013104807074503407035400c001c00e2000e030381100036071160a230004800300020741010000d0184072400d0169183c01324106907910442c03003035004000c0040400d100400c1038a210301e0014400465800303d450030940c599944150755005900110760310381021903840d03100d40c402e205070b05520020244840d125495a10034404520001d88050200e101c243c1c0c1481c40200c040191542d5239050f0000c848503581c0d64140e00f0014641c01c85c60f24018010580c4510440c1380100c220000c0d5001c01000c2c00c02d00c1d1421703543d110108411181b4042d2072400740400c048503660503016000014071800b010a6080000880808841600d4a40e03803515180105105081040c04292920b02c04151000210030500741c800c11558043e4080c000d5011700324000500a0382c40c04100c00b070141c11040c0440d4090b141c660f2816940750301500580c0c3c0d40d42d0103008440040b415214a2504a501c081d200d84e9840052008140c2901c1c50303405c1c280c68000340001404001d09040c07144041441020740658101244103 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 344192248 1250 344190998 344191009
    0x803210a061d06010203120a020a031103040209061011030c031206030d0e010305060a0801090606061407031d010507060e0106030203160e130c05120109050c04090305030402240c010b091005 83
    0xc1500b181d020900781c0007400d5a4005c2007140c0010564110004a619140003414003a40c000c81e100d90029050a031800b4440c501d0405176402240d004040102a541e09003d003c0b0742201c80c078581c41000f41100c1010810181032004004aa0550000c2c595540f40000c1d080d0203501c010308994000d903c16040c649119a00007400b95501800b445e0105258940300000f03228246c01e82c0108415502c0e000c41101005550b03400001101c45e66140d242e85882840d542e00c0640c0111400900030950510382900c034403450140500b00f0070300504219081c481c01e6202c26085030185141068580c0d541c15082c0154030707040001c030702c529000f810b43d00103146c14101d0403008000040d0031840c110741c8121400c02004011002100908009800b0158a5080d03140645c068001014182c403180a034000550040c100341c0036000035160117465131441d5450b10787c248600c01080c81080800f10030042040c110b245988002000c80f031038030000200b04000002d040002c1000c02500c40402d00564600800094652 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 344193498 1250 344192248 344192279
    0x603330306040615050a0e1605030c04060c020d150e0c060421050a061107150203061005130e01120303060801050f160201090206040e0a0b0d1106090a0803210a06 71
    0x1c20804a04d49a0503d8070072445803494100702d0748450a5000410b0b220100d80e0454030800202d101c1d110981001c2c98280c415200a0f00c40141c4000308100030b000250181c1c0802c40040e03c090110010200300e900c406401d100a01607a044030390325946c0306071480702e041101040138042151803525152500c802030306005541e505800c00e0300d000c04072500c14400280220008150000b0080c0074000740d1203040203065201183c11a4039110a00d0f41c214031808a100f40c81c8035101c01707842e2000c560113160056510350042e072075910b201c039404c40011030701c148410341007802020000d0000030440190311300941500c210390044082c50389450104100200303c180226000407079194070054918141c0010ac0c050611004041e4201da80010f00145000d242d0314a20b10070301c074a001c00c1060031072030006c0002c2400d012001810300f12030950f540306640340c50070003003180000c0101511800c070b550703501c02411a0442c1182e260f0885a0750b0140401d8101000540d0f400a00c1080030003c090034060b500080668 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 344194748 1250 344193498 344193503
    0xe010210110c010219080703060807090203041b09020d1404050d0f0908061006090e07020a02062214040b180f0a0b04050405010905010c0e0604090c0509060333030604 73
    0x8441007045a800d051200300c4504450b984000e40d5a004000d0304001c180c60040c1c4038200258090000402c068424455841074440080190080502c1c289500c8060340020703009032015441c0a0380c00c240741c0440c070040030040c52489809030311030b0b02d0500b0220488070320300c500b0542c40c0d100100300f00006d040490300314800046400d10010a8104000442d80003c85030030100c840e21440e000d200800780390a5544007101e909a40700504036455118994803424140ca115026a000664417001860804050801e491000710500b1203980c0c080810468419a0340c400e808400000648182d24140b500034101d0080c404d503221949220030071286142020005c041d20795014080000c00c004007002d402c00140184010001e021310300705130410754001c0035400b074112415807034103054054150149580e1900040000e010301e042c0340c68142484040c00240c40e900d0200501000105450358030702c00914014017030703a40b2504000c81c66620b4182000150b814101c2003280700c500c0c0b41b030159400141c1c2540640d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 344195998 1250 344194748 344194751
    0x4061d060a1d03130e25200109290103050a0803192d0c0504050d0206090a180b03061b07111f140408190f02040f0207060b010e010210 59
    0xc8140b40c0402d02c05880071141146400000380013104012852098000d6410f4409420700c0c64503842481c40080241d00002c0e000d034180d008241900c603024074081c002451a0000c40146403086003030047c21559049400c0710a80c42e15001e80d522540b4190007a0010395902190810550454680541c2e500300810300801042c00000001d94085202d010004001c5040c4130901c83d00a41da8595829620180b90f940d9181d90340c520070142070351b040d0150300015040707602d8003450141408240004d0105d50182079030403000404c03811446484440d6040014114200c10301031140000c03400e5000e8a00030b5071120b1007a4010710074040384018102c2848140c0310003055440c1c0eaa00c16240641c01d43e01000f2805500030042035200440011841c0c0d420423a03030455646198024103512000c915005501450915074456072403071a0501e00ba00c091003070b10b800764a100c0032445140d8002402e44603540e079094203054003c140c3da010000b980c018412260400d09290610700d0540f40002e6032850241c0c201501517 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 344197248 1250 344195998 344196011
    0x203040e04080405060f030a0c08071b0302121306170106050412151d070806040803040f05210d05010504091a06130216050609030f180619020604061d060a 68
    0xb01030081202d008002c05080c203601c0c3c85000c0007005240d00211003807250b190900c018035071400c2c482c3d418984a851a41c07150a02107180000c0940b81000c00741301101036224a0801c022220124400fa00c01c6a600400383c05101d404c081c0b000300703203201ea43c0510381c245043c030300140304060f0440103a406070f03014050b1081d12200d01e82094003131a0114110549114035141f010f03c0c5000307050138404501c908100480784901e64034031007160b60b014120b5001d025982d0500110b40050201081000d0841c0228100d440d1148503003c00482d0365518541c40c00313044000140030844ad0743d00c0c0207403401010201c0c2c003000706250907190704c040029041540e071029050f030710000e01c490341d4109084d142d031020032030b0464403a074440d1069120046030b11000d45192190707400298901d1400000c840d039107894140790a080c00740000080000b0030b8401092644024103001344031111310340020b401101d070850380c0102901c0c1401c0c06c208080382c490b04400d41d00000c0215002c0100035000032600d820503106940003854 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 344198498 1250 344197248 344197253
    0x103120c0606170106030b01171b04021207090302012a02040e01061206142508040201030b06070303050f0a060f060e03121b010c030b130b150c0f010605100203040e04 73
    0x50410341c00200c03180099070050141004154005d0040d6445108140388590303ea0042648000f0f1144900c0b0705980040403100c00f0b0082c0b5101c3c61650103016001500303081e207000c00000400310844280300095130100c010010342d0313800313003188907668044500a8281d04202254103454000e030701011380103588a03081644644030940c030030b07801404464440009250076207880c1015000141075420a2003a11010815821482d400700081c0300401000c402da01443c440165500e10300180141c0c1816616400c41c035490700d49100a0030740740d00c65500002d140c17800300759013102010f002c0c02e0b594029180c58414003841c43d00700113039400e5840380e0400e4a520710711180000e150203003280da40700210002141e0b5401040c440007249950281c040000d020209107050b0440c05c56014440b841e51042070600070181050240d030244d00700301405403407030244d0110700f5a081e000d40d0015010100d154404503c21410480c03c0c414440a041d00700c4010007058208080255603018500074000a104c014001c91308 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 344199748 1250 344198498 344198501
    0x12180308090d050706090501020f0c03031e070b0a0c110a03091205210c06150a0e0406020c0d050c0c06070c210507030c06200607030c0c05150103030e090103120c06 72
    0x101e02c3d4410308a484107078880d0300050907a401c42c8a040e02601c902060090b4448000c154864900c074094011414403540a8240f4000d40e010790110141641c00c12001c00480ca1742da0341e0343c1c032a400c4e46401143d20b03004842d0040c0008508164600e00e83c000c0c08484000aa000701d0020403a603145445014821345c0341003050519800c0c540b017a4000c04090903142d0700003042000350015040200940d0740a90743c0b484d1140c0100001e04026521003003840f81480003c28184400e50030070b018020060504809910f524074007022076180b24041136000c103036940c1d000420044038004603400e480d03142c1001010f94503921600101c2c0900006201c202182c500c0b61540703140ea10041c41e4001c411264090b940b820440e032218100d008010024101a004000401c000780405a00d91656402082d1558601e03104800a040d100e00340000c01c0b010700c0c49200030560405c00714003181d8100d0381c0344409514518000e00003c49494400d4098502140101f0100710500001000c526060408080c408250f2a2450 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 344200998 1250 344199748 344199769
    0x12040b0a0b03061602010c050301080c0103020a050f0a080402041805061504200a080a0c0c0314130f08010f0b090a05060109030b0403023004050105091207121218030809 74
    0x5405115103c20000259003001d07580f801007070150005c00c1200c5400b103048030548000d01968200e0b621854010310300354841d0f0b0061108842c81d10b0281c1c100302c44442e00d20b0080d0301081a44e00060130706018041545054402c1c0a0480c000c08a010303003500050f0f8406c1e0b00c4250041446049100e2000020300e9070316136401059031705602000c61044510b00d9014800c80c3e4100d0805840000c8140b0b0008404030711031b00c01c019000b50203840312002c0e0445950300310f40481380d8110300c20500304180415500010500c48034806000741e05142c06140703080c4110b29007100c0030600d90b100140c2c00d0500807200c83e01c64100d038942001c6841e82c0422035a6690005a174500c545600c02048c0c04403500410050590216600ca052000b61007951202401c0e0406049a25076840d4a000e841a080004004943c01080204114070000d8030b003101c0791004502d000d0a04002d030388480c5110300034078250010030030407880340101d2450b2070820408415a002c030405007641207000007003041a0021300c000c155605c11101c81e = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 344202248 1250 344200998 344201021
    0x180301050f0a0b0103140406021e0a05040503160b0304080f0f0a170f060a1701181410020313020108070c02030a061b0936060b03070e0612040b0a 64
    0x2488607080629418032889021146404050301e00f1401110662082c003400c200c8591340035082c420740e126515401c0007540a04440d10403082545051807048084001030180d001e6280c80f030540300d510700303024142040d150f00d8060809039015038003444410802070540350010f0300200c40d46d850300e1408411084502c04c1074903d45040c0700204106000b2640000e040d0b5484180c000f00c0380c8580c58080180a180038162941e581c8540700d41020300010310404056445400c1d06c03400459403007145c0e40049441c205010341924030091003201c40c4444281009920003543c40a0011403071458003910407001140c91a0000f41040410070210314814400c0e82204e60054009054a99655852a0a20003401511f4149100c40c031248500c2c02d096001d6010b103030494240c01d000030030181c070102a00e4405181c9800440c0c0030031491200c881c210001344030340c03409040c0c1408041e50f0b03801c003014040e0000504201da80c2c401c000420480d6007022200c0c041d135402035441071035201c194980c0303003050010340303000c1888 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 344203498 1250 344202248 344202251
    0x509150102070f030602090406080d021f06050a08160503160603090201030b06031806130201050d11040806090318060a0e040b12330708160201110414030d1b02010302180301 76
    0x4002d2050721b40c01880c041c1012034003080101e682d64405616001842136020250f00129242600c406203c05120600032a10340c0001f502c580390070004291406d036400c40400750388414101081e500791100c1e01406404220300900081c000d41c0c54640c00c0c004540500d0f802c150b1510340c4002164002d4100b015400401000c0949a1921502404682d00e0504c42801ca905c41c41c40484e40c605000310b51201401d4060790f9035860f003d01c01c541d00c2e003d0000c8041c407550a400420000400c0442405094000c0c05128003a5130348602d00d901003200c0d500b600b400c0d648140710402204594941002001c40081d90988020030502200b80c00102804560405201c5c03500844c14010310654041010b1103c01100c0f402c0c4980c0344611808001e211354080301d00ca40401c070700c0408100ca1589000d00002c1071a040e00c008a014664401e114415401960040e00704e01d82051200065240600c4414a80780d131520308000708103d80720154544100f041e901a050644c00150320500d916404050913040501400 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 344204748 1250 344203498 344203529
    0x15033e0a02120c152404150306022817010905090703060c0906090e01031e0503090402070c21050303011502030d0e0a0b090102070804050103050c0904141e01050915010207 75
    0x840f03a4a414012003d900b140566100042d2080340c2c1c0049011102059101e0704454042d0009010091414115403155425406070000002e60140014404901025029140201060003903612850340c1d2030a04144900420010440c00762003ea19046070b00f2071a011a4503120101500c0c01e145850b080074114a042c000030442c03068224168070100d600c299507409503551f696003116500d031402c1c00014050701a003107c08028206020250030f940b40584166450403c01c0310006d012a441b1040c21254114003070010051494140d060300c2481800c00f04112030040182e487c0ca843e484140900408c8010310900d030030515208005a03801d24036104c40c10404228400c1084d903484080b8501101d032400b5480002d0f05485060003504c003503603440030101d42094141001980503100041503003c01d2030052007149080c0c0e03a42c0c0180c071140005160742c60800e00f800c00034600e440e002c1c030320360900a0218500410450700d03081c0b400703640300d007880c83c00c1c80410200900403401c2814650011b00c0380100c841d1f = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 344205998 1250 344204748 344204767
    0x30902012006090c0a08070512031b0106030b1303020a0605091510090c090e07050f0c0109030903050d022a0103020c0313050f0103141503010615033e0a0212 69
    0x5070603018080d010104c8500350103032400c1140034a214010000c0507000400b0810260a01c0e96112803110480415030381030015440320790f0080c00300e8030520740050303469075030810612110344a181d8204540120982d1508025100a552040a900d0041410395a2030009407a08802c1c88024031441c002481140c0d0b90074100d01d400788500c80341c0039160019141c070a81540d40c60090303a50b00c0071100030702000c7d4650365944400340c5e0307283c011450502c0b42d111704000c8501220002c0c411101d00d98429202d0400306030440c201103160600f040e00842c01d549c0001c44281030342d5180d20300417040651801406505801c903500484c0a40120303940e070046032001081d40c4020707140c42c5200e2410b480e016a00b00c0000d00008004405442d01d40303840d00201103178a40851640072180d186110240c401a001042555035807038048817400000344640b0000f90b5078480d810508030301c04406290519010840002e400c070b0708034042e0f248030030400c081c82840000100a42d000d40244004040c1c0c0c03501661250726070741e226 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 344207248 1250 344205998 344206003
    0x60f010918050f0c1c0c020106090903030c02070506090a030b041106040303020d0206060301020703050d0f110f070606082418061005030f06010e011401021c03020903060f01150309020120 82
    0x81c1e580f0750b01900c4400024060400d02d10954005000d99007003403509128011406008040d041d80d0a000c40d502c034003000c40c08610b20f0141c162050720994000890108414000342022401c2d00080c0c03203600c0c20440c0c19902d5071040c4000302070b2500141d0600c4a9225441c4c00d8005405411500c0c0c0c0000300410000103040e008202c00c16140b000e5004e883c07d650355101014200e100d40360008011903c01d206600b080700841c0d000c0ca03600110b80c038000504003682004007540b40c01542c40070503154400103104042068034040c00340100b0075003004068001e418070040d01414000076202c00c17203010040c0083e0311701104c0d04030300e10020b14003410b48000d4103010284918a26060069500034030072140400603120700002c9050480380791401a86c1c6d030fa4200100350074600c0582a01074114800c403450b542101c1807180c2e00d007141520a0710f00590b6114244281418402c008040148803074003023004120b540c3c0c45507146003084000e494000b80b440903d1006840b103601c9085d0940b41101014800305440200 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 344208498 1250 344207248 344207251
    0xa060603140d050702011b030c05060114040b060c0a0f020a0308070308180d020601060f02010e070f09140405030304060906061205160801090309050d05010b060c0106030c120b060f01091805 83
    0xd080a480102c1c0000400742c40314418a50000c0c0061800d1101d94591210a07a03100110b48c031030700e484440c043c445d031141403511a080e00f22031042e0011007a140f0540c6814400d0a0b40c06a0554841c0c3c100021000c007507468800f00038018040d044032040d12021990340500ca480950f61104506880301c8241c01c4c010302208040341c10704101035240b41d990301c0c503810000d66507116038036643c02490140e0a240c0e0403151000f5005c1148107664032880b0b862850b5200b40b01c000060321241e803e034102640341080c1d4009403441d0035a03c8003e4501e01080c440414800b10880f03502ca42c002c4000b003a85e555511313000000704200e502c8004070a04030100181004404140fa044c100ca520600d0050240c403520340f1400c0750010301e002400305000e43d00400c40d504091801900040c058000040c1051264000c00c420703a016a4041d80265903840013442001151000500138190190000c2c0981045039501584001c1c050202c1c3c1c800c803051a48440b141e84a44001806000032410084000d00d18001d148041d000 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 344209748 1250 344208498 344208533
    0x11070606050a14062d07050619091e053f03010518100e040f12020309060714010f0f060806060409050a02130e03120a05070e210a060603 60
    0x1400c50001418411080c480300c020000206401d11700114620540000d2000f086445441e007034684800c040d00140300040d00b2070f28002c201802c2c451411101410880405111851000740f8102e0b0403c00724440d24481003d040300d20240c03010920550070190314011100b9820b94041c00566400e2200f075040c079450f5509034031000c095004400758100e14600d1400240203042c1c00814a440007141c1c5043d4002481d08a1140003d08000039283d007502c980c1c2c40012201925607011481c40b6500300710042c410f11289034080d101a60500d2407007800521144202c0c540070381030003030b41400010b2002003940440c0d0300144144d810825501e0b440d10302c41c09812544182c6016000741c4000a00038140f40c080e22808552040140c40e80e10b815a0810a030341101940400d15103540d10120084c890082005142e0503034013422202907458101e203100d041d14030051101c0200b00041c402e510860b1222012200d011503503140101a141d45440c00c24500119220f0140246042080002c14080600d910346600036 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 344210998 1250 344209748 344209759
    0x20406060f0216081906060e10050112151403031b0706090e09030d3c0c2f010e0601120203060f22170c0105090c0d03090b0903011107060605 62
    0x50700da00c03c5441032039140b2031401160003440d070a54401d400401d0342c0015034070a001c00501b141d142c1903803008400003191421250500180140030642c1c000c150008145105582840440081140e5805034006442030b08031244403038015050640c0d05001395000910b040c4081842c2200d400045542c99004e80301d01808a01d0480c0017181d010001d0480c0d80c459495103000b5031501c2c01c10080c40000340b11080341d01c6a121507144101c603c0c801940c900101035801c0359184c0b049000f400d245442100d0030407110310248105400380000303401e1a2a200c1d540d00750500c46c501d8200c144160b03018098410550804280d02800e400403c2c4c0900701c100d601c0146000360212115555000386070b411400080d5a8500030040340c104c1d1700c2d81520304e5000340c000141314280e4100c0000440500b0710507904035141d106802d9440f0410002d078400100300104180c4022079011600c042d06403006009c60380180241c208880300040c0b1741d6110f0700d094001c4040d40905400e01030340e91055040c200018481740c02030a2044d03 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 344212248 1250 344210998 344211013
    0x131404020408070b160203030c070911030114010c0c08010c20010b060301030f060204051305041a1902070c080a0c0612020406050a0c05010603060e0307020f04020a0c12020703020406060f02 83
    0x50409209440c2642c1982c001001098100549600c981e004012a01d5820819904810040e203003400038001e03442010006250f041e0900c0200c1064a030300503400124154140b004000c44006518102850360081c200120903070042d00b0180030410180c0c100c0541036003009542e040c0203501010503900c2d4403042d4002048214030b8000c940c241d80e18094a9a0b20903824001440841c07010340d03c00310305510451f00140307030940c1c84022540c40d5a00c0001301002030380d41c004000a02c103044034106408201107482040510b008255000c02a020b03002c40300e00c0c0741d40880e2640811040c840c3ca900a858140c084070b400c0000e0349052075400b246070040200040c44509100040a500e000360b030705880340c54580301d051580301c00b0120b45d880258203040e2120344d00c0d02030001c04544d841c13084040804410015507035601141c01482540b100600e41c2074000c910420607000708661090004003820f034445440b1a5182c64147c3c12850141035801c00780d4440d1070f10308006036240c0c0204810811010f03580944070007 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 344213498 1250 344212248 344212289
    0x7090e070e0402060c011b0504170a020a09021e0c010912080c0a08041e03031a1507140703140705011103090306010308090d050114070206010f0807050907031113 71
    0x25654140320701c0880300740000114005107880806000078462000000074070b0008040280311502010f600701c8042000040c061101e040039030542010109a90003c1c0b05400059010808060b5a03115054101d030340071801000c3c242201c8118110080c070220401c3d100e07801104018000c209114040350300e949602c509400c0d043c0688080f0f8854066211810701304600b184c0c1c11798450200401c00c031a0790101ca440c83c18070281000c1d261148a000c1d9400017284284181c5840040a40c00b07071680c03003541d02c04014429030580c40d04540100c1d0b40143d1612200c03010000052400c2010742000304a20045120740075245c500042c1c1d00205d0b003090303032800307030504a0641160f228400c00d1640354140e0444001440895540e80c014030700c42c031028020444914407a00ca85084481000303046082044040030301080c5e960403c8041e02500c80c02c7e822508141c64441d07200c0d03540c5039138454903004100000000b85418041d500405003038105044403135427000801034140080400b4020900d000210360142d41c83d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 344214748 1250 344213498 344213503
    0x2091e090a050304061209061b080c0f091905030a03080603010c030203010b0306191802222409030b04150507030213030f050307081c0b010f120b040e0304060207090e 73
    0x75864012001d145010f09024040722003c28a103038040d80d00d9252180b801c006006403140e018601c58006c603500741e9039060f09004060b40c001034124282240305001c030440901c854021200d01d803000b1030302070118226514002403800100c0d032009034103008042d1100281758000350020304c2840220f0080240e584002c2c0c003078080380000e004903451160b050001940c00d04000c9078542c500442541d190550030b5580c07102d07043c9581105010b4880d9900401c600300601c400103c03200c0c3c449001e03419548024100b5920650002d0400015803403d292441032540150041d00300304051600130108280342d01c1c1504250036802da540d030b0084440e41c50040054041d80c4684243c40d444025910101c20461554030f400c031003180c412009440c1808104045c1d00000e109000600c0c2c2e84800c10000300700c045194024000315044015128140f0941900719081300390302901c4024200d00202000503030307000b1704011a0003800000f030001c95510000401140c43c90300013426800320b5406060034444050341078590349c0c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 344215998 1250 344214748 344214763
    0x50d03051602041e0f060e162d0f020d03060302010518040f09050d020607090503070e150307091506140307050c12031e010905040317100302091e09 65
    0x800095007803290100d5801051409844180001c1000c21240044140d04019406607041640b480c0e40d18500706990807814007420005210ba03503002c4a2500e086180c2c50306148000d603078802001185038542011107240042d40e00004941060040414007440307000e8a88d502d603081c0300e4013600c00c0b00060303094144280035040541c0e0b4180d582600308004080054080003040605c95802522030209101090891103a503070410300a000a100200640c0b802a08240d40a1b08001c00c0100f01c5c1d000b0300140c3c80c001803030001c442e50302d10301d030005913100c0003850545014122a02e074103000d02d040004030b61006030040102044004000078405503102425101c5613204d03003080d5005502800050b034040d02401c00780000e0200700b0156a140090b4041c501c101d5842191540038000d540410008140c49002040d4098070341c655040065080c00d807000390200f03000409030998101c0380c500140c80c207014105480011344c1c2c003070410021400d02840d10041c0c42e0340f0031159482d150f0420009880d8800004005 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 344217248 1250 344215998 344216003
    0x7030b01060f031410030204020906091309060b0102030424032307092c0912070c081203041a0903040812030610050a0c0b1005060403110102060603010b300706050c07050d 75
    0x17400098595402d2001075001043c4159003e2001c0c0401d542035103e240c86044104014000020100c06501d003100403110310308904c904641c0240414445c8041d554040d0020854084c2504042c401203c411005441e1103007181a00d9410ba00c58602e04040c04511940034241a4581c00e00481c0c071800710305969010001d001c940e4845401b5981540031034050042c0d044140c075000e540d001c40a03889410350310340c001c01c41150b610b4800032040083c00010702880707a0004201100c0c40c0b45003003c0d00c844d45003a48280c0c41548004421001ca41c0049040046400038800c0100380c0d12501b0b100301000c10190000c81340705029003d4401036503046441002150005266034440665062990f15132140340c0800901210040c01c0c410000b084542d03681c00508001c41c820b101036120601d015000a042800c00350819010fa0b04100c100d130110f40c0c91248031200344440764000d083e0800400d0307500c04008803c5603034440724042c001011440035401002440843d40710011207407456520300500c540418101c401 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 344218498 1250 344217248 344217271
    0xe06072124090b0f061b030415030c0824030a021002070306150308070b0a02071a010503010f05010b03070509061207020a0b1605120a0b1815040e0c0103050907030b01060f0314 77
    0x202c0c482171070414042c24402c04034aa07031101d90919107014a180d0707807150700b05007810344c06152035540301030f030500922140d00340341e1601080d581070440c1014010100040c0c00c2c18030000e100c80c000401c3d00c081240440240d001444a1141442890041d403107289502060700c0c45800c2540c00480c1011151012081742d0f0700c0341da118607086442e100e074013050704041d0031407117940d0b020132150004c42d60681e045046605c00200860565141c403042500f1200760b1108002020300300310040000d24945da05482d0701030200c0c207100b5550a48140007075154421050a061026480030521454650000c2d41c40002407040b00d82c4010703603c0b4850017500002c0f200c00d82d2030028608210b5030502038007455003280c1001c0384500200750f01900700c1c000342c1403400920104007011110030800c840f0643c0980c1001c4c031080c05960801a03503034040a019201d00d0003130200b9045c141c030f41c40404d54103a01000a14019900b01003031741000d5864102c0140000c1c0071303c030300c1c0380080d04107594207800350091084c41e40034440c501071 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 344219748 1250 344218498 344218519
    0x1409121e03060a2d0e15060a0311070f06110f09100507060c1206210b06010c050607030903020d030c171b0406020708100e06072124090b 60
    0x85540d803070352000341907035040a1600c400140c0d00380042030300540003900001020000081481450b8800656409039020000000c244461810300602041480506070303282d960340c49402c541070300a021000b044520440c00050404180030746642e000e03400030310810041c80308061203102d00c0d409018402c01440020f108000c2500c091504281d81c1802503104d00b42241040080c0e22440b04a8010a0030400401e1105103000070800303051103084007920b908014800009450703000103801038042d01006001c400d6000100e25180c2c000d12413182a90f44c000c04645007482c14107001400b07004046000c40140c46440c00c903c00c611300a0140058888080d5941403000000030000010400e01401950720519026804400840e0380c3c8000e1029010580042c110f07180743ca00345074506890b505404220320300e04038443c1103105c0d000c2885a0401401d140903a00668a441101e405842150007084414506500c68200075079521103042c5c0f00321290040311180d6500c0f04404190381810000c6507000e01241c9 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 344220998 1250 344219748 344219797
    0xe030d0807080f04050c04020f0a02150108030a030518030c0313050f0d0206031503010e010608060a09031b2405010302010305060907020d03021303050607020330060607060f140912 79
    0x2443c050780b0501400c11038002c000c200f000f1900702da01002e912400c06d0000108090310640400650b65044170120b110001d9600d41101d10f500c90240140e0b41d0209500c50b0045101200006440d40c0003210400039a1303980c01014417415900d9008208000207082e51003000101490710041c4400005c50140c50860303180d40690812580f544000c1030641a84280508000c4d603403024414040161041400050580d0500240d00d2615100909141d64142400414400681e0007050341040302030802d503200703005c011440c00210000d220300c3c840c081d218003400f5200480d5801d80146040368000c0c2c1381027040d0348a60003800300c100b508a400202691100c2605062248258024a1043c00780407880002c0c9e5145c0d03644c18106042910310030010703400415203101c080190700151007c0c02011104290703104000b9034841140c40024003241c030604d8045101802e02816400940900000d2035041001c0614481d4007034101c8000c1d22450b446104000041500703a4801c0c0850700d4420055003600140b01018 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 344222248 1250 344220998 344221021
    0x5030712060f0e060106020f010908090d08070b0a02120c0c070302010e040b0301230c0309071e03120804150902060904020c0c0607030210270b0405120a0e030d080708 73
    0x9010481d81266500810065a0300500ca086002d01c0408007038000b65240c0b1400034a849840c2001404a0745400b203070300001500340013228540042501c4c0340220707220a00b0003801c2402620342c0500041003540c10805808140c0c3c1c0281143c421404241c912511006c0300c6006602170701042d410f41d43d202080c2800590f00800303184000c01d90090020440b0340005010a01355a482e08a504010b81403041d600b202e5031070448510342c0409441072a50542c60158907407a41e581c001e2040125088883c40706008000c0d40d54465170240d40c101002c18503a00380c104004010350000c40301030340d075000c929908013038030b400500501d141560003c18260424410070304002c02540104c01c400c2c0c6070b201c0c3e482000c403251142c4001e04141406a0050400007054a0304079040d01d08807062204e0701c0914602c56080903032103640740c44002d42c003d0001c4145680302d2401601d03040304940d100c0d90305000815100700c260303403000c0300c44090308041c1d003924a0484803400c00d03102c0030300544a03400070440c250001b03100744010 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 344223498 1250 344222248 344222279
    0x1a36060306070305330301110f0a030b04022a070f1406030a06030507060503010317030c040b03040f0b1024020706110a0c0303030209120c0f060a1709010203100f050307 74
    0x18105c0103540c1c8150380111054400c0c125821250780c0e104108000d8038a030038420000b044c090108100d05d0518864202c0780075201e081d4900e0140f5540e03140d141c0c100d445650603a01091056111140382c5e4170544e074800308444045d001400746201d446800304500e0008005141155021004001840c00d20020000a600300401c0100002e40e0350200101103001000440010001d81d20780d80d9480d411810410040ca01c000c800710301c150404c200340700c2c8018100d0125403c0314180000c9944a80311031800a840706403007540503050b01445418080800c168249541c02c4800110300c440030301d0003112a015007044542d44800c0035800502042059030300480010318a50081130903038007031080720303911002c00128503042030f4000380d40441c403030720305d41481c0840841044004000f444200700b13000002d0701c61200c441c2d00d5405440046401050305006032001c58519402061843c001e1900020240c000c0d0403c56588c039441004078000181c8181807910301c0d0075120080d02821a8500301011030300d80030344 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 344224748 1250 344223498 344223511
    0x219080c150105011209020915060705010f020405040c020105060d020108070908011107030e0906030a0809031204080c0307051009030219080a12080a0c090302041a36060306070305 79
    0x4002040440005010140701020000441d05455040c040010300c02203003542c0110000b89412083e5001d03035201780c282c42e4004880410603034030a808602041e824012503400501075800c1c0080c0714503015440d0040c2003544c4003914200220034041104034260b840c1a52035580103001c0e21042d40c0594841c1445130f0b40405681000304400340e585091030700310380d401500c10301c0050010401a081640c0300c40783e8084080300321150021401e0190000c0d40700c028440c0300501c00c060010388451552824007800e0f5200c4480480e19448560301c0c21041d44451900214070300ca400b07200304c04601841c10b40c140d4070368112a47c0d543c56140d4107550074028840d26402204002c198404c00001d42240c040040c00b0314944110380c1c04000700d901510282c040140585002c0e005410941410703201d5611503809000c4a8044030701040d03441203c40e00540310f0b40303607145060b00310300300b640c0c62501c4014090f06440300d0500400072148411030307034406c81d02100050f9202c0da8590800008200f06c9840b0f6006240c0119 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 344225998 1250 344224748 344224763
    0x310b03040b041a0a092913050c03150612010c200a02040516121107020114040b030705040311030601051e03070b0a0c030e060f041205120714010515010219 68
    0x7030800f4a1015481203a02e00c506030703283c174000700410908681000707808280c01d04000c06242e818009a1031050010714100d01000a00145014000308004200b01c408000d030540741d01400d0391241040072002104d04a00501040407403101401e414460070006c41003d686120000c07201c0d2691410000c0f036942c2900d4103109440d60280035940d1881030070701034040501d10b07030000109404080d024031807501080c40d402c0d01e80f8801c0700481400c14103c4800c164241b9107001419042c00501226000c0c94002d420424404002c02c150203810400800650340181e01070a4550030107410113565120900071640c04c010b600b0809142d04441e040910003c22004088c7c1d002c460302c1d07a10081150300702840c07800c005004007a1810505400c506010101c0105890643c078000c41c64480c105a8480c07072003045484c981601b04801809020b2000c41d1050300c032000c1860780c49856040c802c80000d5200c1e5a81c5081d441c1801260840002c000070403004241038000e4940f4400c0d28150301451183c84c80c2c141da081 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 344227248 1250 344225998 344226023
    0xc070b012309010b0903061e190603140106030c090c0c0605060303071403130f080a0b090f0607020109021018090c0309050303090709050906040b1609080102310b03040b04 75
    0x66031070603049400303800070180c545e4480d0f0b029020507240c03c801030012014041021003030000c0d4051109400e0344000005802480c00104d142d4080c024021130f40050041e4100c00d0081204c14419000a011203010300c10710b90300b482d12003e40c0012211540a4a004206901c00a20004041c0d401450b4040401001d5034200200c0d44c03601101d545201c40300305129080007541d1824070844150754405080c0441e00340c2c42d05424418915503510381044007501c1100000005810384404104005a0b5900d020590304103007000031029029010025040b07205c2c8004480350030005128240710f07a08120b440351020442840c2080210003004a0070461041507118960140800c070204019402415010001c0008a2518000d40100e030360181048600c1e40000e014030010629060b401508107200b400302400324070480324291010207455000035101e50000c1504c1040b9171000d694030040301c91803124a0310405100081d8803080001c1e000c0e10712761442c00c0c00403c02003030742c0c407800e51f9102c0d20401b5401401d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 344228498 1250 344227248 344227319
    0x4180b011b03030c140405010c060f2c12030c03160509030312180304060210020a0215040f0606050126131b060306121101031503020406080d02060c070b01 68
    0x1d00c21181000e4000c01e0300c500c8404c4099a2010020120200e519003080c149410a40024244c00e081c03200542010b80714496440d0940e000d41c0304801941d80d010500e1018402e0b440c040d59950071800c3c001e602c0d0f006403e030b000900706c507940459220300c001c138482510310758424640d45410741d00110340c1c404108080c020140d054130104002d1600c0c07940c111051078039241c2403042000c9100304001d011800d81050204200182c2c0001e240b5a51001d0203001580303030781e62104128039140850305152410703584c01c0f0a10091240c10311244c007205004880174001c042d114401510340f00c40440108030551510b4003090301c205039031040160480c849005403c208201c5858421000c84440b40c9074241c2604601d040004981500c22440140006d1820101020050703d0380e0495102041030181410b0300d510301c4440e00d1501c050399a018690040042001d1521a0406a030710500700604030058806c00300450300351a042d030150f03a10254003844004882c4c4c200101203000b400b154281d0401074a9113425540b0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 344229748 1250 344228498 344228537
    0x50f060702011a12070b1e041202010f0e06030a0c02030c0a050d111b0d0206090411040f0b040b030c09030708010f02180105130e07121b08060604180b01 67
    0xe024a034000f140140000b00c000d0510858192924811003690390001107421000c43c1e540c04440100f04074546a800404801000403030584000790160800240840c07000d4016403140c522a0007030b81c407148444000c941c01c2c3c409501c12a021507005d002800018805010b9402c889209241881620b082c41030008440303140103c01081200c05420481c0046a181d501c601c040c003a0301c10010081c034940b05000d0400c58a403010b1182d0703a008207a101e9600e03040d5190309049171066407015108116180070040042403681090044103507a2403244400030300c086003030090340c0c1a155131130b10f0301e4036580ba112a03004440e4483e104030340c2c25014861000074040c00a12030301038400540708015940c0d02180d441107804c0003140c4000750600034140550f00590482c1c00000040c1c507006e0141b01ca45480d491001d031070100d00c02c15a0352207241400d6402028000d0140500b200c14100e444030304117038448408200c818001c82c00b60461804280d41c031001d13111019003001000b00700605000e00080310b9900c9020 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 344230998 1250 344229748 344229751
    0x4022508040e072109020d200306090a0b0609041a010b070b01051203090108072304290a180510020313050a080a0623010303021e010504030806010c050f06 68
    0x40d40184086010000840001d101d03a0340640a4503098004018082080c0b0410440c880001180d9540300041c0d002c54039540d00f40350045822540f0050400010700300704006c00c1411034414024020480071800d079820000c4ca0140084c0c1c006d01c48a800d0707a6403424403008100007081a00c90716194450740a00e919180b40c0745004e0104010000d648a490341080c1c10740100c180d1202d40504182d8503001d041070000301c151f8240c1075007440d250035281c49400003280d90a02e141c1001903115004883e000d205042c001c014011100c01503442c12041510590040101d16100101c0c0761020042283c07007806441000030206000d40c480003412070039120004a143c0140313404c001c00159100050350060420781c00346181c0100b400301e85219115091145264960903900c070010031441d203a40004564441c000b0754807100544c0058201003642c0c2d2030030001d55410b00d40c503c8080c520301d08085d98aa02c80180030320343c4a1a015198140c0366101c000046500c1c911762141030301c0358000c420404581010510826 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 344232248 1250 344230998 344231003
    0x1404030209040b0a06050108010f2c09010c0908030a0c140102041e0806060916050d0906110304020a0e01050607170c0f06011716091e06060305040309080c010c02040225 74
    0x101e511316001c4203070822510680c106c00e041c01700740c81c0100181e208079a200710035148154400100b910b0384414112105590340d074400c0010f1107030010400b40c1038056211102c02c8a1569960041540d544040d5440b4480c00c41084005a20640e40720003003880009501000d42d1078000040c078040d0756641207814002c00c00348090098860080820540c101004030681141c803c60303071035909040425910754045c80c040d2010040c0400441d05200e1100264000748030a50000c0c07092040c40e20944282240754401c4608920a811980020074085100c51840303041c0c030400b910f003e03d450002c0c1c958503126120803010031048141007003202003104042c00081b680c022032800604040d410898000d038101105220f0f184a5802412441c205021442100c2d044480c0740d00c0004e1311001c019020303092100d610000d900c119040a08c002041039156103e540310383d001e951050350454440416580f42c200c4188003d0004062144a901500d00303030b40100b0390001e000c004c00d136002c43c080708421601803055006 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 344233498 1250 344232248 344232263
    0x41d010603060f0c08060117070207051512090a15021317010615050c060121080c0706090f0510080a0e01140a0b010504080a150213090f0605060a0f140403020904 71
    0xf500304204540925203444919040c85030841c41c1820000b48602583d0b200d43c03002d100101c01280c1e8250080c49080060140a01400b041010741c0b038450031582d0080c0b004003440c3c0404000a5049100444d0000c07109a002e03000d002d0b48241c0030003900182d040f569041c03100101c1000000740410080240c46c0015601c100046203046c0380041950a80111400c0c5000f070020411040e008040d0200c1c03c5819110320103c15058008100d0703000b084e801c0942e200606481000401094941c000204c030403c8071016610f82040c0c03030701c1d40e0f2000c40049940c401c042e00038100c50722038003580d80507822181e480005040300049411020101e00d0130f681600001c011410303030120500120150f54024034002910a00341285000d11f45040c00380d0342d071041e0401404000851340050000c000607011119884180b182003503c0d540c441040b9030080071607100340f294451514200040d00d003482c40948025003059141d07020004100754003503504041002460708031010400012006075241d080c05402603004502 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 344234748 1250 344233498 344233511
    0xc0607060b0102010506040203130b1305012a0215010323070906060e0415050d050307021806090a1b0302090105041203080415050c0a0c0809030f100c09080a02041d01060306 76
    0x1a085176000741c101c5000c1c41c010800c00040e8600c00656406059000c0030596040d5160024003004045052006041c0e501340403000003500241d41c0d641c0c80601c1070907401070040c2e03e89503082c0c0e40c2d40307151031149110707603c4440104041010b04100791901c0000742c054400341c01d00d54a4044c1807481a42045080540d501c9050084c268440e003441141c2c10240c034104180c503496443d44018000d00c0c820948906d450301161001c00509005442174541d0203400c0c042c4103004040070500b0f20300300b280d009005044610009112241c68010002c45541e4005030750202c0c156500304a01079881802c5050502c40b081200003182028181824240c03402651090700d01d003801e01e07004c40804500c6e9107417508a0700389418002003074080710486445002a0608016181e00c82c0780000503400368130881c5501d80141000d040b112080031a0181c101c4607412410880c070f034401d8071306499040702401011001c1d03000010001c0142005c1c0d20451000740102041c40340b100503481654292582c5820440d4116160b4a = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 344235998 1250 344234748 344234771
    0xa05060f1803030c0d090c09020304080a030507080f0105092a0d050108030a050a1223010e060301020c060c030a14071e0305070c11040209060c15091603140c060706 72
    0x860380701021041020710702e1800d0050305000b013800f64002000302c1c1c594403000c2c18100220002d900c0700410703c5000546d1039103810304041505030010035a1501082c14500081c0c049886019a507100325880180080540d0074038050000c0014000c00c1c4030350280c1c0d041c480920b1400000c03a02d020f140c800c280510340d5a0400c0b500030040d140107a00924443e0b0060108250b20343d00502903800800c0c151806128198840780c4400140002c0c03601040d030303044609004000b40103c1294141600d410405100380c0e6150b020905080748a0540100c5003500702c0c0c0045110b12198400464000d92440b80214460035550b00300c2c0003401d4140c2b80d4201141c00801403041401d1690550301e14620681010841407a028801602c0e60940d660000c020100c45c2080e40d400340d07160b80c15116202c0d0090801601d40c420300907030aa070f51034160100c1052411100029000a40010b407200740ca08046031031020151950b034807111403a44030300c285c40f003901404400c0180340c1c5420001d051024024032000c51642c0c02d18 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 344237248 1250 344235998 344236021
    0x2070507051807030510050406090e160f2102030d0c0b0604020708030a02090103061a090415050f0d03020c0d0c0e0907060212090301060305191509030f0c050a05060f 73
    0x240d200d203000e1001c0452070b100c0c11502141e401e9100607913050109465a902e0f11101414560b50405a8410304e80340307010030020302c154805004003031242c045880b0303a044000000140f40c0c0500c141e41120741d904800f4000c4c0c10300c200c01c0740e1560070151712558103010f0030b50029080c0751103003c0324000a01050080c07820301034030100326500414266011842c0401f02d880361681c03480020105840d43da0001941002d0b079120740e200a0060241c03144007490403c921035042a154804030003e88105e050510307000c0e044920a2400c421034038018609212a14900140304a40d404100c042c0e05502628642c500152900a411000244146d0035880c0560420407000c0103140042c12208440d0b1000c0da05001c001c0c2c001130006462510241c0d06c6454642c1500024003404c19a00000d100340144010001d5218401a05540041c803c214100100c0c18176240c0400311101104042c0014204440103600d46004040101c0c2a44c06101556030301d202c25100d26103421000da400400c0c0c030001d44104014904034 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 344238498 1250 344237248 344237263
    0x108060f0c070b0406051503060718081204090507140d1d2109030304092a020a08040b030c1204031d0102010b061905040f0603090506100506120604020418020705 71
    0x14884140c103202c0e0948400f952190020001009560769001154034903c0007095480e8482c0c0c0101100c3c214070b0005001440e51144078000201407020b0103000c140b00d140031581c0e0480703214501009040518246c0004c1c080e2201505d020188620b9600d20010401d40c03100415034030440f5a00071501542e10201c800013901c000c1000d40b0a5040803c8825044004030712190a00081404881e102c0b54031000090a61203941d10032180c0d949408072490403075440c1c00700080001c42c0e405110701c580703941c100140e84440c0b20103402451a001084180203d4090101868001d028072076a1810051f140f1240740c04488280e900f500480c00030741c8200c14104c501c020402c680e620a00c024041038802d0b0300840c2040c0206029484201c8201c44003008040c840d40c1600d0041c400d00b06030803d05980c59102400605421005076007134020400000c0214403c005140103e54010300201d280c840000b0540d00c0383c200103802294400e0302040b00140b915512009108401d211502c0103039145114607045151215 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 344239748 1250 344238498 344238511
    0x2010f0305190903030e0d1709120412080403080c030d050916050607020402120c1e2712060a0605031b0102031b0106030b040c06080a0501031e03170108060f 69
    0x40104000031511068044030910380c15500c0480d640000d840c0a8014000038000100c047c807a098500c078801b5884020311030302c02502c181001c800d481d2003110684540207440701307401485c0200410049400d00310ba2040000d80100949420305e9200e42d1030100940c05040b81c54815400480c103e00c4c868014401c1940100004000f04070700c2d5002c03c0c0100d481101403107210300c10b0710003150403401e54a880e01120700001c4105288059403030500c0360040e0319040020464070400303200d030145407020040c608035034510405070040f9040c21021500024540070500103250070124086a00884003810040c0354081c240071000400c0d02800c10082c907150140401c0d180c04510542d441404890343c01104541220b0f1a81969207100901d0030f50071800742c007040c0d000400100e0b60801700428804904043c00a40c1c0003984d80806540b1003010728070540c0c000780405450101d101290800c0b441c4004209120030b8803038108401e2490300c6003086145008240d100e04419080641003000445d00d14410503800007 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 344240998 1250 344239748 344239751
    0x30507110f060c0a0309020303211005210a0c060206070f02030414090402031207230a0c05100e0402030103080d1b090e07110f0705010206090703031e05090303040f0302010f03 77
    0x405403240d6035440b00a803c031031044100061381030a03a40300750090070300c50750090204d03640e8004420070030070080d190803464a402032414010031048603e400c41031080350001040d032101d02c5d8440e8003041e031000341014070f201a0301c103412005000600d0819032200900090300070341507901e40344201414039039001c0209002c5402c01c11052010714031560804141c8070040d41c50f24002d540d24030120b45000c40d250046004a000401c0e020100b10003030410044060044035a1500b021568076030036501e81100c5401011135005150500c803a08100d421444007402d2494199178481482c0040360880e4800e07003068840b0b031000910a08002c0c2680a01407c12012810500340700008640c01810f1001c01c3c062141d800f80340c540400c000a100340700c20748400b0038440c2a5280103502d0751840359185514451580036004010010703002400100b00041165010b072070f0305031400007a103420140110816455400d001d01440300c41d103075850070030140c800346c2a1242420001c4d401d41c0005840b800c09001c5010415 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 344242248 1250 344240998 344241013
    0xf0308060d080d0c051b06040303060e0906070c05190b0f0c03010b04120f02181005030f03071e0c030b0702010b0319020607020d02190918020108010312110303040303050711 76
    0xb0740c0d40411543e1080b8030600028002207441011211880b450041190f03100c4405004a0390300800705046000790b219407410400f059480c2d41840b4050300442c0d14580f81e4001e8000100002d01580f0b04100062095043e03809075400301c10054000030002406550034083c28040242401d1080340d1180c00003005c10705181550b14181c842400344c400c6000d080a00e0800e4080341d800c000b0403908140c41c1e01d90083c12070402800e008006e030840701c001c0721601d001300551030340010107040115013a924400220013a501d03090003512040c1e9050a2990980035807078884440d040428542c802120145101c1d00031b1034600d003000704009082d121003085140c0301e50032078501c1c00314064000a4a020b031075416030b4081c1c0c031002d043c00003849c9903038071480c00794206400071101c0c40c80b640d00143c28001c2d1104840c01b005412005211140c04050752030000380842d92100061001c41c403030207528903125105182c450f11805182036940e00b1034005032800ca001c40d0b160310500410300d412090013608107450000800c00c1c0f = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 344243498 1250 344242248 344242253
    0x12041523090108250c03170c0306040b010c110f03070312020609061b1204110d0305040501120501030f0204180f060603020f060a1d01110a0b010e3907020306040f0308060d 75
    0x400340115420790a05c081d0804142c10140590007403104a490020721a40300e10f49040b88400030b910031500540719600d0500c2d0740d0302c19800340042c04c01c22900910701c0c03811902c2c401d09016000c0f8602c1d00850345481214030020000d0072400307a860300c02185a0191000c0d0802c20006441cac05d101420200200d000c4861002510308844d044d100c08510b00300000d502912036040c900785100c5860742c196041050004010309254100d001041110400e03a1800c2404c00040100c808a0708280001031a2409400c010005031174540c1080d1108424007464200904c5a5580e242c001440c403803003103400781d031201d00400c00d602d0200c103808480d40301540d5051505004200050400f01c1040549007400e004c400031b080c0c0b43c0d1180c5510080102c008040310036680c03080c10092110a024858813920b207440c2d000162940c9c0100d0300c2113114000340140482030745107501c0c881818000e10741c1c141c400c1c0f00040c050040036070f400b0046140128090360514000c5569400c1c0103101000080c2100d01030088a442d9400 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 344244604 1106 344243498 344243551
    0x8011a180a080a03210c200f1f05060108070206130309080a03110f03040303020a03050315061801030e0d0507110604170303070201060812041523090108 67
    0x510117140c08108055910081c94000041c10f900380d00307000b9140030010400208968410f076030580c0c00d0b00c443c0c035141811081c494048400c88003e0800c0e00112441000c1d0411000e103480c83e000d2904000c00b958954001d44203000c030005094010080c10b129100c0c8402402c0c0a000380c2d40c0c84003107070600030103c01c3c0340315100000703000d80480382d407805200104490480e54076030050311840c1042d450580f45500014021003100c800050450300700e17070302c200040030040c4034140841503a281c000001801c0b00c5c00340c40d83c0c2c1c010740c0c451100a1340040e0010186c41e15039a2240c2a1080746880d403000c21041c1c06580d2003142c1700d20707150800000d0b02d180800598030443c040ea008000c595550398400703036100ca400c260065800170400c42405002c404250a5500a915040256490b044651030404540400901156558000c60010000d60784588101e4002555104c1c130408041340c510b00e02c4 = true := by decide +kernel

theorem cover : BRFrame.Cov 344064748 344244604 := by
  have h0 := BRFrame.cov_init 344064748
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344064748 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344064748 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344064748 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344064748 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344064748 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344064748 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344064748 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344064748 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344064748 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344064748 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344064748 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344064748 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344064748 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344064748 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344064748 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344064748 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344064748 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344064748 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344064748 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344064748 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344064748 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344064748 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344064748 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344064748 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344064748 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344064748 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344064748 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344064748 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344064748 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344064748 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344064748 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344064748 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344064748 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344064748 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344064748 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344064748 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344064748 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344064748 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344064748 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344064748 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344064748 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344064748 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344064748 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344064748 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344064748 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344064748 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344064748 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344064748 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344064748 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344064748 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344064748 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344064748 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344064748 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344064748 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344064748 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344064748 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344064748 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344064748 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344064748 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344064748 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344064748 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344064748 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344064748 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344064748 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344064748 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344064748 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344064748 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344064748 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344064748 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344064748 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344064748 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344064748 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344064748 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344064748 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344064748 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344064748 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344064748 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344064748 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344064748 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344064748 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344064748 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344064748 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344064748 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344064748 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344064748 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344064748 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344064748 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344064748 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344064748 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344064748 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344064748 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344064748 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344064748 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344064748 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344064748 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344064748 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344064748 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344064748 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344064748 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344064748 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344064748 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344064748 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344064748 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344064748 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344064748 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344064748 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344064748 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344064748 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344064748 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344064748 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344064748 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344064748 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344064748 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344064748 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344064748 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344064748 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344064748 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344064748 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344064748 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344064748 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344064748 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344064748 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344064748 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344064748 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344064748 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344064748 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344064748 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344064748 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344064748 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344064748 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344064748 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344064748 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344064748 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344064748 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344064748 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344064748 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344064748 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344064748 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344064748 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344064748 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344064748 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344064748 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344064748 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344064748 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 344064748 ≤ n) (h2 : n < 344244604) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
