-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3270
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:10:17.965059+00:00
-- url     : https://prove2.me/submissions/2b454c67-b764-4d55-b000-8439686b00e5

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 587949640 ≤ n < 588129496 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 587950890 1250 587949640 587949643
    0x14030705040629070f021c0507060f080f0403021c0207030602040b0c120301061d03010f09080316030510121e0317070309020a0302040b01030204030b040803040302010c0906211805 79
    0xf800c050301d51070011a0301c0c2800d10907240f419200c0c032a4004a041e14400419820080740c0160810044864524003841d0001301c0c1e4217200d408001c0100d615519030520000100034501440104040351549a0005010109900198218499500001d05071080006d210b042c0e18280746640004e141900011340802c85003a18405000105104004c07510a460043c01041050009014100c0001d0300301a840981c40b00d000f88003402e0302c50103000080d00507566590300b400da40e40204140d460540001c240300c4211441000f140300c258882c075041005080c03850003a24800041c0c411a080e02002e10484d4003840700d4240c0c042c0c0541103400d11505804075500e4081d1100c00d02e8101c0a80101c2e0203030008843e58000d0044a000683c000c0c1403003601d0b0b0465080000a104036040c00d810141d00f4040480000c84440c03000d80500c0c040c0401544900c0c06140090030340314910500700401010032810412503402050300070b510300c044200203a0400e04465007400804003400700c90418450701500300140300c1d0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 587952140 1250 587950890 587950919
    0x20307050712140a150f0902130c08011202031b0103180c0e16080403030e1c0e12070b1611061903060806070e0f0f09010f090c0305040b01140307050406 67
    0x22545581141c0d60803180340c3c3e5200c0489000180c030940c1c80350403014940c20141d11100080280c1080014000f02503004202001b080e6030342811110340e11100401c3c01a0040e030028018001459407033086403455000c20344a042d025807281d8a0070301080c0683c2c0c240c1c001e030800c030aa0800809a101000520f081842c05c49800344180c4108209800c0440c0501800001c0d0303c06042c0136446080903901c40e80d40880c01807509001038a01c2d8024255800b030380e9403c41d041d074240340e203c544d00c064080350101c0c07c0240c10a40c5c00303002842c130342c040d00d81048900d0881c0f05944250301e050581000e040818186000742202c000c809076404000010100310040066046235402d01072a13901b0800c440d01c1d01c90080d9520001ea403001c02040e015240c20f0090310b042c0d06030310b030707101c40c05001f100b0342e0381505005c920b045d90280c0044a242409403018803803c1c90074420000000d0a40c0340902450034a5140c10760720b801c1c1800f0394541401c058020002d00e40b0100b09050003400064800c00030681d0340e4425605012 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 587953390 1250 587952140 587952143
    0x15060c0a0209040c1a0a1d090c031009060621050412050c07050604030b15041416110709020a110703030504051c02130204080d140f160606030305070b0606120a0c020307050712 77
    0x90b00c100484070203131041f10100180602c00ba14071030450704d07021000007041d0801800c0c03440f5194a4600840e03c3c581c1303809220700038131003500e40b0440848840c02c0794400f14441d100303002c082850081008045001c4058032a5624068180240c1d01d100209000c0d00341074080c0c01040e04210300107000007c100b01c89000364407800040f03c0c0f45400210900c100029185588114290008a60042201c060400e001c0314440070715410424014121441080e0030901e80d5848951202d27404107030007a8103030308034040c0c0007031a00b9035014142e00c90441e90003401d14091030017081e000c0c403030440307450316041c00d8105218942600100000341c6200101121000b1b94454022151140a1807005000c0280951145903c002d19103031224100304079a02445500d4000344c0100101c201003551000119226100d458041c5000380e81c1c051b950000c070304226004050141140f40220010040708087c00700b400146038000580080101e4071040c401022441c0d4041c6400140590091400000d41c499440841c02c0c03045 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 587954640 1250 587953390 587953397
    0x70906030e1506010809030909010b03011e0b04152601050a050a061202030406060e0c030a0605012c03070b220b03060105120601090312030515060c0a0209040c1a0a 72
    0x718004003019201c0d1080844181d082122002240156010380321840d801111001100c0c01e14410034000750b0317095400c0c4d1002032070300000070060004081030400d0046401c542465150740910b012540ea80c7c610036480f0303810300c0031440c0c010b035145588200b42042031207545502d4040d400c0b4881c104100090000c2c0710300c0c2c0c814110b43c1301c0041c40f803e00000c5401103070034948071410751444401941c00658001841280c40503a100c0011034110145000c19001d481200240c540b00e24111640d94111881d9400640c14044034811001d5942006000380200041031030011b488404600d01003454a209500511441800440d4643c11111200ea0b54411040450200c400f9142e45581c1d0400f1032005440150006608220031030000409400140d0444810300d01035040660360f8a030103100390070010306600007d07100c006005001003000c44d038060300300d01201d009141c08442d03a10503540d4840c11030001e0113500000001800e002d01c101d181c100501d02c241c0e500c5407003500b010603400243d01a03400700d03011 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 587955890 1250 587954640 587954651
    0x20a14130f0c030e240405011512030e1906050705011116031205040f0b0702120f0408011b021c030902040903020705191202061b1501050f0301050405120306010c050607090603 77
    0x40c006170a19813280303031a491560702101e400e00e51246200081059405640303e4594810f2400c1d03001d0140d00030000003003041141d10562800811000000d11110300c59a480d01c03090400c00443d031400f00072200241811a81d518552502c0c0d40540400141403110305000304142d05401d103600048408a0b22a940b07016500c4c841034400c4d000c560301624043c008298102c0c0710000070f40c800d0295034000c603075401190417084041c00d4560640d070003050355004510b00030804100c854001d00406124103d110031040201c3c9908600a65520410b46501e0301c0c1101c1001c41d4903d68040c0d0b00440185402510078800b01c600750901960321080c6114150188480100302c0d441d0020240004090b01c0c04500503040310785198082004607080080080810a86032190a8010004010040c40003841d00251210b40d07250008020341c1c5840858524001e174100303002c101c0000d00100703040c03c4410380030703050903226103a0200403501c625004000030704920448041c45182a00280490111082a68207001 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 587957140 1250 587955890 587955911
    0xa0803071d0405181e07050402090a08010524090402010e040c03060b0c0a0c06090614130b03190b030a0506060d0c080d080f0105040908071101050f070605010302090702030403020a14130f0c03 84
    0x1041172550780e4030142c07508034181c240b202e40307000d400a11245200070003141c1ca180d100c0071002e084800030b55900c0315030802800070340d903843c0307403400d40303a24072101103d0742a11403829070000b801d440040008141f00d19502e00790140c486009600c0100641484440141c0340d0203403a210b2640c8030000c8800303032610340c503100000818510400c982004c0e40e141d59540300380400c200c8140c1020760072411440c1031084881c8008120032107031b80044c5d8070070b01c0301800a1444508681c0900122102c24148600a80040d58500c0200e44002040b81c0c120320700b65100c0c00014100c2c10301c110b01a91356040003243d40a264100110240e128480740e01441d05511000d034183d0741c030002c02040340c1c403240c1c00030301c844010303c001030210700011020401e4200c107042c010319086240520744140c0d80716090413941d1941e10380060040d42850010325074028618002585004d00b10b8001641c0c840542c1f19040420150071b09000154403003204405030507100e000280594078200c50504050b18082c07840304000b03403500342c0401 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 587958390 1250 587957140 587957173
    0xd26030f1b0a0815090c07021002060106090b0705010f0e0f061f030320072c090a14190b060906040c09051c050601090c09080a0803071d040518 63
    0x145070003048400e036490040a8802690910001890303100d03c00c40021007520b0540714035104038840c6591095171580d440c201d01c104028403140181d9030085501490040c00380c582c0203c4a04103480400da605500d506440c40c000c1d024040001d00c00e000a42000c0408a204000280404851241c00c043c1d80082d66607210503c8601038010301d42110600c0e154040011030300a0f0207114039020600d401900e11282e90b00041c0c60b007607290340010301d11750407000c042c500301c400c500c000d170a600d0490480340000d08207080105d43d030b102d6201015095000381e411841240c00b04000e102000000444489000142070429040c81d440031540180100c040d60b0000c0d04a240900c1040b95509158480281c05402c10b41408600d9010180e80c10059000c102041d010a00030031500d402013488070b0740483c041890900c010100319480d409030101c1c2c0d100150b6980001d42c480c007502e0384880e5600d04000b5102c03030041e5034800c141c1700c2841c0719007107072400062040c0a0310100007030404610940c00c841a081c1c01900c030301b = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 587959640 1250 587958390 587958421
    0x10c090e0c030c1b0a020901030819090b0703030e07030b0108070f060e28090501170c1f050f1911010c0f02070e0c0705150603100603030e0d26030f 65
    0x20002a008200d0503c0b0883c0d132120f803010141000040340d4030351240d50301240311030f030082c1c04c03d03035007c0340208150110040440501c3c201020a1422003009803800d007030700e8401e001d0001c0083c145a00e0300d148982110341088403100840d004030307801005581d10402d030343e1a91400d010300307a4040164000800e25a01420220708100c4001e49030400c10901411034110300f00c03407030744440d400e0039419200003880c00306070064602a200038110b07111082d04441c1e18514103a02280aa8020800390981d03001401c80301d0744180610601e81400c652341c4488064098803840341e0f01c0c400144070420402c02019544c07010811011100740e900800154012080944500120b09410401070b88001d00900071001081e13180d54000c140410814140301555803a1070a103a110511102c0c00380f6100708104452404005464045400280c10001c150540c0c5000349245000b45100c5e001d8005000c00d0b42c00c12000e61200f85500c031000b50a0050913813880704191890f8019201c58403403450100108441c1ca008804a = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 587960890 1250 587959640 587959651
    0xa1110020721110f150106020705090a0c090f1502010f06050303270301090f1109160e030a02120106050901140319060b030118051b01090611010e010c090e0c03 70
    0x2c2e075840441c000744070030600342c015030071400c020070086103900030751080044c0441000007001500e1050310b00c0070000400c120580c000e2007158000ca000304040e460711500703d90041c0c200d103408158566a41001d4404000f5940507000700c1e642440001417440c2c80440c0400000036aa0082c030243c0716848411040c0c076514000e80e50302d50800c1114101c84000d201c41e021203101344840b0281e041080b02c0c0003070f0842c3c0c9080b02c203982c6107407901038903c01c00409c9002d0344c44080044444810a040003201ca180d800340b034040d8907040c015844101201c0303036400c02690306501c1e0f0051070100a030b094092074034080d044c68490640240707455000810a0781c41d00395034415580300600241644c0c0c41607482400401280b4605842d20340e510086051030741c4003809003114040c0c0d07003000c01404200310320f0709500d4002c180e4140792070101c1e92020088203070b03440030602c8220b40d942d140121005082503060390040000355119041c0390310f003141d205010340e00100b50300111500310114100070b94502d181c600c3c4e10f02c000c80300d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 587962140 1250 587960890 587960903
    0xb13050307030c031706150a0c06141b0307051801021c050406020c010201020c151909061406011b020112060f0905060f220917182106011511030a11100207 68
    0x20301303c1582d1400405040c0c001c1127850400d0944100d910344604460380c004041804400740750401c100c1d028550841c4000b8200034034424a1413421010040c072600480d10004a0101c104124000301e070b1003002a2007001508914100540241038009840f035032051081c0005809408900e007038560040c0301707440d40810b07040050300030040d16140540400c2401010340d03202d40207071201c40e080b4003c0d520030100742510600300020290001c861100d5040002080c2504004101c851744001003410015590b449a0a00f002d224030118055218050400354110b58800c6104140025a01000d5000540507802c01d885c0502c40d101c101050204803141048010a0303201c5151241ca0b00f00a1580008a0345011b00b015084124042c816010303203a0042c18180030805008900c44560701c0c1001e519425103481e0f482c051038070002c280015840311014403450b0b04254000d0080608240101d58100203004414156641d61003d040007030710001015000440380c0c8604029a0002e03882482218542500300300c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 587963390 1250 587962140 587962159
    0x4051908031501140c15010909050d0c0201120c1806030203010b03011401020c06030a05040606170705040506030307120c03030f0b130b010908010f061703040509040b13050307030c031706 82
    0xc400b40709408014207158104841d00054100b12140f200140800200780da001e00040150351007142808601a0483c40e03040d4641448140015000070790400050280c2c202402010030074001a24880405405400258103141506001a500c0301034180703217010b10425261031640f00c10342142280000d01400684060401c0107010380c110468061030729500502c120303602050b1020205186810981d10310b0001525074080c0401c10000d070048074040c000703402007820040004903415a41b0306c200c2c4101c0340030b15624000700d14151020320455054070303007003045c0307002150480d60020010f0172505000d0300083d00d490000080100b40e40038075100c0c10001400c03050300181e1100418010240c116101d810711450f00c40c0020000800c1c01140041c0926140010b030300ca00d04454801902c1c40100001d080b81c1041006209940e104081c0e141c1254202201c0541e076a10b600500c0c00e654092000078040e8440800c0344010190b01404928426100b81c0e10707038613810503c140c040303000032003038942a0b44081d284 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 587964640 1250 587963390 587963401
    0x230f090309152101080607020c0a05010e040b0901062703240912030b010210090c21050f0313061d24030a06030b0c120a0911180405190803 61
    0x100c4225450488180304140b03444020b03003d411514401501c02443d1141e154010071110600b0710400d50b00824500252011000820000c3e403964003a02445050140001d01d003007041c0c031356034007584409502500102c0156160030014001000b202041c0c0410300305482400c10b845040d140039002c0740e6019041c4a64003016000040c00900042820300c5419680c1354070a0114000c0c69400841c1121520f0009140042e800024240118807030500c1c04a42072000010010380d05030b05400840300c070b072000403090b038004045110080b4204a00609240300c2c030740200c02a040d0200090007028946000e0242040e42c0714401d850551844106082c0c6410102901c8180e061140200c49040c0300407164203803031090222007400340d40090380ca8082c00d80d599802481000401c04001e500201d04010302424540700500d801c030711020007040180000d8403030726800b04000b5121202010850018100399480c100100180015170044070160b0710f910608450307aa102c220030503001031181d08540010b1840c0d948 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 587965890 1250 587964640 587964649
    0xa110a210f0305160c080c0d0803011205010908040807091503050d0f050d1e0509161a0913020310091a01111606020a1208060a03020405070e04230f090309 68
    0x405000b034003800f80030001080b07454590850229400c2c03180721000c12040c1000c0d415490042d00b048003600484590348440003244040080e6030441d001a4514444030026140144c05803a4040e001408003001150204d4a00c0c1c0100f2008141ca2040ba0f0070494103c00d100302d11042d0f900c030300c805031140d0852180007801038841e41031214440090304082d89030104e02d220200460740303c030704c1c14050a959540400c00141050050f20740007620b0138002d0401c4c056002224606a00d1480740f001c1c0b241040034134100040c0108103851803100001c100c0c144042c0b090281c00c01940c802c441c0101c24038890100400d240149206195010030038408138810465613000640ba4a00d446e41401d50500c603146180c00c100f040c1080c80b501428841e07014000f16a124905241051f0450000342c00b4840c2d01c3c02005601c1e00e440c0710740c0c03080b290101c42c0800d00c0c0d19030001c141c2c0c201800380002c40d0010b00300703d500c8100d0240480440121074086607135140e00d5071507030101140000c0a80c0c0750b00541e042080000b400c0e103403 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 587967140 1250 587965890 587965913
    0x90b07030b04090b0115080a06150f030f05150f01180b0c07150f17010b0d09060b0904120e060f0f0304020a081005060a082407020f0a110a21 62
    0x1006400001c1202c03d540300d0501039138090f0320100d4001c5c0c400d0510155694040c0e85181c2121502e170701805040c0c202021003181051600a4000704050b480d05540c00e1440780e0003540380d410100004101c035050180c045080d100041d400303180684030400d03500703141c3d52203003d10802c01004030b05001246810500010a04c0d84000a800254800c100002c180c1000100010b600b0740c1c0303940c403070a8001c240340704041d004109186003100c014030f00200400804000c1021500d0320b08002400040801d0765240442c01000f04002d80ba400040310010041040310b583c0c80c94900b02c005460b90148070b00024100100c511230100c10401e400c030309004012041605001850304070307100414104445448aa41500c0e003c04494944401a1510203005d0181070200001001d0800000513100690301001058850181506094840400c131400904c0c510310a0254000c125246001d8034070004150501d002e0907819551000d124075071428002407403001c564680704468020303480503400044c01d916201058103 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 587968390 1250 587967140 587967161
    0x1312030b0103020d0e0615100909050c0c010509071a090102030403021e0303030c07060b060903030702090a0b1009090605040507020d0804260a02060105033403050303240301090b0703 80
    0x141c0a002440842c4001d0042405070000d8a0007006d5600c1c004c041c0d04888004801e0007401603004c1c1108200c9913a1141c00641a504001c0c40800d4684079620381c1c0f201c902c00c2c0400e1f00c00951070a070030b01a0b00d81011800f4800c83e00742c03030f020b0398801a21450000f901e21801c0795460150340208410070041c14080786082c03030301280c40725410b4442c0200340860b04540c4100c40f8241d01d030f500058204100000341c800c22800c0101038820504242d00341740807a03a1f9210b40400a03203d9000034001880764081c41d0042c12070308101501e032500746c00d10120040c0800b030300d5000d04024142490004a218249842a01d1080100b64018016801c0030300b002e1b101c010014100b960400009801480240044580a03003111003038262165115031090009041c80c0068114502c20740107086680e02d0f441070040c000701040c5051841c3c612040510440101342c196a41c00140280000320400c038000400e016007080d0344a00f03484c60141641c10500b01402c8562001d0003c00c40e090300c00220344a103200b640a0078001 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 587969640 1250 587968390 587968397
    0x603010c020607230d02190f1701090902030f010612060b0d0f033f05130b06040b03100504080408060c0708040306020d0b1f140c060a0b010212040311091312030b01 72
    0x1201e5840c007017040c0c0c3c0c0040000e0b1900744140c1d00c0300c0b041541c014904c9141401515040c0741070b1005885600103140103210381c000d115110b125400a540d42032150240503d0304000800c00c0d15a29104c500b1a40b048282c00c2c1c0d081c9282500300149400c05090550b1025806000120b6031002da940c00daa0030440100b0100c007007205c2d024401000307401a88042c0e84091900015440104804651010780e040180316001d5010020307640000108029070103500084200ca0100c0c00d20b82000c0800d190040d40c0c03031894030107401c1a09103c2401a410000c1081d101c1300f80590300955961003814070284544030005200b01000c000800c0030ae1042c0d800b4050025002001040181700b4078002115200300c54401d111803441d292084c008550403804180d040030152041c00d060000714000300d911600000d01c01f4800645030f00c50f41c102d81c1c2c400e0241c0398096090415294590381c59090040341d8103e09000381d80103250b0000889c000b4035258040244590f88280082d01314100040f00f10041c00c00c02c00060f051 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 587970890 1250 587969640 587969647
    0xc1e040801060f381b191208010b030415090b04030306060228020f0a03150f140c07030e01020c030a061e02070201090608040f0c0b030603010c02060723 67
    0x803040a01035203008040c0d50403e201203d0500303c0d04948540f0181203000c200c510501030300c14480180030006102800280d010f6100e024200f81c1211000c1050008000750041c036041d801c500c1032403010700042d24094100d41c00c00c0948890140d900c48001e005900c0406400d00028000914081121180ba80000c2001c200700035181c0d6100c0c0010001d5a0071008651980c1c13003800060b504100354042c082803109082000088141480b602c80585800a4001c50084007100034a860711018540119840360760340d10803404a81c1e042006014110110361024208400711800d143c03030f000301c0ca02650010810a140084c2650140c806100450415040d4014411441c00903a824008041e416016510201da001c500610b03141d8080d900c15030b410f0465205120400141c0da000108800ba00c946080844160b02c0e5420600c4203a100c4c41e80c002e080281240b000308242c98054060342c02118103030000d000c407c46400050340c85070001c580d0900001d180c00a011003200700ca00041c01005203035252980f4 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 587972140 1250 587970890 587970899
    0x80706200307021c0822050f070609090b04050114240a05090a0e040506010e130c060e1305010e060607060e150709090908091521100902030c1e04 64
    0x240c940049414901503045294001c00455080b8036003132100700c1900d40400316103030210041820030f5040c050307403001d0b00b01851042d0410904220300303c8075008050071200f09580d9594000c1c03840c0554000e0248860414000c01c3d502d0601e4081d0f0350580d40c01411085180351041d0520800000400820700c1400e180c030003008008008100422a0316035560f1040e82e9030b2042e90a00c0f0440e01203034442e40260240c182003002048001c07845506464030034a180c0c0c1180c4a0004d0f2a04040c128400074240c02550080080c5054101040046004085c2c03203522240890007803000440d0002d00c61010020f46a20000b1030920f401c00061040c10712034800020200409100a8034007412415502c16444030181800a82600000b6280080c0140901406445d6803a51000c506002c3c145100340109651001c020307810b034050081d55100072120b2040080445810055854110213a8050044082c42c0c1d101107100b0f80b00d4006c687c0b040300d2000200d403030081c0842245100d803401a80d43d01c103400c1b00b44004103 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 587973390 1250 587972140 587972201
    0x601050f1c03030f0605120a0803060111060708040b09030a09030825061401050603042d0218010f060f020a1b08160515071e1b260a080706 61
    0x100d0705010b95030000f14000b4014984007100c24541041c0d124648545403082005030015500507055400000540c81ba103034040166404400071080100030701469013005619640091813070b02c21800b803103000c8090344560700c0c0b20f5101c2c4140000b640c0001d50ba0042400807d0012008080d190700d40100c81d400080315200111600c0101001100c04039244c2103c0248462000400390240030100c640340d00d14141595445581081c00021a01c9001e0141409844101410b0050741d05600a84030f110805108202661020001d01078a4100450141c01281c2c7c64810544c2c2020100c0d02e400a1181c4880707a220b010041900340c0078100719800e0368030b01098804003130040b00140005401000c80c00f030f00b0082000000441d4109160780d540d000e20000d0003056105c10469612000410003000d01c5442d030520610a0032405d0300c03480401020007001a20320380903150f100c0c540304000c000703150000f20580919160a00300c07a0191001d1018400e08000c566164030032901c10301907000c514400c044d41620344 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 587974640 1250 587973390 587973439
    0x10050c0304060908010b040b061e07020d0b07080c1c020c1212011802180906030c10270f0b030c04150905040e0d021c02190c170303090601050f 63
    0x200040d860800c1013158280c00d0280d8030a00340c04a0f014000401c0100200340d8030300a400d4083c14150501d41e00512178a5200111100643c0152055a140340700d41860ba1303c000c4103543d81c0c1c00041041e400600c1184e02c00069a81100c07104241c8810326001d10084400382d00041c99400090150401d400780f01c08010005299582128022428543c98082c8440316098042c0c042c02d00a03004001c0e415009810741150b801c8000120b0b0b030114103449103030119140c0141b90107050b800c04546a0708101113074110001a110320b0541c80803070141d080f00f54a08600703502500c5000c040b0007520300c00b0300507002003001a55002c07074103c00c3d40741856583d42d4050542c040c2200b20001180c0001028000c41c2410b018203403140310036100034a03800741740d507500070751b91484110b00003800821801000c41192007030181401702c05481e031071440e242c01b0720308028030507480604c00c5a21840b81d12458001c0c003040032080d01c0c407071909000944590781c40c2009100070f0803d0b440c02190b1000c81020070205091122400 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 587975890 1250 587974640 587974649
    0x80a0b030c0a060201090312060308040608070c0b090313081917070515060a0603140c03100512030909101409101701050403020c01020304080c1507050703150b1e10050c0304 76
    0x2180c03206c400d040280c151310b42c4019075400c00d81032510600115448c0011141220300507e0407020650b1000390858041e0004d101c0180458460024001c0120001002c0d11104080c884980b0003140c0d10407003503603100301140c0c0060440c03450100b50800706d407441da50b00359000003003442d443c504903065071590705208841c0b950900e078450030701c1801034500b41740e260030000c0c1240381000c00c0740d9059022075130204032006101c3d20a580c00040043c2085004501200082c10003404002006c926565001d840741c00076003405000e84280700000e50304503440c9203541c0480380304060100e00622002d00b448803081000380518200c22035181e001895103400d0b160440581c8800c80002294101450000e0030013480c0141c00b41194001c4c401400b01204c040b840c041c2d644402c9958511a07444482e03001d4003030160302c0010300140181c540000c01d04c80e18000c03001c40500800300400444d1643c0080082261001c5000d501001441400c2e107414103040c0d80d807044000b140d0400c6824000c000030010b145a106401 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 587977140 1250 587975890 587975893
    0x15030f0d0201141e160e03070609031203180f230d080106050315040207020d0501140a0b0d030905060912010e03220608070c0c031e1202070501080a0b030c0a0602 71
    0x1c074604110740c150304213a0041000c01480c0c0001c4904584401c070b0280141c8440140c1004c2e0310202e0707200d40035800700030155002600342c406a035aa0741001e07010f01103500c001d54141d00300c1c55003d007486129201340c600b2040c99103c24590000c070368868035155004503408031130b0000c6019800e0500c1ca0b00e8401d241c14409280000c01c0196050301c0d00030030350801039104205216040c8240301c040c2900281e8071520800c01c0e10016160011800041c0300c8200d001c40251040d46056001072180b40340c003000f24802c02007070720180840400d03a804c0c07000280d08101c014000a030503000511092038002c004103c0350750b008241d8642114460412400c4440d401190340c126480000d06104c0100c01040e0118440c4403080100034881c50300c14050421307580100078008204c420040d5a041099020028002e1504000400c20440100612038543d403008281900d00150040d20002d029100080e408182d403010b955203101c94a881080d04003910a8110180d41402422080a0710391580d10030031008000690 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 587978390 1250 587977140 587977151
    0x5070b2214150907051909020c070f080d02060406020307120e0606150309070b07150606020604152d090f050c0109120c0317042301030605041415030f0d0201 69
    0x4001d149480c401c4010086a00741120030490058008184002140c00943d0500343c160300415081c0c103800c109810410020380b02040c10171020400103101d00035900200760780ca0901d511401550b640c1c804126a007070051f0b00410000740001c00d150007450b00000c3e01e04141c009525000c16840a40e06c00714410403c1d5403009080010b107140c031070f00400e04640305181d01842d50402070364403030721b8140e1405442e5214000150090070010f99130060200900c20600410405440300b4000351a0403080d2419111744410381c40401c100312180c842c800f80f004455107101d1240895410a040c0d5201000c2c402aa1942c5c3e03042c0000450b0250a440c3c00d6103207d1006040308410307820000d08500d10f03641180d00408800342468000542c090000000d23030390024902d40748024000c8a468151180343c108104c00400d440103884d00c6030b40d150782d5900f031b031100f40ca013445019150418002204e803d01442140340f943c03080071034084141d50301540788002e80507003500c403098400c04049142040001c81c40d0010707903448 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 587979640 1250 587978390 587978423
    0x30807240e101d0601120f0f0f0506070908030a0f09080706020604020916020a0b0606070c1205060a18080c03120f011809080a26071d040603020105070b22 68
    0x10f116001240070014000460003024014107961054140034120440407002656000d0103482e08071038455903030001441c1c4114a040c07401c0800c42200c0e1030202c40d503204150102d8400c034040c19401c01a215501c00441c01d00d628000c0c115000a5014560001e2245008000c20301400612050b4054901038000345110f043c1031060110300348009140c0106d4403489948265256070208800340b406400000d10002900e03100001078641c400d44800500c050003000340040c54840355a01118260b014000307450242e66804086003c1d1007040340d6010f03180c0d0494001c600081c414501030148035010804503401c1c00b07510048021451420380b40301030000401401000240c10003c00c4010710555000144020030300395891040e2800707400021130501c03038150f6401c0c2c140c100c0204596680c0e100780003107003458140f481c0050880740210102d002d01e2500060440810b0505d4002d0904699044e0b40d07051800b803040d241c002d00c8210152443c0c9000f0900a102d100c1c0500d40a035201c2d0741401400280724a000d20b = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 587980890 1250 587979640 587979673
    0x14130609090209060a14090a090b1f020718020409060b071e031709010e070e06040c02060402090610020f0601030606061d130b03010b130b030c0a030807240e 69
    0x15a100c0c01c02903004201c2181d9a868000a64070001001e080280002c444250382c0502400f402181a400c00c030282d0340000c0034805604400c50051082e80d00c510f000d00c108081401c0d105203980d0300d40150b440600c0c05c11507030040c0303640072103091490741c0018100381c1c03115800ca0940340ea80d8040321a0420106401c0184039180b03500441c88800300c010345d840340300070b0f54028080c0c003216008103107501d82140c0091080402034020003441910101038801c025107400c02805440c4081c0c0e04c2c01d006a140c41d000944c1540000381c2c0c9d500807034006216641c559241c0302004030140546262000b14003542001c402000420880c0c18043c61040d000403d080d403c00f1070040c03201750184000402c444100000a40684a000c0f180540042145000c29451039110100c1d000d80052249550001c40000400c0d8814204c5da01c114104102181a50320038017800041150320320f01c42c0006082e80c4800c110348d0001507802c602040304181d01520650403414a24002c804642840032119900e40200c000084842034 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 587982140 1250 587980890 587980907
    0x2d060c0e0117010b090a0b030a060306150501090506070501090507060203040e070512160302090d0c0515030103030f0c0203010b10081e100303080603070506070503120903090f10141306 81
    0x400c2ca03203000021503082e0030080c001418415201c000000061000c490f8841c1c18041000c0d00324490507650b01d003402960040200082c1c401560880d14001482c601c0c11190554101201c030140d4464411a08020802c10075510610049038150b60310300441d000110280b00c01343c014586a000345d504d40d0701c0c102c51080300c85001410384080101c00c0200051503010844060340005503010211200008004260000d200703000d2166803020300c102500003007001038013071942a03a0096840c00b2841d40a00c0308803100307000c203000003008503217003207180071140d407041a58039441800140007142000303119001c00c4c1c4200700840786000080960b030400c40d18440e014422a504100c0002843e414901400154441d900394013008003005940008510b80355020415480230340300080c40c0035a1140a840c03c1c968992088280003014103062303000481a4502005641d50400094502d103c20700050040001c44000c004c011024030940742c074800c0109201d103014010b00c0000e01c000301800d0381400c4018201d800c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 587983390 1250 587982140 587982167
    0x2161a070215160b0403080907030c03080901170a02041d0903030705070c0306090303021b150c0f0c010501080708070608060a0b09060d05042d0515090a14070f060c0f2d060c 76
    0x144810320400c0083d030b100c2035900031641c120405540344c030500ec004a074542c2c480402e0300b40d00b00040d0207210f544105030340140200d809004604402504206a040c6013440072284141c20f5001800080c01840c00382d070080100d0303449a043e2090b1035440344d0b501406c4450f901000e40003c0d5010a010800d0040202038440d1041e8040c01841d1480c0e0b1103c01400b0800c00400090a04601185071242c5100d00001e554800e00700300020b2100c0e60b101e04042c0d517030310090300c60314906106400b0001003980c0100c50040c00303a1000f501c005049800c1c009603020b81d9004100d89a007101c000c001c0c03441c0303291303583c451036000307502c0344d40030000505410303906805008880d0710b05030f0040c0160110100080c400104130510f0074610b0040362241d07440b044081d00f400805030010b071a81c40364082042c0c1044011517a801550000540710a03079603211078044034221080440100004030030100e41f00410410000448900100c8078020604814081158040d6001c1d070411030f01a512303004410011130b04a0401130000 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 587984640 1250 587983390 587983393
    0x40509010216060b040204091a240a0c0309030f030c050d020c010e040b0a0503102405060a080c0f0d020409050718061d0901030302161a070215160b04030809 69
    0x2c041107441c032800002c0c40340c005007002c0e910503610460f91504c0d01900e0003402c3c18003041000301c0c0d281401c00031005004803e07612500d010000f030031060500602c54040c020700c019405081c01d41d01401550035825400c070690512401040c00030014160070041450b0b035200759524a002181860500d00c0d05000c4107500c0c003990000c0da118580e6980c01040ba60580c0022500412154800070100743c2e0000581c201c15090700a00b0071019021155411603a0620056203481800a4014200341400c2400b070158940c8440104024a40c107440b40001c540c20070072080c0c042c1d26103000b0100e0400e143d0701c5050744c010040d40200f41000050784a2281d1341c1e01c080c05090035889200c88155500d580440c5024450600c880042505071000f101c2800c0492808058501c0d9802e50f1281070207036a841042140e01501540d00b840070400c26442540321550031000040e040c20489558200301110b12242180b000000c0144150510552040100140c1c2409003042c1d400900302820002d0505e80000c2804055 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 587985890 1250 587984640 587984647
    0x1d010f0609051308130308210f0402130504030905120f0f210c0a1a01080610060f030e0c033309030a030c110f010501080705030f030d0c050705010e06060405090102 72
    0x1506905204903d0300341e1101203140d4a5035016000408110b4540010701000340114905150448200417101d034000e624200401554031302940c03075480038044a0094100058501e10800c02a49070080c42e002442410304a91158954000c035a002d40704088002c0c5030303804102030784000001801f10b08a04035000d03001c0e2815100040040d50000c442c001d0030034a9150000d1141c207041420b1250741c2c0300d03a92000ba417004a000f42030620005040c20300401d00316000e54030104000b40c299205610445443c0d031900320007600c0030103064000301100c2c450752000d40525040d05000b90b40c03e1002c41d100700c3e0b065001380d506a0101810030754010301c10043c0d290000401c07041c40310024002007512244003541c0b03800304009104100071034044500400c401580c2c45159200c8400c0307901074114505070f400315022214041e96a104050390741c665141420016001003000403000b581c09d400840d4000d00301c1c18182e2410443c1d50700e80d804c494000f1040302041d00803409101c0c451a09004082d0400c501c0c01c000c2d406d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 587987140 1250 587985890 587985901
    0x201020309100906032f160804030b0f22030e010c0b011d0f09070e060d0209041a090309090615220602070f030302061f05030f0c211209041d010f060905 67
    0x90012100501b0900404500c441c12400e5151480d41072a602c40341d581e131925520b180c080e4201a090701e901d0003115180740001d401819440243c1d4440d03100107000780308415903403000d1b42c00d0b40710f914410781000042c0e070702c460100c2c003900000c03402064400010004001c010104404000c00034200840d020b61907400d00c10a005c0000c0c4e50f100382e64410f0402c8a00da101d550005540e010000302c000e4002000008020a12101310700c5004103001e100c80f0b001c0309540317002c043c546134411030303281c660b12500e940041002400d26444c0c5c840c2c40e4001c030382c0e55441c02401c2c0060706071200c4607402c0b41050100c4041c042c44650350500044000341080b0201c004940c1c02c1d030750040d4540070002c0c42c1ca4880d419061450502d80003000b44400240405000d86480c582c0700c8010301d132903076a10300d80a0b000b20189045040800c196955a403242e5235904007801e41010803c0c10141c1039800b0408060f4080d48500e1104200000003808200c4407021800015200c90b049000800b9144280d003c0c9401301d10704020440d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 587988390 1250 587987140 587987201
    0x30123070e03100c1b030309140c060409020304020a0803072105040f0902130f080a020312130312030b0406060f0f020a050d0507080f1306092709020102030910090603 73
    0x94502500300443e4104c000f503400c490084200e0443c0ba00000700c030f807114041c9a015482203108600a1290b540381280341c00300d0760f5072148103482254000408002c1000380203442d0f030143d41c00ca44000c0108850300d66801e4182c1c915003000c80c013640c003070b04040d00d554090100b40101d81580b0741d06007446814540f91016a041111181c440c0408503500000d01c19500190301070b00e07502414500181c0303502d6544038203219680d1100008200c0c040d204a4910509144e01101601c8607001b56a0140c1e60383da05580d1040340c2048041600020f050312800d6080b040e40d594001d03100a0081503480c490402001b0030000c0280710b05850a4095421455040340440e03000318072502c0d2031400e401c00b1039a43d5180d213001c110f40e03c0344d0b50b01c4803020000803a00341007687c4481e00303260464410fa42c41c407559589914540e0108140d0191480860412082c240030034007168200c2c0c0c4160340140150303810000020301103405032800c480c8017030000b0f4010300c00380706c00c0750148101030032440c1d50600789460805035217400 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 587989640 1250 587988390 587988403
    0xa0c0f052416020409050d020d090801020412030e01090b07080d050a33080111030702070b0c071203140a0801050405070e01020a020f0402072112021603120b030123070e03 75
    0x2036004079800c101003003d40d241c81d041504125400411205a00d0403004000d4031508080e642d14001241d180c2c000462031414002d440648100c0b1030711010510040c2d8054455010911041e41441519400001c41c40306000140141a001c0c82e6181d40c0c03900620702010072503100a0800301c01c00d207084020110600c4d206000c41c00f28142200c8202040380c0c40c1d030b2440403448a980641242c3d801c0051840158042070042d5000d0b103899021148030341d440b04400100e0740a00c03107100c0d40c6a4045101004141c420112403100c0350f020f8105903411f40035074070140d09103074003454134a0042050000104480d044c588a42c5501451300d1402070310381c11040c2e0000b5221305420380081d1107525064000002661a0741c110790400d648007280740e4009411072610b602c0003c4c443c08800c041640b40c000080e504c00c96008a0b07000f40d0080901103114440c80d5030641d9445044008154015a13070341c401e4043c0d80702481154441141c03d41c11030f107200b8203194681d0000400804003c200f1040042c00300c455200002c06 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 587990890 1250 587989640 587989657
    0xc0e01120308060f0f1005070212061b1804021b1015030b060f03011d0d05041d04060b040f0b04061403030910121a03060a0506030303180a0c0f0524 65
    0x145130040400010f80c42592030304140380d0000c1c0030002d50080e00d800200410003980700b0348241c0d00b07180099000c19140c0c0c0d8210762040701451031035925165041c49000900d6101c04010b0801d110385054004581260040700c00fa0303400388805580180c3e81401001001c15400507104103008850740403500e08120869480018602000341c00824415030b08c20300c00928042c0d01400800001c40e00121280740840c24015590b00d0780111a0003203102d5200d00100c500703903020f8031407402c40104c0b1a0381d00300d0149d00017403007905c0a41d650000040950390b280101c449042c0580c06c085030035003521081200722800b540c0024a2a050485401c0d01c585010007960500ca2046860003145810103e040c0e503000303258a070b180907417880d000010004815080c2e00c2800f500c3c0940840b0000d50b2100365010440b1416915039500d50b109100107901c810303000100c84402083e1805850504000d41c1d544423112809801506c240500c1c0182801a81000040e01c03041100700300720310a14004000301210766115410f03c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 587992140 1250 587990890 587990899
    0x51005090103110d02270a030b13150b0a080a020906010e18040807060c11150702160f15180605030402060c060a0f15030336030c0e0112030806 63
    0x1803440e11680254800f0500e14144820340e41e44100760030b5808020343c8001500c2169004600d092083d008112170309040524003d0540c8400a0654480010709500241543c3c1300140d590700e0360b000540300b420080c03494041b03480041061502c5004200b10f081741a00300944d1a03020903120400369980600d840c0d00704100303080030314071138003000081180c03020704621002d005540c4c2c00a100402050400401020b4047c40c020820704c1a040411034001d4210704000c402c0d42c0c0441069003c0311956204d440c0c022001d07004590466004400419681c00d181c1d0000520302c110380000c104c4241910b1403907a48240d9850019081400380c0e80c8940164028000c810810074040001021519240102e8905000c1030007200d50603e000c404000c00707420f03012900c00391103040a28941c5401c290300e641d90203407a03064503600b0b2459040f00803146e103108102c0d03804143d400c80c6001d01c00303002520305040d40614040d5074a1034800f401c00c6d41e0008584070681c80030181403c3c2d60016400300354054400c0d500402c040742e = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 587993390 1250 587992140 587992147
    0xd0e0a0905060303190507060c0503010b0a030506120a0b1b030103081902070e1614030c121e010f03140714190b0f0702130605010503070c060e1504030315051005 71
    0x8086850740c002c140c0c81c6507807905c1e480103164205404c107000e005458130425050161080d509003c5925000038400d0752070601c41840717521101c502a0b0009507000b070004d00b0515005501c41c0343c0c1741c504030b028032081e038150300e0303040600c0034800c480c840c495011210307400110714651542e502e1814900c5908128003e6212001003200c045109100d950024200c0368407032421418151a041168448160004049140d000c0b9800781da10740301d8162072107280701c0114642018100f0350b000848410007006080305105901507140c80b1816242614040d240410140307804078203500c1c0025410800a10003505075011000030411105039007a8081d040700305680f09045480042e902410002642d041030008500100d8a04040074100f000381210b40d00840c0d00709005400b004202003121490300410313000810400010350254000c040d8014845d1003680300261407100001c440341045603000c0e59170a103a5444040c001855450b003c0d001c101c0d80c000133015100ba00c0c3c170740000c0301070052840b02c1d0203010021 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 587994640 1250 587993390 587993401
    0x9270d1e0203090409030e09070905010e040902010e0303040b070314070f02130213180b04050f28050405012315120102160804150216141c0b0105030d0e0a0905 70
    0x9006440b6501c0b000b41050041010380c1c0350180850408801f45401050000300040302035100340c0c002341c211030b010b850f112800d03500d86041c0b0001c0c04101e071060f410f1003101d80000107907480400c01440105000058036854030001e181c014010785010621000c6440d0074054400441d042b204420b204960489440b4502d201c4159007202034000c10540442c9500c101000003100d00440342c03150311480242c0c1040140c035014404010840b034050390482c1b2441c49880000d9110001c030b111044401c041070000d003e88041c184016019200100d80031100d59444440032640452403848290500103891050841c40c0703001c0c0c2c4525070245266000d1071007244030882031403880f076080d41111190308165104030940c0700c603030070005d4260303116201c1c4201014203071b403406d41c02038804201021450009000c1c02216071803c01094645804160525400901100b10201c0e403a0102d00e103448051041300da017542503240c50101403d142c000c1d0200340c14041105080b0a01d41c0d144100d41c4103480c50b5010001304ea031a81c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 587995890 1250 587994640 587994643
    0x506070e0a0e0f182505030102040308090d140609250602190606170f0d090b0403080f0906160204052d0a1b090305071a0708160209270d1e02 62
    0x50041c207040c50040a8090074954007400c8403540384401c175007940c070300c96968400b0300d8200c0c801c03440041c10401081c0844102413501443c02080c06020304220310b0180000c5038468280001075811f8a040d0f0f0008889a8940040640742c5948400000a0600040ca80391000c1d485841101981c06840318101c203003020010b256000d0300150440305820042e40081c5100956118280d0717044161034442c2d40c0c80d00440714414003900013907230045a16907042c14a0f55851540a820480301c405150741c0a205100b20350b102c1401518800300c28041e00a001403240c0107000458101030103190b1440b08031018070301c000c002d40f14003450b03944405103407890640d1800d0701c8600400100000e58411030000d204084410350103c4ca60095a024405588030300d5070324042900d0000c1401c84080c2d400100b4440140800d121802a16805a4040c2c030140c03006103070b90029595201c12100e00e03641c07491010400d40c1382440881800e5011808400404d00980c0100000d0074049400312000251581c80d0b01c6449010710 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 587997140 1250 587995890 587995921
    0xf0a051b0d0906020c0d03140d02040b030f27060c0f040305030307080708130201020c09091905010f06060207030816020105120a0f0c050a09150302090a030506070e0a0e0f 75
    0xa42000da403004107488100030032000c00c038410f880c014400c1e0380c000b440d2407400d0060741c1045580340d103503500703203811100c655040c642001c078801080550a100c0000c01c0120440118420902c107400c01d1400e10306000c000c42c03019011181e012001207034080d5540c0c0450002801f81d0005408a0030729203070441d2102e41c0d0800d00c59a04010468080841800400d9400032103540c066020394981040700e0351485a25034200b0741c5014040c1c0142d00c8000a444581032509006420140000540b1410300c001000030b01104043d40044409070f40d11355418580144610540001e0101407028040352459030701c4565450017040200001507002d0110b5804580c010000c032045054182c101d50001e242004110f03000b0030301080e80900035424602652046c510440c12521282004e0b195007000904007421030344103080030143ca01c181542041000e105545004c2c540c2c006500c90300080041380b0f00208010410714070803421074000e0380c0e400000c0c4400d0401e0035480e513011281200c19145a82c501c4100c484030039 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 587998390 1250 587997140 587997187
    0x7051309020d0501090506030609070b09060408160306110406080a0e282009160212040806040611130905040503090406090c020f0f1e100501180605060f0a05 69
    0x207100203659804100c4640295040390481c140c2080a030340d5a030306041d01e490701110b80c00602d81102500b4092542c1030700c0a0108080064404da090a86031840c1c1883c0c140200d2207204424144a001c104000e582e0103101030480840b9a800d0806160141c0544000c0b005400c45440c9a150380101811311700401c0303211406110346407141e090703c411000d02112100c40c10005d88400018402c00d40881120018003508410301400c01142d176654106c000a004444c0020101103000344031110481131104005440501081e002800702414035141000072200c1d1308a160083d110300744181d891040400302c440045514030400415191740e5840c1103400c61051080142c0e0107860030b40701080400081c1d10440c00b0718419002c0700c100c20b00c964030117a41c603504035500c150030b43e01c08581d000c201450501c500e130803070550030215074a43d148641601e0540300c00342c11210401039046000c01c4030725000e0042400900e8280d82140c034201f004a90740600b0310440030288280100001c036441c110400411102841 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 587999640 1250 587998390 587998409
    0x11112030705030a0b0f060906070f05100c030b1801150314010605040602060915061002030904020a03020304030f08090604030f020a0c0f050a050f06040e0c0c030d0b01080703090b070513 82
    0x7854120070203800b54200b50f0780780d108a80b40140795501400e29400068011200400140c200600002003014aa0020004491140181d20034200182040140040d032004501002c5065104400e00500311682028040e03c503500403050340d150b40ca19660000d0540e04c0124200110002c9841c1c140d020b080c00402c0d0150390a843c10000400c01d80c40300180c41562050f07030950768681c40d0200d07119603400781c529000070300b02d28285c003140b80c6203081188500101d0850050368180310381800010102d80001081c140030235000010841010b80c40054400106503504000c4013605007495400c1d40c0300310045c401024420a006100441e40c001c22405401e0b50b400070703012481d151aa411001c0d045030314410795020780f904580c04951881c1c00d20009a4022010700100e0030986807481421503110084c0401303810f0b030b504210701d501e1405c0920003010030075401140403904441100004100200c0201080c08040c07800f41e14400013080c020070b4a42003200c3d80b030500d8440490407903051201d0015880344c88103 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 588000890 1250 587999640 587999647
    0x90714160f0303050c0a0207151202070c1707030302061914100f0f060e0f0612010801020a021221190204030b0f0703020708030a0207060902060408011d0318011112 72
    0xc01c114890300300340261190381c06204540b90071410200e5809200d0051000d03822103034040c05422801205140003000e146401f0040b00c80342c907960b4003240c5c44910300360b40702d0800c04818010004500e0b589a9102c1c01c420003084a01e2444d1002500e03020b024200c600c14410b0607203240021812900401110810102c80c09060705140b40f442c5001d1103244201c06030640a07200005050740e014445d901182d40e141c40f40000e81801e8070070080c0300350031203000c0c5034040703001d0152038039440c00c1204a5010346414400141e41e4401043c02910707203203140100e1038030000c003003010300c85288109c0f000841da04e03203010600c0c0158444081c1c5400843c10078006100c01440800c1c008180006201101d0281e070303000300103028589812078110183e10600030081e1102e00d04201003007408040390b00412565000b0000000d4650f06980010f81a5215a101c1c0035560345521f5000c000c0914107000e032501d010264001c518001c1050401e45580d0041e404081c1441402c0e0004d5000c2e40d0140310402c0500c04030131505a5 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 588002140 1250 588000890 588000893
    0x1002060a0b12031b01110a1107120816170a0c0c0f030b010e0c090a0306061e0e01090b0d05070e01060909140c030402010215190b04060509071416 64
    0x1a54002122800344403418214410101d00340507041e81c528095040c09549800b007415440c1c08110504800c8102c29981c07a58030301090708141c80501450302d219591440c0d110102910289400701c1500a17002c148801c81c02c8000040c4460212910b900000d01500c60380742c810f0501c9540d00f42070f103103145820b50000414405850b44080000c04039480b6019a2174950786407141d61543d15054003000380170030a064014000fa159507030b00c00340c0c003a103e54846441e2485440100e2001001a84100e62164880c0c80600c420714609030404142d40c08000c1128030385141003d00c905085040c840c4424480e610a9020343c01d803940308540503459000421210300c0c070b607261100385c081c61007481030740000741500d800400e90040700c1c010700c00c4264484005411a454403000f28103594400f520480c15445600762508410200d6110b8501c00c0d6184076444581c0a9006402c10584141600c29031140b40780c0042805036a0340d041c0344540094142c030700000d00159481418890303205098030071b103095809205520 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 588003390 1250 588002140 588002143
    0x18090204050310020f030601030203100f06020a11040506010f08070513031209050607080301031106042606090102070c0e1503030d050103110604050d030c0204110424052113021002 79
    0x71035105500300ca80510400b2540070403801842c03d06015000c00b003020038075079032182c1c000c0c0d03400c1030204031001d100b2a918429031030491421b9002c10050b0304581480000d12003420702004542c01d0580301400039242283c00205000401e20307e20040c41544000300c0c4120340b09500b07940a02c50500380c040c80498907810f00c0c05008aa52003818001040200085264107299040d1140a0b901c0b0718000e0550742955075800710b0100c07080c412600040c060200003a02070030300340003500d9904030182c91040c80403058810340c10408020090307015680100145000074a8042201086a40002e500c2c20f0300c0d1110401030705228072000010350325104c0030901c00e0010b480c950106049a03c50400c01040300202c1e001d014550046105440d4824403124210380464007a0b0134405405100810014005900302c0b200481a00715801001c1c080481810f54400400c6807034003010b40c1c458909006041155200408078040c007080390103c12001c14501060445030b640c41c00e9a0900d5004040410744658000001d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 588004640 1250 588003390 588003397
    0x12010506011e08040219330302040b070b0405031e0306030115050307090b030a0f1212090f0f150203090714090108030318011104030809040f05040305160f0204050c1b2b180902 77
    0x500c2c03000c04032560002d14002e102b1582281e8050f0103850800b0440d407034500c40c2200003881921203000410030145103c417541000940403803080301031a12400d011081c1801c40fa01a0183c0c403c03445610750078000384ea00091448110f86842c0d001003451580107010900f80507441000a2110304c118001c1d10400c0132603070400800401d513555160881020f000c2c103600351581e030000130b03200ca05004104004200a0141c02ca1aa80544400d0041c80881c0400b14100d034000c9544a0103500241403e01c0210002540203158001c00c4030052420f50418031500e48a100c0944402214861580301b009461000c1d0803030042d4820382d0900c01d0321155a42088069540f03c5601c01d4415841c06040c0401c007841442003070f00854060b9102030404410880300603e400b5540810781c0d250b024484d02c00300581e5140100c07489104429941919800ca451080d098141592503000c00c0c2d0300580c031154001942c0040c080340711051010160018900d0700310541d5401100120f0b564694442003000c10108010f0300203 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 588005890 1250 588004640 588004709
    0x200a020a050a06060e0c03070f0318140705040b040908040e06030703150f0f09030c06050c0c030f071b0608040f140607020d0210020703050d0902060912010506011e08040219 76
    0x1c408170f03070396400002c0310600c822110080070403c01a07007006200d1095111080711050000f00b200703c0011a110700c105800c0402c0b501a2550202000f030103030313040600821030b1890041d075090140401541e00d408c40750080c0d0045056443c1980005101a034040180c940110b0300980204480303840d80c81c0c80c802910500110180303aa0401c101641248224411b400001750140d4030310101200607900c000c00780902410f507210340d100a1008a910002c24070081072880003c00425a0310600fa2514021544404485903049040039070200441758000840302d41c010340c404414440140e191802500c10964030500038554445e040401500d10b40000e203440c06015541c080b01d684805101404081c1c0c0700d06000140021800c1c003045052a042d42c1080640c030788000d00742d07400e01d520017001c00c00031181c0c12418142a9110030a0007007a50b000141c0b58a0000d100301c094844a22085004d4849400904000d020f03d13040c19805420300d0310022444050080404800740315030b6007104d60003800003281304 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 588007140 1250 588005890 588005909
    0x3140105160f021f0209040e0102031f03170c190f020a080d0e010305060a1d1812090105160b0915090f06071b0501110408010e01200a020a050a0606 65
    0x11050107900507000e500c2d46200e90307401070030000600490710510800703480301489002d40074003c001c4540e640b8014400342c4007003800010784038070f01581004d10b65508101c82c1030928510701014401304143d605d0300c0c1c03040c0d80011640c590300e944e2040b0081c5042c401c00c0d900050803610031120070070000d06c1d000a82c100c44c001c46801d40919111808162101d07200040c01c0089075412000f901154001d4000b21340c001002402c80c0741444d610b0105542341a45448410345229005041002111070141000a5106140010405802000750501c1180704810300380d4184038004c281c1d282100b000092059110b50b100340400300a062102f5559503540100e401e1940100386c110001d46030000c0090420030120210008281715100c640007540ca143c50010442d2001180108030004200240075016031143c40760038140d41c3c2d518000559084400c07181c0792201c00d90421042001d10b00d0400c0310b108008054102e13076940d5079000c420607450040c40703000c018030314040d01280c201402455840441200e00c00710 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 588008390 1250 588007140 588007171
    0xa140c300a0c171204060e012f0d0c0e03060a0204030209060418021905011b050606091e01080a0c1706010317071e020a05121903050c0307210905060304110a03140105 73
    0xc0c0b08d080e14186030403100c02030030301c0000f150080c0e1030142035101c0c1d2411152080c544400030020100751000600b17000c8c049081d00303401c801103042c20021a83e205c0051081142410f0a60340000c0c141800036000d14840c81c0c82d1034201b202c600302c1031101d0044680c010400794101d400e41201000000c21803080601046c42c801c07451509003140b003100d200039903020000d0310296503181c1c10440d01c0e24001d0b0009144c9000e81c00002034041c104d11a840c00381480c0b40042c0846803291038180c9070741c94070741c2010801c0020315a10b1420031a000401e64190703a4031000a84481112400364655400381140140c240c0e91260318007a40310180400030700e003490090311310290650701c44061040b01e4a0017280210f040c3d0140081c0e456000341c420512001920030b16203207280016100401d881c40e0030050050318150740f04982c445081d904c000300750042c3c1006003408909a89000009041408002d102501000f01c5e0041d0b400f0503030700e800442000d903034080b0224401c41100c0818034000c04084880c07426510104 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 588009640 1250 588008390 588008411
    0x206010515041d070e0d03030605030715170601030b0d030903020a0905042f09072006060109060c0c090c11010c0c0f02060a140c300a0c17120406 64
    0x1d0007100e0a444000071511030154407400f044000e200001c00010800c102c3d9a83c9090300e41d00d51a0200764580642d40100305c6a06003c100760410420354030000800b0b2a1203030031160103030449100008001e10900454060fa200001070303000d00351070f091903030b0b014440407440b00415400c0051181501c2c001e440b04940769466107800c100320707842524040c000a0a00c10001804c0c0c4450b0000d00c90180000001d61024058001140e070000d815501400859495011011100c030041c00100003440c0d10700c0100914140360307002a00e42849402072004100e1051004000d208111080030010301d404041004040943c64004041c0070051551070310070750801c90701c1d01c284c0f40b16404540040b41c00c00052070100116a00300685a4422201d24040c0074442942d4100d00402a0141114060010280c108002c03929840e1400f80f60348180700900410b0320144040080101041d528440200c3c14581d942c0b21613401c2c14000e00141c066011500400001e00c3c454032038030b100c001800303a071040100f070209220300c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 588010890 1250 588009640 588009679
    0x2070512150a11030f041403070f02040f0b150a091d06122e0e01060825080a12170421020312041104110c060115050a0c030305100801020a02060105 65
    0x2c3c01803c6035400003d01c0814031800380e01c840c0c00d0300700b403152191900e140c2c0c100c0c80c9a41036400011080d1144501d240214040d410140a22840c0540c8004204001184600001e010b0740f80c03d81c0038112036101040e2244041e0044461741d0150034003015007071610b41410711070f0f4408038040302c0c028010f14410b0301e00c0c54058000502c0a4a50b10038444010b446150140022102d01d0303440d0700455501c0d140c890700c0c1c04c550000e108500c05002540045d08000c02401105802c2600c4030402240c8620007400802040e200810400300301980444030842030840b041080320324030303042411100c80148120070f01c0f04204c010080407200d26071548180103100e4183c00242c1c0c4074003401801050f100c114000140004103038a641d00c2400000500001c2e00c520000c8804000c1e070440c109011030359000000500483d11054540d0031401414641140f4114458030700428281164400400781900c03000400c2000e44000080303005800018000c54071400c50140c020b68170442072060074040da80380800901030102 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 588012140 1250 588010890 588010901
    0x18081b090c030601141b0a030e030a0b0109150e0127061811130b1308010c0f03020c0712120905120a03210e03041d0609070804020102070512150a 64
    0x46104007282156034403001901c6200000009500107901003140c0b4071020350f42128408070308141c10003411451403520b400382c00428031100003071080c1d1112190000041c003084945056034040e04010031050846c00c240c001039802c580003c2040e0103641c00100c2e0f8002003c1c06120903020044800c000c122040b9880001c0b04c1d00b901800d0000301d108401c540c0c1070b0582c0c0c0c01040b20041200744035860250f80640e06103171040c03070342c002c250541c100065001080c0054110b140181140303800800000c4006000505840c0d6115444420301d0b40101c7c0e90046d5240c00d020480040007041b80340104c401d0646442034824140d46542d00204e4240d00c4046418140030ba05c010ba0406110001c0080207044d45007a901d445851000300b20b0320b45030145ea405115040e003d040c1056410000440c8c94a050114032001035108070000e2400398030060810440d0355580029540081c0542000c210946460004030306210a0f80c1155030000340d4a40083c03414100090310032a20f4409402c50034154940c83e2035a82900c2 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 588013390 1250 588012140 588012151
    0x13151b02180612030310060e0402030f0103030c05070801020304111905060a03090512070c060807211116390620010f020a0e010c0b010b0a18081b09 65
    0x708060440034a4501d003014480c2c010100410b00d041a1200041d89495940300710744425403001c030003400300701d40b84e0050007a1038884000c0780c040d4250f280548074045071203014800a41008072280c14181480070921410015040c2c800c02903650f46820b050003d000006840601d0103140350780c60028203031000c3c000d50429294000d109600d00340041000b00d01518942405660500489800348400d1411400a003480341c460507650070102d04e040e03c050800500240383d0024000c0c24401021030840d18040c56000e008118800140c05610a090000303e000310309400e2020000080340f44188140b084c1c000f98104d15000d000000108001a10f40014000c1c030400714403006600424000d15001d42c08030180102241910900200d007012160309580c0422989c2c1420756002412702c040075880b01612800170001c1c01d040100030503aa6858206000c148500010303013030007007003041c2c10b40d1060919400e1810b07070800c14612580c480800079140c3c10603206c46161070b43d0390106903059080403880c007841034 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 588014640 1250 588013390 588013399
    0x40c14040209010e1e120f0d0503070903020607060b280518061c0213060f050108060f090403030b06070b0901180305031812070b070f18120813151b02 66
    0xc4180d44d09015001c000b2100804c0c00c1c001201031007005840702010380e940c2d41c80010003007003913074052445181003116242e40c03035007080010010032821603008042c0380c0403a44d054401e039568142500f0400014002030300895031244240e41e11450002c009120f42445020200320003603a00d0b518401c000314080c1601959a1040342500090b60720301e4418101c80340250b14200a10b051801c90f800110301000451000d10103a503101001e001507a200c012207005008203003009005070400c0c00006240b00304074601144202d4100000030205403103030b0400c02c2d0b0404080c00780f03600c0382424a442c2c1c44c02d800844200a0541c0f038a200801e000c0c4460000074040c43e0141c460902d192103042d48152040da02c1c001c1d400311442002d000d404c1c00c2640400420059000315100c009505090800400d40140303184984100041300e00d0090800007080c0140045600d048080d02c1c800c02d8070700d802500703409052094224002081000204400341d54001d034603403d0301c1e80c1c2d071000407820071a60b07200d201c0c200304010703401 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 588015890 1250 588014640 588014657
    0x41205030112030e0f1f0e0319021315060504050108100b0403080f07051207110904020306010b1602060f03010806012103030c05191805030111161406040c1404020901 73
    0x403d0041c08500d4a401c00034218041c50504040481e90078400c001ba042e6030814010340c01d43c04154405e04011035040120090824044041c038402d0280c0c501100103807280000c10f21000c00041c00c0da00c2728240703085821096820305d40e44c0783d002d0040c1d0050f100c0d280c0481d2001000441e100d02c5103203441e0645051070002800d040c1903807a001c109801244a020261b0390402107000402e004122a003ca1190600100e40d5030b016031a0070b00c00305100c41c03080c1d405461104203001c010f0f40c02107205810345030101806034440c0e03070319401240500500840a5040741001408003125007903100118184d480b02e0007158400d03603032040303528400c1c900425142d10642c941c040007000a44a9000300c199100b540c500b460500d20300c0e006800600e0303100030342d00002c40d914410840c810319041c101140102011002040402c1c60241c5502c03c0f4400e250712409400d85008900c410400c4100802e01c035985110122421031500c2c0c6043c00014120b401203016500340660b0300007580ca041d001300c4d83d200c0300603940c0840 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 588017140 1250 588015890 588015893
    0x41d0108031b1002032d160e22021b0a050703060207111f02010e152e030605060f0d050c01320d05070f090e190f0203041205030112 58
    0x50307a000704800000b1070155066620480c103203800514000d500c01000300100c180494081c140800316508490005074002d4204042c02c100b0a0301d02443c00c031541411120008043c4c00070f2512a240385420120048641c0000c0e201d000d02ea0103000d00000c40026001500006c2049503a20900020010302e1580248001e20000f56a41c0251240300c0c03050304035042042030200010411441d40380314843c60f50311340c0542e00f1416424000c0c2502a10340d04054000010010700b00c1c042305100a0160b4003142140840e10500d0041d030000700030344036411480d001019107a26100014003001e8612078400c0348100c80358490381c904060b604a8140e4400c3c005d000c06100e001c0152201104881c07826501300301c40312041d01c0003581d246020440314007101440d6559020324901c80803600003034900030030407140c08505146182c00290603000e5941d1307460510207540c3e440b08140100f21402c440041024280603076811000e09540145004610806802c5e04c6c592401d402264180024031078070030700aa9482c0f0304070 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 588018390 1250 588017140 588017167
    0x304061125060f090506280e0109031b03080c06100b090117100b16030318020a050d0f0c030f150905060c0c0f01020f040f0b18130b03070b041d010803 66
    0x1a103100c030740c2c20005040c0342d4400c0000d14980040f541403410507545120310301440c1001401f44100354040c2407034817103d41d5410000b00121100d004c014032021950f800340c00e0911340c004402004542c00a8011390f50700510464585608050b546d00310b50012103140441c9000010040c2d03000c2d0740341a50341c1da00e0b20b444007007101800c44010f409214000d0078031001040c42803000005054200080c107240f410704600e440c004045a02c00b407410b41d400a0040d0403d00166900d582003400c48001311000c144e11150b81c10181021114214010090511a000041000b80b007840290300d0030301072540c0707000448010002c0f03015034401c8040108640c101c04001484524020068100546040b0858004000b08030140d1b00b243c0c40600402828080031400300403030449018a0310150041c26038050811003800381051400e41c0c0424201d10450806482c01c400b845c05500c103130640c400c000c04595205994408a420a6006005852003407007a8014500d4050316080114100ea20300002180342c15079652084 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 588019640 1250 588018390 588018407
    0x712020112091a0a021b030702031e120d0b010306050402030f0a1a2215030f02010509060909130201080601171801150b09131a010818030406112506 65
    0x100d400d03c00841c41c203e0754042090101e80300b80701102c40143c1e00c00a0a2400e03000d2480081c10407136551003000a000181c0b000302e07442901031981001000d4240d072783d50806050a4851b00102c200300e6001c589820a2080c642041400c032030207803810020b041d103841c10300007070380302c11140003004810400203d502c9025941c0100b1095059248005c540c050350740c00146205080301060103900da03052024115000f6604c03801000c018140309001c00c0c1480c40ea0380d4000d80090070000390603c00042a04146522000120742c40c111700140f03600711900c1c10780c01d21404460600c60036400200f2281c00283c03c0c0d40640b42c00c1c0801000b1924a11150387c03072600b6000c60900b0320116540305d54a071070042c600d04190841c0754001d0070251005a0300c40000c4828401340c0e00b08590388203211410283d00d481499180202d406502000b0b20b0304412580d04c0102c50460701003814203100d1070740720000300041c180da44001d1800b5620140320965045d4500110400400b25204400507901003011104000d8540038001c203 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 588020890 1250 588019640 588019643
    0x61801030b0d06020904063623090d030510180906091a070201020403150e010b090109020a0305010e0717102103080711071404020702060f0903071202011209 69
    0x3182907281d52010034404201c800c000c41c0c03016004075041c2507a1030b141c013520380644000f400c4281442071000803408902c03140b959141c102201c8103403114403800980c111403c5603000111042e900d0304140b40f101c01000b408c450b0081d89005100380c41c56010302ca40a060300030035103101c1d500c024504040d00c0016550324041c0310380e800e50741d0b44202e40016003d03006103c401c901070805484904002e0030242100e08006000740c0459104120034400a410503c240d01100b03031031000020402aa030301c0080c0140588403855511031109400003542294079001040750344195682401680d0fa2511521001b42041c1c07106404035500ea08006100d400c00c40c64642d10407529803c0341e001030b640c1c405d102850382c824a4048a044100b071302400506800600702600000945010000b44054449058441c0b840303008191150b04499440d00c065902e9030181d0b40e12580003062117940c0c41000342a07410aa0020b48110300038001c10310300184002400300d65480340354040c3c44800b458042101c85000903c6440ca0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 588022140 1250 588020890 588020897
    0x13020f04030b010b04440a0b1906060e0306040206030717040c0603110705250f08030a20191401090308060a09150b0307021c0e0a09050105061801 64
    0x40420720a00082d4024650700300010740e9181428111403569820b20226840d018440700a080740789a140143e070440581c560800d590822008000c5003806150350001c0c0811041c0d5090001ca124001d2030882076046800c000c010365540c41500b603c80c003010000159141c0c011000260150a0004c011a07020b14a841c1144042030075041040000205039025120315070287e00c140140340e0140b01d842d40036001703840d640b82000c28950341c0c01d0750b443c2c040310f80b843c080c02c4844030100400c62a03c041c101400309200c0024003039407503c9580d41c2d02e8004d000c03490000742d90080d640c0480c1d15500e071072065000040340030f03150800c0c2202850058502c0254201c50105402c014101428020300c141c411b410310a43e2201200e04002c0104200c2c281142c102c07010243c9020044a00604c414900900302c40e82e40305020344a6885030300503802c203421542100840c40d040d0200d50000d40d0321004d480f0440c9402c503200300724103880d0701500c000c4403400d018084d04000100040221400b003c4d4203643d400c40140b5 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 588023390 1250 588022140 588022147
    0xc0307090f030b01031b0503030904110d14041a0f0f060102100609050406050a021303020f130c080108010c0504140616051b09160206060105130e0c0408190213020f 72
    0x1180d2900001c1250310940307200d5500c400501c20400302c80c5c03000c41000f0140244440140c100f00000f038692290050003440b440e9205151041d43e5221800c5d40c941146d0480c0400041d840c00450b880c00712000c5900f2110302003698102d604082070205003502514626200d40400c0d611808a2160b00c40c026001c0e41c19485170b41c03130fa0a000c5c0b4850146c0405000d58400124950410345407417815100c0107008503e003280103001e130801c2c0c880c01d48042c000720307601140c400d00e008e10040c000c103040c81410320080c80005d003000c0c20f00010781e0700b01e00181c3c103e640c03104c002c01552244000454450159018510f000c00805100c210340d840c10318041e0190407001d41fa4040015002e41e500c61401510020280084a01d0503804104d468034140440e4030030b01c0c10b0380307541c1c031038004807002915100010010f905200010074800600c0d4000c10b0f4800c041d107035843c001180b40c1054103100302660058481c0c2a003030b115545074038030f00303d182c801d181003803690292528900460b0310302c0c00d0000e5000510380c403181c14000e0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 588024640 1250 588023390 588023399
    0x11030108101d0607202d0c09150a050301020c0604032601141809100f0209240f0a020a110f0a0902030a020c072c1009380916080c030709 60
    0x901015600403000041946c00c0c07a8a4403241d08164100012a0030903017080c42d09180c4c0c0c0d2102c156007070313001008540013110f105400000400c0704440e60003940c1c1541c80441c0041c181c150000303079640564001e48441c0c0d0320506140600d100c0d14045002c001c8503032030360001040a0880c62001d060411001007031041090700e403141c0c1c0403910b04101c0d20180c266108000315280c0031241d105a904009158406610b0200e01e44c0118101401341c0c040d00182481122040400d45108815101170072490034007507968030382c40c4400a5a0f100c2d610001c0e20001d048050f61202890000e21440405202500140310f00e03282082e070078029040100941002902000035608454081c0443d20180003202e06240f0780c2a80c242200f071800d40d40c03001c20103041c0c0302d40080c4034858040750511800c8414004022070001d00065004400c4240240032011491007a01d100300c281240c1d1810754108501030b1045034507a40e401a0224004804459200109800340d02103840608040021076101c81e0381d041400c010f6996 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 588025890 1250 588024640 588024643
    0x1200f030439050411040b090105070807030c1109010302030a0204090309080a0b0f0117060a02070201170403081603061a130e01080a030206010909110d020411030108101d060720 78
    0x24204031002c4a064030030201c1d681054180c00c03101410301030b9030800443c28080354004003131246000795003c6a50100d01c0d2550ba80c410402c0702e488951000ca42901c81d919881c0203400308200c010102d81c55501185401c0107414114076040c103c94000380103241e52510350f002c4c070001f0100408294104003149001003111001000b0f0021700500c00c800500c081e1801c2400740000c2c10040c1c000c001c000b121500c0031139010300000b5040b85c00045280e401030b5192200d20040c0c2c0c0c8a2065042c5442c03a400c0407040005050b04040c03d14030800b0300c5098490400c0251030110f00f00d856a0294081c0d80400720191101080b088002d8103118041c080341600950b250003034181d83c00c400f640218803551141040701e04040e41884513a005001d001c0050020300855904c408003c0b0511100500034401d010700743c1c0c25561590031411a007503104994903625611014216240c1c010030f400428003505001c00e0300c150320304200d0f0300f4904e510040060b003910380f80d4103000c80305042c00c0b603025070142c612200d90501c800300 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 588027140 1250 588025890 588025943
    0x6040e040c05060a120b090609041b090f1b11252d06021b06031e091e03030408030c070c0b0d1409031207030c050c0f01020c01200f0304 60
    0x45848043c5c040c004e21200e68142c4011002d2039024002803070030b012098807100f0300a80c200d5403245003008083e106c05101003400c0c01c2d551050201c103081c0f5480c442000000d0f404035060311400204607103080c1e0070308000d0b2050b4156140d10100b6600a045075514092514964001211601c21400096540351001c89a00c4085046809401440664080c0300f8021030040390083c0302a00241070954032003040d10200c0000340c2002e90103014000002000c00d03008003400c5003a1803001c5510386003401c5c0130a0300c681e00c280001c4100c01d05040c0a02c072640801c4d000054074881c0d81e01c000e56a10759591f030107010141e904070396070032035409003042000705103020b1071400343c005050581c0b800106203001418407001008040c004000c10707081000313030140a507420365407070360700c1206030034007141c60300c0c2038002282c04e41b150386ca140005026080a042c4010019001040011340311802400300c00000c40518450350301c0c0803917201090604214030500b98069a01459102e0300a9107000501042849046403205 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 588028390 1250 588027140 588027157
    0x15092903090304170d02191e14010507031406040b030c0a141008010602100b030c03030a110d021212090309041109040606050c0705041a0604080d0305010b0906040e040c0506 76
    0x1040440e0600040010544400340850158014403030384c44d0a1748003035141e481d64289100f0000411801e00d0600c282040490301504140700d0700c00e9607050038200741a183c07100001d0b14440e5400c0801003031358a4071a009100c4000c40e10201c1d011581c48010400c40140440c074941601401401910f0090340e8030340c080c0d0030061024a14011015504c1000c20400102e4010714078144101c2030b00600c155940002c14413821458a030380060300f1011140040d25002442900541c10722001495455041d4000c0c4070000090320001101e03a0703600d407024160303107941c2003c4500615a0040c002084038400c15190310343c222602c841500e20301030450b40400c0c15100341c0010107070040c40000d200483e50416120303940007410b10b0300c1d1450825203502e003042c6c1c44002078440d00c1c0c85281c58000c160806440b1034400f0a60f03040082c40c907030b601e0b56a003a07044d0700c03107403460030002c0440e141000005000801004032054890001e2101d4a0039040402200c04000e02030710136506108100d40101d0f0396150302006007c040e = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 588029640 1250 588028390 588028393
    0x60e03250314060f061e060c010c0201050105030d0c24050403030212060f06031605040e040507081b060301170c0d06020d060b0903060705031902070b0708011509290309 74
    0x80e400c60505502c02001155420302d182d2200c01080454a182c18250f500043c0072210450900080c0f00460300543d038820200340e00640c00607a1103a01641507102c1c0b004a803540c1c009002d1a0390781c504050b12440108800c401040801101c0d40000780d550f040a041c4d10303e0910029030b8400c10281c8002107500c1250103d000c03c0e400203800820303088881e129540803808441c2d016509003084049001400050450503c4083e15405511014000c00c00d44d000303040c02240102880c5030609105030b40e00b2040c03061081e2405200e01f421600c861178a401e401d00d100c0500114656441c01081d501400c210094452840c0502c8190300e00a0780e0b040c10480c10700380140c50158440b1b2913070489008880b415404a04507034010080040030740c41c00315584d40d101c1102d0601c1e980740d695483c1da8230140c1074411606031841c0e200051203010886910202c6010307400380d03a035680350342c0e0b2038260145400d48000380b540045070b02c0590801c691000d1100d102c2008030307a0000e0014019510030741e83c1d03054105448103800c6 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 588030890 1250 588029640 588029713
    0x15050c1b0c130e1f0623100503090c091003080307030507020606040b010e0d032a051203130b0403140c0609210a0318080a0c03020c010315060e03 64
    0x118903000c08400b10080006404002e180d00c10201644d0b2809a040c3ca04004451484520180221548040020031084101d540d1803922168446c045800314803c90344125000310180b20001d00c00c80590748580b803580020801c0f61040c50400615a500405c461074824115074048002040080030310700171120740d280840d25082100c006814980001e00980c051880d129008019a07806690810000415200c4c280c1c086458101100d15041d05207000c0c010003030880d0941d182c04800390700c0713a00c050b000c0d106603103003000990464480c621043c3c807521710748003645600c400494808821650080e10070300b031101c2070140460030119660000e11074120a03410840c200b00303400d84c041c04102107540540707210340001d640900c14030131940a91038180f4201a9a01c2ca44910b0400707840c0d801e004c403500140030584508400c04000c1c030030031040c001103005010f0380307618100950090003808c51561a00002001440c10004125880244101c505a2620401079124a800c02800c0c031200306124086200c0134 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 588032140 1250 588030890 588030913
    0xa0e12040e091c110708120405091b0304080408211209101a0a05030307020916020f100506010e040b0a090c0311040f03053c100e0304090605090415050c1b 68
    0xe041166006c1c1040b6001001d650a4080940e003c032010f8076012901c4049039103079074640007102d415962401d000075000009000c06e10048074040c0c4100d034001c02c100e510038826440c00c200c00d05142404514800340c240805080d000902e2100340c2d01c101e8080442d4075021010700c207902941c4098105d01001c41043d40b948070b603820b1088414010346000c3d4000e620b880c07841d50100b00750100c02000d420b56402c0d030402d40c1000c035200b40482c031529012130040b03400d84039888a6034402010241c441c80d01041c10368158080701c0c00c0170f00600d500c0348401082080d000b4542000e80004e411a40c28070001c25030f4a44502541c54480f0000c0c2019220042d0b86404060461806610303000094640025a4a44400940d40e00c5c400b05202c4600c07150700706001c400082c40e1b80465141410100710302030200c1c1050900c80d00d50a000020b042182c17030301082403042c00e56407000d12100c85800d480161602800340340d03040c5050003980015070030000c104106071610043d401041c0c0d50003030881030240140c2015070004e0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 588033390 1250 588032140 588032143
    0xa031518110f060331050d1d01020a020102121303020d0807020a080f063705060a06110a111504030305071b4a0a0e12040e091c11 57
    0x860100099450500c0c60030900c848882001c0515400c00d100c00c60084007101301c02080840d202c5c0954054200c600c102c0803240c0c094101001080901500300d2001c48401ea1581300280c000280c54060b00075000101002e002914264441c05910709284545000080180c860818030b0007100d014070049031302e4584520410904001076071121074242d0110409140050011074040e812000040101d82c4c4c0a003a00034000c2032400196183d4140300142d80902c80380300140d000705100c0c01045504070301076500d424050394400801c09120030594048501c1e240001c0da01c00880700448401003948041e5100b0134040425030307000b80c0040f070008001003816000c01060750f40341e4805640c426a450b10241c100040c0369180740000185191024200803180c83e840a08003900100c1c9140c0d030541c0c1c500c3c2012195001ca02c40040d2040b03c000d41c40d04102000303512010a84c150b00c158414841071a05291101801100a016005810b01c1c01040c0c2660425410041c101d04400081d807a900540011080120b = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 588034640 1250 588033390 588033409
    0xe0601081803072d1a0604060b073203040311300c06030f070e0d06021603141305060d0b0603040609060b1f050c0f010504030c140c0a03151811 63
    0x2111942400f40307880c40040c170202d03840312010301c4041440c0040c0d43c3c0c400c00140a0b105a40c404800030600040c25410b00101355160b00f0500009124040ca00d11451070030706008903d040201c0c95a001400144000b400c400e084042410004007030100c40500c9003019103c4074088940a45403902400140a42920134802500510000c546045c01c510b06800020b83c03051000b00079404004403c0310340c2c125552441512500241c12030811034481c00c0304042d21a800d540742400341c004c68504000f0044a0008001b211910b040304c00566130b556207408144000c46d001449000c0071703e900c440c486680350301c409000e580314501640c00415050b490341491000c03600801110707400b42e0110400d840007840c87c030794000f88070341c40c40c54191365411b5040086810031420403074070400c07542002e00307000c1419031000803140814003070301005e00c20f14401c2c40d42d9540c0f4945515490340107001c102d010008940345032040e050121405801042c84a1064408400c505050f0f1086940c0c0d00329001c1601c06007801e600304c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 588035890 1250 588034640 588034703
    0x100806010806040f1113060b13230f01050c0a0302010b040b060705061f0e042616080a030e010f24030503030a020d110409051f0e060108180307 63
    0x3400703580c02d01e80c5071150003040c0759101800d114485168817146489080880081805e42e26040000e0b90329519958480d030301202038808480c004c0c04000c100007d0340300c1c00201101c841a801074400080805002461003d02042c0f8180a81400482d10303400050120340e408034402d40c00000d14040482c10403044402d4645400d0048109028a0380081c1000540d150011504c407440541445405104180729245402c0007404410200520080180e440010519101c07401903480650350201c04032582805504103412090719034000c540c012840d0b8900501175001c6a1a0204265046e05a09401e441d000c0c0700f80c10f0000c1e0313101d1021701028049006454000150001280c8481c69030b01d071543d480c000070b8041c050031a03001039848a00e03001507000315000c0b80c65038145501d46a85409810081c80125141140d000910610090102032040a0381c2a1010094504441e89401c0d00468030410010701c00545582c59120012081a041028161240c800e628050f0115020b64200c144078110444 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 588037140 1250 588035890 588035893
    0xb03060f0406150b270d11150c0601121a040b040215031e2a030421120c02210702010207231909090b060f09070e060a03060803031008060108 62
    0x10500000c90004d0446030712022026039611a488071280d905605444145038560005d010b0200d4802c11513036000490050208032808406402e000421403414828075861a01ca50403900c01400030016104482d112140210326101105841103c0941564010340b000d650b0400072204020861400c3c200d18a0340c15401d0688a0642c00c0040104500c0f6441c08104050801000005036000d01c00d45119070700f00c1a54000c4100d00c80744401a00c0d0640e000740ea085c1c0c0c0d5290f0781c01c0e807a03c40100e401805000c0103025603607803400d6880c0c011102c004160003031111085001740e074500090900740120540c0d6107412041e000d03541d64442e2002a103400780d0b40e400035034072002d41e41d840340404c80300c0881012685000d5031a032001902801d030728505610b030382d005182e10901d4001c07001c007404400701880344036500030741c1d0114960031030508101c20004103c0d400b400085604602032040e00340030010b4441c2544d1400d0126005480714002401c680007240d07910b01030b49034180200142c410401002d80140540340 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 588038390 1250 588037140 588037181
    0x20d0e0d020a0b0a091e03081807030b1504020910020f0f010e0d080403021f09061a0a0902090a0305010207120f1d04152303010e19060f0b03060f0406 66
    0x58480340d10400041c50490f13941d554201e11410700600040c1da1201c6503480e285000c240d03103c0c0c07502a05240040e145420984c0b420032000d0310342d000c001041d006a80d0003a224080c0780d03039070495000c10440c01e9055150040e401303101d2039429440f418041800c0d201e2a030050324240c00e26542c03ca141102c00949503a82d46e051500d031080d01c043c0030503c681058440c2c80c16100564580c2000c1c3e01d00a903035a0050b20b4143c01d080d910b01c00c20790f5648120a5980320f944140b007000301089202090b44140490f030340e030051500f5010865080d880e802401d0002c0041c0a901945940703840c0d1600b243c020350310590b00e010000d40c0c1562909d80c400000e40034443d00303003401440380d0380510030642c0c0d04041030441800346981d05c080c0040c481c0c0c071b000c0d0003001307059401c811301804112a880c1010030000145450084d07080c421006032441c00404c0d20051200e0540e00c0d04414401c90b19407001070031011616002455440b14070017160b840506c090741c0b01c4d4541c0e5003040c5103401e151400304110381100c185510f502c030604 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 588039640 1250 588038390 588038393
    0xc0115080d05181c0213240303080708040c1208030a0b060c0a1e060e0f010f061413060b0301170706080103080a0f20150a200a03060306020d0e0d020a 66
    0x3403d803644034070035900744c80d9014100200e8038500c40307901000b0354440002041c8044514040d0408078081c0e000604070346400342554101710428040303000090221b00d00340c0c001540f00d4031902c070296025018420404115503541d294a0f02001800c0c0183e40c0c10f030740041082241400c1b8040e00c00070700c0b019640c15107450800b00419454000da460024030300c69005070700e4030450282c101c0d642c106603001542007014046c5039050541e04c0301d034001020007550a013540c0c00c07055211807248000710303a961400d0443c1d015400081101140308140d0640304c40e559203c011030b9000c07206000d10301800c401403409003040c500748581440c204c0a0f40c02601001010401403001441c0c0d903054950b01007075401c0c98030441c400b0b11010350710400c403140b603110f40c0e6a40b003815000711100001c20841c3c824110144204d07a490303e01c1c041c2c0c1902d40f801e001e124401c84900b000781e10015400c000705039078112880d0001d03040c1d869a03107050517a8428442d0700440358440d25003003010f540c00d0002c02c001d00654002001c3c42800ca = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 588040890 1250 588039640 588039667
    0x6050108090309034204020f0d0c0b09040f0c0c331d0105090c120708120325120609020909010314030d090f1209060503011404020c0115080d05 63
    0x19212041610070b00b1421084000c0211158407042070800003091170800220035049003100c10888059129245212807500c4d00d00b4680404030070f079900421103001c1141080068061603005c134400c180c00a60303c10101c40c001107144100c500c461031954074101c400045040084404402d403075020b40845156000c0c40000c4002c0e400c1c840c0407110302001041c003201030524040064640e4414442c154204800c0001550f80443ca100c0481412200910041031000d40d07a41d40d003545008400d15030b440100200d00780c821640295600c2103249001d801c150402c040c00c0d14500540344050004600030040a40d9804858001c80001c1c024501e0704509003400b110010318100410b11014000c1a1490300045440f0301c1401198002407051409201400c01c80c070b030200e860802e102d0140c1e041c246880d000064039100381540c004540e1644d9805043d03074240002107420201c140f0a06603c00e60070030038001d0241c001e01030300188a030840003255001c0c0c507002c2d64506201d01443e03d102040300c00c12011746940c00 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 588042140 1250 588040890 588040903
    0x50901080c010f090b030a0903110c28050d05070612020906070609021c030903060e0d02030d0b0d0c1d0a02090109031b03061103010602010e0309060703030c20010605010809030903 79
    0x2403d1030084610649410140c0d03c00e41e164206080c0c020001003007144403005c03600400c1c0381d981300350340d456110b6070449115520ba0b20b002002c0380d072000550b6070f404860b295156604400000e10004a81c90b9070343d5100203144201c0380c080c01c072031ba40c111250070070a254000480b50384841c815002589800d200800040035403084200c0104582d66900c0070000399100c07400208281d5103044a8043ca500340d03070401825102c05807000f103610a0a00391142810440070614840c100402e400039810302c0000307420f84018100b0201c001e6041000f101074036003c00c10b010200130041001604e1052070070722072407282010030340c010281122140100b10284c0c035a40e00a03004421250000103a5550800022404185804550003d80306c942000400403c681440000b18103c85007500200321300000f01c221503483c0e0181c001407550002c4240b0a14020a00a40140c8242406482c0c5050b40b402c25806000d082100e0304001c000503035403030301c0620865130007803095900702084000450030181c0e40f6002994480c0c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 588043390 1250 588042140 588042163
    0x60a1202060c071806030606050f060412060b10030c1205070e1306052e0f080105061b01050703060503011103040804090c02120c0d0e010c050c150702030106120b0105090108 76
    0x19002034000d010302c50900c9690050080c035000440c64207005480700028240900040e11118a401c2c1e00054030700d000c08a050713002202401d02c500b0149401c41d90440703c080210152046502c0340394107801903548400c4100401c4180c1c600180c10726034240e00501d600300d4101840b05441c900810302c8580c40d001190600b40c110119407020303030f5005490103800944030b25031050750030400c510306050301d00200184200d44900703c540c0d80a0307090640d440417070f5014028080a40032a4a41d00103010608012005011035070060b0a5100c507540403040140c21a0400c6a501e0002659080e05020f1841c0c280180803240000d0003c0509604040d141c40c9464411407080c40d800590b5082d8141c1000c0c024407050982c1582d1700605500c1d03042601d038544e11460710101400008206498400e1158003416110341e140c0d41040060102243c0d5400740f07c009040320b01c014101d0601440303201d005a03002d000e11310190824000a00f0a1006403821080003103060300700c0f503c10a8070300011f0004000010342201d815 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 588044640 1250 588043390 588043399
    0xc070c0b030a060e130204050907061b060e060f04020307140105030c0a0915020d020105060a060c0303050402030304050a0b04140324041b08030a020c100c0b060411041d060a1202 78
    0x76200c45000308000e000c3e943c014014440c2ea202001201d026000c10982180c2c001e490a0284ea1f5580c0182521406a4081d08010840440c8110203540c01c054101400c07902c00d1070001102558030180600d410b1044446450309000f8030f08110450500f03200140080c1640c0e6101a043c806810010f007060100130084e84814201003540318016104103040340042402c00c5500c0700028000381e00030345440d60003081e140550709140114400d412321400c850708850081c0d846d0310710305c1899a82100605005082aa850301c0148408101503544031504c900500941c0f0502d170f034a034604458130001c0c0881301c8900e48243c03c2550000440e602c000c0800501c1c1d00b40004141c590358a61401c5517949400b00c0e910140d400540101007101c000001c02802c4c2c0e9a840c4e02103d084c101c03490100010b030702120035880d000505000880000840c03140c9810341000f802440400c00c800c1c0f40003480411f40081c0d1101711010100050482002d002064450304400c1c2a00d0185030300341440208051340e480104001c2c0903 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 588045890 1250 588044640 588044647
    0x8010812070203190f0308010e070c020103020a030f0507090305010621120903060c0302090102010b030f100209010c051920030615030307020310050132010c020319080301030b0c070c0b 81
    0x441d07809000d013900c070042c003002007412410a8140040b034400c86842c200e021504800c00410340c03152001181b0300c581117a60f1980d05080d10b07a0700440203504809500c2040c542c035000300c040200890b0084e00d101b0300156036840d01a5145051003820354810b544500c6082255008620111781801c44281c2d14640124807028049a004800c4803500342c01c0d44060821450561007884255158006100290003640203105540783c3d141015120f00340c9003a104150782c0510b01c40601080780c0d070058030820505040c01501c068444e11400d041c50304410200d1880e140140245082000a24428516121010050020b0400c0c00c0c04640c1d59100604910402025521080390740d90f010400c80d03914603400f40585035040f84008141c4003401003801801840b00d1410480c4041050758002003141c04000522030b000d1501c0040190340702c40344020140c0c3c1500030080300385041d4080000b14200544610002039496145050215101c00701802c24211070308208420350215100e00c0650050307801c131190803542c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 588047140 1250 588045890 588045893
    0xa0b130b0c0a030f090b2802060603060f07030b1305010306060f0b0a08101d0907080f0307110a17061504020c030304061d01290609010f051620030106060801081207 72
    0x5171130002d5881502c40c9000059903120349900008200707001d003680120807204440340c000998580350300325625905a07009900041c281224120700702c0c0c020900d030500003156600b075008284900364907110707a44119200c00040040006034841c1c680100741034807d66985a084c070a2400341131181c0c1401000300025040410500d50f644440300e0018000b101d0504d07800305204c0c01041e01001c040781c6050301d50050003c00030307460102003a507000142c80140914078081c2c03aa510280596402034071242c110200f41c00c0401c44801d641455040365002c50b0041840e803401c03801d0790000341602e40030507005500521000b00c00fa400001075980043d80110089845107003030740000040820450502136548c2001e80c0e0220380c030031030382d00c43c036607107083c51040051540b002c0184460ba02c41c56101a0000d4007a881c01c41010b8442c401070704480d1401d0083c020050642d454141c0d1882d41180b002c00020848a01c448641c074091007210010101801c08200d2585060300740ca86800007d403020b4011000040d02c0700 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 588048390 1250 588047140 588047147
    0x2070b0309030d24060e0a05060705071d100602070e0106050a02010f06171005040b28090c050108070305070909090302030904061514030c09011d0a0b130b0c0a030f 72
    0x4880c0f40b5011401c021415000c030b0203040780c070b20b4105403103800880c0c0c02020803510304c28002c00b1060b40c0c003d040740402c1031400c2c0c1445441d5020040681e1240140b80c1c000c94441945080100b01c1d200701c1581302d0050508480e11407200026500110540d4401e400800100e880b80322050f04440444c102246c030762607200c5050b40504094602c003c0f1243c5002c801013689482c0034401c58449a0000464004105042c051804c980064a0103420000e00f5000034030084c10000c1c0202c04078034981407a41c0d114403029581c00075105c4d1404201e0b40b0012540040c84256404050749500c8a02c03440c0600c041e090150015107000c0540c05203285085e100d600030001d040c000c0003110741042018208200040d034452454040c100202c0b883e40026080400f403c1d4010b812200340ea000b4011030f0314403464a1115001591820456018a2144102d044000780c090351980020001421180200d0b696036080c4810b44500180e40d40011407109000d200350708680c08000f60700740904c2e500d410f04000d040c84024054 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 588049640 1250 588048390 588048397
    0x40501080a0921082205100519060803180103140610140d140612030a0e0f030319020606061806090a080f030d060504020a020316060b1002010504200102070b030903 72
    0x50303002076280520180d100e039004404c1031180c0e0080c0b490000359903030074954010b42c0111000281c86540b008a000308018407551007180c0106158100618008200304440140c03403050b8032036802c80c5c0003c1401000000303007803214003118100346820401920421700d003405003040506854004c8001403624428140140240341141c5003640d1410344900c1c0d00c107000f101038410010420300400c0e9a01c0814000c2c200407440803850100300e0080e5003001d448502c112580c0b028140319a9201c07075400701c45065a10240300078000e075800e9000b0a100f21020080103442e10f4000740542c1d004510810070f6003604212580c4410300c1c540119000350790b82c0c0c00c56000460300300f1180c100b0070660050b00540c1010f0040000104035401c0181c2e41444056901e90401040740220048000541c00c1080703100c0d107408403e2420740c06103115480004411000e032001c6a03000c3c400c0b06c02100541c0d03445043c002806511802c0400480c01d4000d1051480c0c3ca5600003500d5017035600c01d09030885400300100c1c290075002d1064 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 588050890 1250 588049640 588049673
    0xb04170405040e0705040b120a080d0f0608030903061b04030b09120a1707090b3a0c091203050a050a120c050a1709031621080912040501080a09 63
    0x920203d004010000c0e118100c521519215503d0482d2400850038030a04443c46a0142c6025103114074941c1c69084070f66024030712002d2195500c0b40d9044813016544161001741041b0340046032184c100005041c90960090200c94110148182400d0303200040000c543c02e0746e600801840c4c40c2c7c1c458100c120f1500c0c140001100c1d03035a41c04500c0c5440036901091545202c1d046180c484c0a80d01c0e2000c007a141c00c00036000e50201150204543c01c01201044095040500e05181c4014101000580034034a24048059040300c070392100070080700294000b03540c90280000580c13a4055410070b0390050014801d9500034030034004042101071a81d1300030b04121040c01c01d485024080107011101c0144564081c000d10404207911007080e924420820b1441031003071035814000d41ca030902d902903000c0c405000c1d070300172540b1001201c0041c03401000000d41010041d030945230813110f801c190300c03454200b12031418500c948400c20700c070402040c0ea0040d001500f00b02548400503a40501d4103021103035001e2b2454 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 588052140 1250 588050890 588050899
    0x3120a020c09180d0c08030610020a06050f10080102090f0f1305070c17070b0117030c011a1c15051005030d020f07060c0f080c0309090a0b09060103090b04170405 71
    0x1040580b42c440541036001c0d450f500141c1d03844101030003013074500244080005d84048001d0000410300d00b080424815005002c0c0121042d0403550780d03e403004c3c0e41c800c4a841100d02c80311000c1c040308101145020010b060058002d40c01e020301000800c40c0303082c0d85020325200e000d4400900009494400e10303980c02c1d0a0030705c014040d506d400e06010b040c5002c1e20f84100e540c0002c00150040740c020032029510b0343c6500c6054080d40b640b0740340840340e0741042d00c0c41d040c42c540010007551181640034030510740384210300480c420b0031281100070407614400b0342803001030404000610b00300043c1c2040009100e4480e00400107420744817000d41a402208641000d0341501c030b40c00c1c0100206400242500d01c40000d441229500c9440d540116518504003030020000b170724420403030000400a60142c00d10a00c00401c9a0800d92220005404007100b95404250603035207101e185103074146001d619500c0f4800782802d008043c081d41c0c0d03020b510080103002400380d00041c013041c80c0d510725190840c0c1c028100180b = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 588053390 1250 588052140 588052159
    0x17060f0d060507140403053004120b1303020607270305010b190b0405040e0c09070f02010c0203030f040210141b07291806040b0a030f0b03120a020c 65
    0x1d01500106016503000d80031a0600000907040c1020342e04441c156a8050013a03d4034005004440080b01c0c081d10301450700e90071072229040010701920191004200c020000c1031b000d0000d042240c2c3c020400f901160000560030003050109400044854005242d03190401c0540744441c0e0003515050274100d004121510f0000000521005400c0000d403244201d510902e42c00c101010480e140702c246c880c041d03040f031003400200400d242ca80c0c0254580103180060382d0664814000140a180c01102c203d0080f400500c903800362203609110704400505280001c5d440c0d070420b40710352071030f071b05004000a100716000f0300030f80c441c144a400c2040c1001064200d00761280107980c05081d040301d4072591444a4850300c4800101e46010300010074040f0041d2403554003403210781103541e100740c0c4050358040180054190040c801e4513000000c000600c00414280c0d214403c000c0e009054506c00b05203c44003c0c1401d41d64103060740c4c08a540004c01110702892541c485080700d003a800e0911900b0010741c40725806 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 588054640 1250 588053390 588053393
    0x22030c0e0105121609020d06150c15060807050f1f110d0804080403060b03070e090303041a06030d11010e0102030c040806010f030b010e060109091b0807020a0317060f0d 74
    0x6000c1c103848040f038200203d600302c00a581d5488100444600021075900420064416290b0051442c003205035000b043d050b495031054101c0c04040c0d058140000c820500320b0040c8006522050304030072428030309100030f603e40418650341e003000c0e00440c0d02c00c1044140b81640ca954101c4210403141201040920310314144e500075007203015000d800591742c001d43c00c584c8401403103000042c0c401c56100400f40d04250541e150140104525000e040d0175202e40c1d40081803201618140910038a441c60003141c1d039103054036050740c24030010a2000040182141884420b5501140070f84c20441c40345000d0742203170134403480f1502521501c030728408594400020f0105140300e11008005a801d60300480309a030b645c0715482180030480d4440641034a6860005114480d030080c001d50300010145403d210213070700e4108000480c0d032924845e00d030a4040c4d41000004507007094507940c0c41180d40c005400c0c0b0f080240c501412100c00360303416448071454100041c81e140d6851b00407000c1d10301c2c05800b41c00020150f = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 588055890 1250 588054640 588054659
    0x72906211606020616080a020d06030f060b18060315040219180c0f0504090207060b06030a0207111e0603040f0b16080105090103200a0306110d0e0303090322030c 71
    0x2d025820041c0a4100000c02c510403106582440c0e40840e07a82003656550a14840020342005030345103202034440b4030000c003040e1009504103146014840018181c0d06100820910450400080881c0c034400010400240d4010440c0840040b00c02c0601583c1c0d955440045d175000d0340d6a9031029149082c0341e0208034007a0030410341c84411540b00040204c1c0700007017802d0b00c54980303130207001002490402040c041c5042d99000b90418500c10080441d0030107900d0001621600211060030000d50702007511800c1c0440302e0b1024520082c1a6200407404001102c4208100042400c40340913040000121f002c1299101360506e032940c000b260201c45051103011072003000340c0e0440940004003070b0000030a4a1524000f4541207d90217440c01c490b00f56a50300c240110402060015404941c203c000008595179000b40301042800c0410075aa5504028015080b00c00e45042130b1120f0741700b40100301d40d2240002c119603c0d80d1415080030b00d41c02d16071102040001054000034820341d811040000da000c0d0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 588057140 1250 588055890 588055933
    0xa0510030e011a0904080f0d02040603051f0e0601052101030311101407080a02090a03050c04060602030909041b1d070306050d05061605160807290621 66
    0x2001402844042d80d0b103504103c81c08490b46416a00084160100d000501035100a0200c002c06000c0542000c001008030304c1260407079030104003c2600ca104001480e0b101c0750181040700302c00c01079020511f042c05014042e044008201e030f414031500042000210740448042d00182150400d00c0e0125a12450300406155402880c4621841000d24014151601e800742c0f801c0d4500303882c1c00351030306d03510300703508803400074015000c0d04489608210035000c9440e441c1c1c125005d10701031001807043c0544201484203e4800b944082c0c1113403c14072020307205565041483d13030819001a0a000e0740980740c0d0350318980d840c507680100d4410384059000601c2c0d40400e88203078403500990310104102640d800c00e01c0f6110000740002041604002e0014841164003080c2500e6203084c0e10f0000e080c03900a042c5c039000c0e030010880c01d1341e10700e00c04184c200801008000514185048108907a010a55600794060710310010f412a4801c2800c0c580104901d803c0000c000850041807045454446008090850484 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 588058390 1250 588057140 588057161
    0x20402180411030403050d02070f0506070f02060c1303020d0c12060f1a010e041d19150608030f0901030f020f1206010305060604091a061209071d150a051003 69
    0x1410a0b0003411180303640000d0b02e11464040d00c1e030306c0c9400c90328212100258014038080303680f0040801520046403042003401c3c801e0419482d00d45805020100180c80c186d001001400c544500f0421180d51098a402920450340d0644010740001e0903890070700c41004241c1c014080ea4845e002c2050140308582d0880084c0c5104200204001074030200c0c07082000146d91002404144008800056814258401c0d000742c0a40005000d100700c1d50340c5540c1c2001040302c01c4d002c20948100094081c8036036240c40804218401000b000074030b2400801e1500ca01a400d10000d0903880400ea040b4a81d0183c1c000d451680041ca4045580351042c1c0ca80e45001d81104400d044041c5e80e141c00142c5650080c464140680c2005191900b00740c070700000d000c041c03c50b110002e03003480c801c025010300c0798440300b0240c0803032121b1807000703955407500100d414503000c0d03a98010704100d00b8100420308107070320358110b90f900039401600302c021507107046010609181117540859040101e007e1071807002170f0300d0341c450907400 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 588059640 1250 588058390 588058399
    0xa18060b160c080c0d020d05010b0319031e091205030c06042102060402090a020703030e120a080702060105060d05061c080408010b0108010e010e0702100207030207050901050409240902040218 84
    0x25900c071002507507105401e00400c5d4200c24410390407400341c5011481c81407050300c100c0000c19420ba40c3c601003400c24125414900d17440e80362690740c1c0b08158004007040b83e0720140846400841c0005100207080414522919142103503100030041030140a104841110710300c90121465824035144c10691440358015aa4102d05500807005440d440070400c5400360740c00400c1074202d5103542d0f08500095011a01c00c03028155211000140000103021103106250480d06c0a51034960103a0090201c00004207034500f1500810700508c044d80e5050b064515040d80a41c0018240c0d0b500b80200342c0100c0c1c1440761400b203d02c031000d00000c0100c132038010410345114000074402a0f03920301c01596100b500703008500c0c03005c5891b001840300514425a01d688007102c7d10454888040c1e0500e078100320382c002d00c4240c0040e0001d800c1403155090982e1f00c50300400040d24208810002030f12454448802034268070b0700f945502c5010b4100c0c10040c0c104070f81d0702da0001e000b190344001e40341481104840c0b40210f94002c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 588060890 1250 588059640 588059663
    0x3080405120d020c10030b04180b010b074803030315030503090607030507021c051e251a030f070504060804080d0f0f020a1d0a18060b16 60
    0x4038100841e400301d00042c1a001004d0229019080202952407107861000300355584074504030f240d945018034001442c10080100740f40200e070a2903a14603005801401e078001c0c1c108040720001d800b1201c000d540941e200b180c2011030015203a504a80800194003c4850030042c2024144a001d002c204040b2842900e04010b2004d40a010740c40d40400c41c840a0040d800c02d001c4008141030800041100520074900146440c0140c1e001480c99240e50100350400301703100c0e030307080d080190410040b00640400c1c0d9410070f24405088460795509142c2001c100c1da09552052041c1440000008401419001a0102d02458006000e8a15400460707030391010611105c08071740032901420446058a4881e80c4100c0c143d40d5a48130f0860a5000c1d00248a2003681e40c00307080c0346d40e00c2e14030491800b40308468015a444a92510040a104c0030340f19141d80302c440404800e80c581d403414560707401c8607c4030803e1212a040381c80c6c80c0d070040480ba4040b4840d500005001103540706240c2c20307000c00c2c80c46541c15009 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 588062140 1250 588060890 588060919
    0x20619020715050409150f06120e070b2709070c021c02280b04060801051314061219030e010f0c03020615060c10063609080d050103080405 61
    0xa504200c1c0ca42c040200d07100700000d00041000d50888032070811916446020301d41c1d1000e0501c40111940d00800005030b0a0f0116081c45845024103d2042140f41c0104107060805c0c010b42d2a5115401052004000070601041c441d04100520300300c0040c018201041c80c0303040c45019140211a000c124858001d818851410401700b10001101ca27030090030304034017000d11150382c034021200248403407810b0202060004240c0c12441c000c10113450703103640b40341c00e551400050014001032107103200741490404407890700c040410505141d00c40c1c01191420700d6540980d807818105010100e0702c409181d5241c42e50401d0540001100c010740d03400b079903600d40720400100102c0d064200c00500800680240e000b0400100500c4640d444a140c0140264580301e076500443c2e14081a007c44c2c0190240c1382e18003082060301440310280f80840c496a19410b84442c08030a040b1105210040c0d14030a55402c40c95050003e99801c0d2241034034400030420081d6100c2c104840650441d204032441046082c21003007 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 588063390 1250 588062140 588062159
    0x10201050f0402210610030c0501030902180c07080c0703020907021f0c090510120b060f0f0d090206040303110c041811040e030d0902030d0906080106030b0d0206190207 74
    0x1d10a59181000788510b4949a00b0080522000d049038415002d40c24241e00c0003038014031100e80201899451001558076510b0810302d404104d5010301e05162800907008007585030603022406800e1120325801081d03039030101c00d507198000c006000d006203101080101c3e0a030303c001041000c1d20b000319482c5580342c1d41d1810490b62000c401e080c1c01100c0d005220b82e0700c1000c00b039030005681c0681c81e06106100a481d90080f0b8400f00c0700c500300c080002c84c1030a181f60340030401e101d002000041909d0030b51034031200503000c0b90b10f0b02c14520005c028020009020403460300a9105080603039000306043d58807581c90034002c000e03000c1c4100c0307218140964000305005140c10300c0741c44842d00c81c0c0c628a40c03c410680d15604420f1800380c1d04180c0064450b40032000c1c0c04400e100511080a840d0130014080e1044d0050629012810645a0500141420601069401444503130441e550b42c540410001710b064045604420300440085d000600403035402c2d01440c100310100c1c5044940c1c0d0803680100e40c0e030304804 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 588064640 1250 588063390 588063401
    0xd0608070506130e0a06350640120e0f09130f061d070506040303051c060302060a080708090601052101150b0405092401110f01110d0605010201 63
    0xc60210743d0700c0c070402c0a19442202903501410030100050015038038084960501a5144040c1d01020310b1903164044160804079001846000ca00400f01850b00114290307502140200200700262002c038030701c6542000c0c1720142c0300e541c00070622003850001890318411800d81010800041543d28040f40d495040c101e4000c840c0c3c11000b013102485485081001c441c24001010035101b12441580b04d0002c188280100751111a03910310444102c000d8810640c24010310b5040302d4458101000200007003948902030b565161a2030f081d1307101c0b900c04840203400501081c2c6c4000c1d0051008103550b85035039000801c0620071012074980500c0b6607111400d4544519003405070031740c03000c01c60590031848103d80024044014611000141050319210116140f0041d03a02c09030b01c40740001001e001d10309003500c44c5600100360b50600f003a802c9113a40c6035107079030912038090b50420140780d0003040004c80c20400e50082210b500000c020f10005070016941030380c0004403126041e81040c2d0009072552051158 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 588065890 1250 588064640 588064657
    0x603170a0e0409030c060905061005040b0a170a050f030a08091f05100515031b0307080106120204150c060b060703051213080c06090601050d021309030201020c01020d0608070506 78
    0x25041c1c0040040104802481490800d4081044414620300016943e21030301000c22300440041c01c940c500100c8001c406241508454001e0341481200102a00e8242040054483c00c40c001000c1d14014a00b0038600030491102400620488000b18100800840100340c0050f039590340741d1540e030b55086100d035100c51903214107a0408100c9840101c2e04901e902c07103038012915000707004002d6070318000118000d0071840680002c140c00403d00c800181040240384000f240003109a0851600507000751040030148914014400210110400308138170341e04450242c0310096241a91030401203000f890034041da00216840c03460f041c400c0d1850310708003050701c3c851313581952707181d241445800f030b202d0b0440c0c4040c2c1529100c003007c0f84a01c00052414018000400041c8000c18070780c40e010124a00d451010b034440f50040b08040113410260f1550351031012842440800455040c11900e400c034020f11500381e0600300b951000c1a0b407040c02420b41c11400c04c548400c002c0350591a1140e00308941d9208240b003 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 588067140 1250 588065890 588065897
    0x203040633050a260709020c01050a06051c060b010e040c0201140901150b2a0313090204060c140a0209070f080f070503061003020d090c08010e060412050d0b030f010603170a 76
    0x20440005001c40710018041d180113001d446805994034040c4090341c02c503201040959444204010560603548030f6040113100c202e030140103040008201e081c00140605015064981302c00c0b6611059003e52080d2001030400740042103c20a2400c0090080102c44040300e0301251001c04150350450501981c400481c03049143c2c82c03500d20f0965031303002c150300452180d6290210200152070460b407104040341d401510001461780c44401503040e0080311901e420407551144140f00602c00e0030f80c0941d03250035507640282541600c2c51810031107031800c441c51b040258003440720010068503aa0058485040c410700d929000419200d203030141c103d1010882d1034a00040c81840050000d01c0c1500080b07996880d68140141303850500c5076000281e4070120820707150562400360411001c4401d00c03400401d4240e20005c0c0c4030b40c0c10039559a03401c034040011480c0c1048000301d801c1404c0036244d8054801c0d035400074121440d05050310b4500c0c8c041c1c0070521044d559525804002c0d01c10b10240c1b0b04603200205143d8 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 588068390 1250 588067140 588067169
    0x3031205042d02090109061505041a0703050d060305010b040e070e151207140111010905150604150305010c030b0108070519051207020a02100219060203040633050a 72
    0x40080c60900c0707010301c2c001c458418001c000e5001d40c0f1400070140c080e10810a01055040c08c0031044101b10705280c29440800104010801c0f110001000c40401c49510002031759640300d0350304048178a0b003d13113980e2881e000d00e04030000040000c1503000210207030f4103482c02e003c1030710341c2e0601a0b00e600d1144240c20450080e00c0008419030500071956940e0100248045100400d020102e460010701790001320b00d01da90440d484049680003a090200d0701e00701402800f07844801c0e076881d070702c8150080918003a491700c140442c3e610742d12900001d141c0541640342c2000c0603078078203005010b4041c1d425440082403518100c1d4070076510036030005106540c19141c1c00c1c94544040c0181845090420708607080003801d200c0c442c1540c4d4900e003c075002d110b403540140811102401005110070f2107507036450965020f0043c42810300c028014880f9415005200145c60340e8460034458040c0455401d0142009005441c03a0b1280c591099881004a0310b60740c0080055143c000b40024203c0501030200241541c9 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 588069640 1250 588068390 588068423
    0x3030f09012604021918090203010e030703230918040c03020a06080405070b0c190f020405010f29070807051c2d0f050a1b0602040303120504 62
    0x11001008200c0041c07400c00401d400307100c01c0d84018480303100d0701c51180761804188070940c980b210f450304640c1c201c28060b41d20189007110f01103144980d00c2032220300d10f8403501c1250a565007944206000b08005c400d5039501d0860b45401800c3c1030041e0302ca0038500c0d5203000142e070f5000301b50003542c2e4044000707446c03401e41c501e440d030050320600d40040040380c2c50605401e0100060701d455000400401294640110a042602d0101c1c107103541d82d003090305202030622400b0016003000a130351144000d150058103030030b01d05080061820f5540d00019400c44c0c2040300005081d0300000a440c211415440c1183d980010342500754810084a10000f00c840c00c24020800420301c1c0c40010242c0621442c01c0724180840d13111102c0465071009010310102c2d100f1501481c2c0d003c0c030741200c0240f03084a0400000d0007146204080c140461801540c4208400820003400450295020782d1841c40c0130700a01c5c401c030040c1d140c4000a9801800300314009081c9501c0502c0101c641d02902c0c2c0210351103140d00c1c1080105 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 588070890 1250 588069640 588069667
    0xf03030f050f0d14060405090127050304030506010b070c0806010f060809030739030b0103030f0203040807082407090b0906070b041101170903041e08010c0806031b0303 74
    0x20580b0701003500c0303041040c0c042d80122441042110f8900000500107807405500300412680006d00d00c00e0140d04200e4850811040c3c04405007018851802000701d1a840e420054618003860708001d100d4442c0d9000807800d4641c110203440307000d1003aa0054081e0b03495000c40381c0c640d5028811a8005003061070144412402040125480401c220860b8200300c40d07922a031000c44c030030400c24080c502503c4208640248405843c04440c5003a0400810541c81c3d5660314604800511000d403c001102d01069941031007801101e00411308041221402510b4000302500c0d4109010090000820072030881c54440d4840c102c94031070111038039800045440c0c043e100703506600100c14180e01c40010450080003911008415000301d00441c404991074000c0c500150046109045050068501c0c00402c03004034000021241540c0d500020b4041d9071112076103401c500d031165040300b20b840d424248600040c5a0100380c1d64802d00c0c0444c1151000104d0036a02c0c103100750310b003003059010341040010311408203d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 588072140 1250 588070890 588070897
    0x1508070b0d050c6103020c0904111801050108041b0911040e070203070b04140c120d080f06061e0702060f03011a180108130602040b0406090f03030f05 66
    0x80e11101c03031800345000359100350440c001151210701c85072102c4210f20260084e0031002c480070384011840c2d03c06110b00c1c2080000500070380180d40b84076078601110415200703019405107400080c00d6076180c1c1c02d180c41d250f0848080100214003401000c58040850016190000e0480f441a142d00300c40341c48a442d041d0301c20520758550408803a45110002c1c020446200b2001000600c9604a803124140704e8500758141c0082e00f0003007154070a10040700810b84440f483c0343c01a81c49034041003600209043c5e207040241c22a40d0035880010440c1c0c640154001182c0000641c11650741c1098030b43d03c4081c26000482e003941e01d07079002002404091080707403201c801d0082800c061901075040c40031507400a6201d41c8400800d445019004c00100801c20400c1c15004209503000f846030f084c582445c07002c1c002ca050740c9036414100104880414090505042003035825a040b4a05542d00c03626001c641c50305130700c00d200720760000c1d10170b0500080c0c00342d42002c0038065a616a442001015022104480d10380 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 588073390 1250 588072140 588072151
    0xe04020a0803071208220b280b01020f0f0d0809070509010e06010f020d0206130809030a0302070e0c03010501141803010903020609071a041401090801090f1208061005030c070c091508070b0d05 84
    0x59042d14422141108c40c3d400b5030300c1c20607000c0128094030b004000a08000100715400e44a9101d12103c1044010208140c804c034462031070440a103650742a400c504e000e28543c0220b0b0001c4200c00042601c0b05002400c600c16182078851803442010703110102e958120301c510a0005811020203d46d40c2d000e01901e80c1c3c8c5040c06503201c203040070040400203041c80c500010450240e0301c200002c018412104c4000c9611816848182d420366141c480043c004102080c0000c0d902e60b0700083c0c00328880d0118a25602c031950180081217110014503001c0c1d910305068a0350362281c030812400241d42504d04201c60004140e21901c1410f06182c600c52a109014034180c61703050020030400491050700910882c04100c1c001c0c2014415040141040b4000c0170046414004004035003080040d2500c540c07404e01e00701c1c4407500d0055525589c0c0c10b0001c0c90350013042d2004111001c040b00000700d2107155049500407105120120401c903a0b60039038070366680e6091094240810041c0900f240c4490f0039401680d002 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 588074640 1250 588073390 588073411
    0x613061805030f0a0c23040c1106100302040e030f1804060b030708040b0f0c19020102041205030c010b120715091203050c06060a0f0e04020a0803071208220b 69
    0xe600c50300002e05080c0480b9485000d940b100d0440e4007803240c41c1a00c04001e10f200312442a1030000c0307241221850f500700c48034600840d181c0c610104000d1007030020800e100e0510b81551506e0030080300400c0704043d0381c4001da10a90900700600d802c0382c008004c4601101000d4051031500c0a040140b156007a000e004d0303254450342c0c0d00300024248400c00c1c000e41c8103103081c0d9144142031415183c001c6a0400c054202d070001c071880d80411407004007810407122845c50000c050320041590703900880c0688543c0c4c0020151110f4000740a00300304000010b41180c180e044000e00002601105224106194421400143d440700d0800c00c0442d0b000c099241d400240fa181542882c2c1d1180d1444245400c054811000207078000b40d01401c400c0240f12041e0040c170200c5020940030319280c99920141100d02903050170b0729071040803c0455a424000340014907514066903102c020500701880c0300028990030001058031030300041c2461203030017160a41c05001d144980c1c0a40456100d001428100421030f0020 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 588075890 1250 588074640 588074687
    0x9140c060a03050c19050307020609010903090603050a1e0603150506060301050d0302100c090519060203031f1d060310091e060e060f0601020c1512040f0803041b05061306 75
    0x1004072007178040704c40250301c07280c0c1d0300d05014800900d00140204a80722992520582c54002a407000c00d05c01102d1107403070003144c2c03601c0d120146801000840b0080c0c03007840800042071403020598001c3c04c110303800b4004903081490b158181030180c0e0301c2203444580c03100c800c00050240d4504490010681ca02920403184d0403003075640508211401d0000910220328101d900f0030144c9040159102041181080100054a0500b001e9540d01001e44054a0740e004900c045945607609100e0000801c1c8055a08450701c1000e005030700c0c2c01100b40c4103280640100e0888841c684080d0103444107159105541d00503501c1c0310b85401100c0541c0403400c807201616444000c4d60b81a08000a90090b98402c607402d12038207109001a00e00030081c00350303034040d4544091041c0f0030712107902596944030701c0007490242d40d03889290203000c4a04100004102400210070f000a01c14410f204100c2c0d07520400640050941751005c014a5006480a00c4500d281b20303c010300c5103612501588000c6402d90148a58 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 588077140 1250 588075890 588075907
    0x3230102120412141210060507150e0c0919050c0f0712091706180c0906090c070503030a02091e0d020d020a0f12120c0b0c0f070605070309140c060a03050c 68
    0x31981c059040410019940001d01403500180d100d00402408642008d40c5000da45580c3d91800a02e00924416219500d40d0380b13640286051003803980c244d43c0241001074515101c480e24116884007201032812918160001d808450075008a61882d10500f48207814a002d650710414080340207691801001a80240010000c94104a2149a0411801802051401c110b00c8074602484404030049a0301101400e00075448100400da004801502c000c1ca8903501d10b56014843d200342c101c010628403000080103080441540a00301206086800c50f082d203065840c0c2426100d140d14034144d002040c0d402d108014a44150200340301880680000003680c4d81d0401400f084c00c0e29031256100124809078081004100704004040500c1400c1c0750740c009100f5107415070400001800d9071aa8440080c101c41d101402c0020790350515400b410511844c40c04d0000200584103104049403180809034945480010100e2045d644100284c062420100495422000b0304805400014141010004000e = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 588078390 1250 588077140 588077177
    0x717041203020c0102010c0e0121090b041a0c210a0f020409020901091a04170a050319021e03090f01090e040809091f05060901030b030703230102120412 67
    0x4203958082c2d0060241614801c001a007036554125441c8104542104404602e0780c0260241c2000201a01e20755624290f900147e00105103c0801030882c402030001c0108100c440c1032800321100d07444801c121240c6074200c005925001c0d040140c0d01030a080704034060700c65a43c3c00c4141c2c0c82041080041110607801c100761049a01c03a801141c00a60002a90f11013560803000540080981b042540c03540d108201814000e4025801034200c0380040c4070340159191020000b4100054001003513941d140011100700800f002544601e01c09400350905020610b118008204c0f000c07602d03400a1840c00290b2400c2000242c4c040741590305101007004003098580c641007000f4410740c032a00d1034640e101558000c021005100900c1c1d45203a00783c1d030903414880e154180c000001c407036090341e40c02d46070040040140c0141c00d85031006509481540300000601c40c403070300d807014080402d80c0c0700000a00d04410403401d074030650031405200803c180210340001c852080740141070455160800c0740701c0034a42c508 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 588079640 1250 588078390 588078419
    0x82e0303050d140103020a090509031e07060501060507022b080301090b01020613081905040b0d062423071b05270727090207060b04090503071704 64
    0x80d400681e0110300c0c041d0000440c82a44800b42420442003503035851903000130200049802284501511000441c0302e000c0108141c880d8962581e981c3c503030031702181040341c0150300300c104183d0b1320900b0b2600000b0030500030001c903086990060701000882c442c09524502c0b048080014190f031409184102010540d85d00207035003c0e189500d004039950740400002494031402400d00c40004d4008016400021540000c403495890800361100c1e107021551001d58140c081c076440290b8400d80011080b0a10b030069202d413040e580702041c08030b203001c0110341404400e1040503010700800e00442d4a00c03000740340c2e21384642c02c2c406006842803801459a0702c0c460096403400410300c20042d2414148130514003540c0c0340300803842d00400741d04400c008201002e841003000e481030050080d145005004119101288130b5a10301c072141d03400b011651107410b44001d62100c1c0007940c01c58580000000103140c035024040005400900450401042d92100d84406111109a00030620704100003d03e2480c0c80404 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 588080890 1250 588079640 588079643
    0xf052701020309130e01112802010b210111030c04060302091c03080f131104020702181f150822020a1220130b010201090804030b04020a06020607082e03 67
    0x400d45e80d4942e94405e0a4410003081030481c81001d0210104c040c0b00700386001080c0320f40c65804030a6803002c01c410303801040001b1065030481d0040c03880c00d01503501c0415000134800c900c0002c00c400d40c005d10500e0002d00086d81e000034007000c1000100200c502c0ba03005000b203075000414000656103a0110301e2002200048100c1c082440d07441040742c64011041d41c2c503440340c2030310180307002c100c901d0351038054260070700c1d8031244a00c0d8045521001e54680c2c81c2c19070f03000419507003043e44504104050350700f100c42090004c0a0041614404030715100940c0340c0c058801799076241c0c3c40b01360300c0b503481500e10824002c03d60120100600191340c0940c0e508000c030001070104410011801c407050070042e011000b00c0018030810381c0c51344002c00c0c02d6294105048003140c00d08000041015623400100d0140c2107504014003100400314003c000e0040c2010120300071442120b54803161030390b5090603600c0e010111000c0000c01d4450b00050001c3ea001e10441107441c030220005003c00c00e001c425144080d039180c00 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 588082140 1250 588080890 588080929
    0xa0306170a0308090c03060f19050906010503010e010b13020a0c05010212070f030c0c230304140f0307031e06090210020609060601031505210d030b010f052701020309 73
    0xc000d050f00914a01e1300075400d000a000748074903d10110b66140000340040350005071003000209005072920324030450b01d0401000f0b0003142001c400d525641d4070b0a010b42d6200707510344260910203050501c550300220394050b00c040e00031440010300d90000c2d0450b030f01c05130910a8418038000002d000f84014283c0c4541440e50b40c46da070a02c07200061094000c00c1109041c5854a880c042c00a0b4000c2141c9040d2640a08d200700c40740940e030910081150300c0ca802c0c080d50b00c004903002c44d51050346100315070002010b0b5251410030760030008040d6900003074030000d42041c1280003141900c1c690000e500700010b01542020405030034940c0413480a840408a190050700000103200070144180403c5410280c00d180034000320001e0703520311410f404644501c034881d5501d0004010240309482c007002c0c40640c044152140c0181160000e40584555280140004c200a5502c44094052020380e5020200c44100c041e041d00300c214000008001e0070400c505500c41440300d91540d0b9224040c00b81350068107807 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 588083390 1250 588082140 588082153
    0x507080714010c320d11240106030b0f060f030604050108011b1107030b1006092102130f020301140a0504020928120c06020f0105070906050a030617 65
    0x18815040200c101e001d580c10048501c003040c0214616110241d241c0b103809801c0c1c2c07035146012045410400d103d212419090080d107440303052254000d07060111a0343d2107000d1b035081c90103140d810241d410740507552070148918800107111300742c442c0e4864002c034400a4401d10026500000094068202e0b07a0501c4007614000b080101d0350502e40119030041030b4031030092286010070481622085c070165890707020010060701c050340d00700d8204804401941c1040000030142081c2c0c030032001c0000c10f0300820000c1803103c000011815607080149580e441d044d460b240200b18650300300203609482d0800350918070b440e1040361502d0915840114000c00491220000c88000f4405101c0d000901d0b6100340e00c110f1040c00740b180c00d40c40d042e4941035110200392481c8c2d200041e5540c810102c4280e50003090f074a50003480b98104001c443e803458030599015408848080c15407025403400d07074400301c0d00580000c240d00301c10400c041c060409000d03909298100451019246c140094010ba184c2e02c6555840c2e010701b = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 588084640 1250 588083390 588083399
    0xf15050c0a110a05120904090c060509030f0c01021b0303120117120f03060910030b07051201050d0f0201030e010e060a02130b0a08011a0d0504030c0b01051008010e0601050705070807 80
    0x11641c1010341c007030b020140c83c01c00181c2d215141c03034200410048032411400115200240e9403507010b0700801d64090824000c49031904c00c0200b9a4000e0080d15000348182400c031500c41000141040c24418164024980f070000e0214405680740b000c0040c2c0c1d0144030510151016000d2009480d020704002500c23000014001600c1500e003003050310329880c5245003002240c0402c0d03540000c41e540800291410700140e240c1980001d070601207640080c151505100520018a030f000b002803541d0500040600220b9803170381e0030001d4540503410010400040d010107400103501903080f8802b60101e40000042da09070110146d401c002d41201c0c0075401c59400249201520000741d0804040e040355440309040c13000f040409000c00006000f108401800c14002c2e85234915014102d451005150300107000078105440d019101d9044903a0840d0708208110011510742007400f032580756400103079960304450346403040b4680c445030041c0c01241000000c01045c00801c03010411800202886801418450300d030 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 588085890 1250 588084640 588084647
    0x50403180f081509120307020d0909050105030c0f120f030408010e011104120609020d03120b01050c0c0607060e030f030a050a05014704031a060d0f15050c0a 69
    0x41d001048a58a03012052103000d41c0000c000c100344101c5a112001502c41912080c5021008030940b0000d820001c04c0000540e80410034260301e080fa512030032400c54031145190f05480007405400c0d0594010800400e0300e00c2c101418800074030700079003003058031000b0507030103410400100c4003645180c1c400101006201424400c00d103c614281000700001c1d00716100c10a1170384518850040da904070b000100c0b0a015003544440c40c066401000760809041525000d1b1030103050080c44a034062400b03509046a5014508540d01d2004503409000500409001c00246400a850075100580c1d40d07511102400c40c20030080030201884580c0984138a0000b8070b01c02a13580c0203003003c046909140041201c40102040040c4907002d0b02c00070311b1003c000700c60070030800390002c1c48025041c81d0780018203c442407201c000c006030b1780141c1490fa41d2085030310303040040c40c4054800c2c2d60802c00340c2c0c1091000c1071400030404006489060512100003444021400392907003911400e5101c0000076901e00559003 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 588087140 1250 588085890 588085937
    0x140f01020c060a06030209060d03110304170d023d0903050913090302070320190f050a0302130c050f0721020f0706080601050702060706050103060c21110c01050403 72
    0x10034020134800c0500b141c0c080340180314090402d9015445c142c144400701801401c0c2c01171214a4613040381c0d10f80365107088180306001d104022510300d000d2014100f40e00751004c10544600007558280504021420f001c83c400054003410351601100e8040c0881481c2c805401003001940c000e41c0c40c251a024481d041145440300400c050054a1401c1c4000340000e801041c1c0c50116904003420441940c6c560618020204040280381e5000006c0015124540201130090702540c01d0b212001ca005c0d0345170014000d9040c047d0002030350102e1010300b0b400541802da000008810101e00c1c04a0602140da0010441030f0070602044422094489844162440c0340e9012001807002c2d200400311404940300003038440045002d600300f003028000004610b40d0258040300c008941c050400b42e603030303819418810002c040a0104403a943d00b408441401d251184142c410183e07407016000e410604840d500400038003005203200880c050901803140003440c280706070307445240aa02d4250790310301080018030340c0c0d40 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 588088390 1250 588087140 588087151
    0x512120c03090a060c171e010f0803031602010e1f050a111602030c061b0c0103020f040b070203010605060315040501091109090c120106021011090d02060304140f01020c06 75
    0x140610800004030000515914011303000031000803a865290b1003183d01c03421000d40c035500803c5120074854003c0d141d40c040c4007041c2c032000d070141081e40c86003284002000607100b4100340340d000f4400704022a9240c441454820118000001e5800304002c00380e04103140b1120710720314508026040604030071039004540e803042940008100240303c0040241c49801960315000711a04806501030442d20100540605030030003c0c94140ca070464400c000224035044407030036489009019828207954007a0003615885204000314500305410a0400d07951354102d408240d0703046d92200750000c2c0585528000318081c2d48202c0c210464032400c1c1050100b80d0304113a0101d94003d107040050003001001030140e1301c2d111000c0b43d2042e207503142d6049032a1140500030082006000003400021490340000b5641d425101e002014015504070500c5082c40b402000d0500c0e03044001445280c00602c2d04200465016105000248070a00c1800d0401d19014071303103020044581d0300007035041789400c081084a6002 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 588089640 1250 588088390 588088411
    0x240e0709060605031303031e0e031b0706020c120709020406030209030f0a02131a040c08010f0e0108030a030c022508120304050c010f120f09020111010515100c051212 73
    0x41c01e01e03072000030304505c01c002c0c003a040541d12201c0c0625135008560700d00800860362014010300001c81c4455480380d2141312880003807810880c285c89a0303000828040121905034001d4030410702c19906001c11941050443c0d991800b440c0e0300442c102090b071010b840031b4101584e0041c2c40f49200800d0518041954858503c19440100810010b81d0362100003403040c1c0c0720881c081030140c2d9000802002c6898a042990b0181c10410b95075241948660003d040300e8101c0040300c1490342e100c0d0480c000030b4084c021054240c00c1000a9201d00303000b41c10603421941710780b04035416010071003404070308495080100010320522000c1000510380c104064080d15140b560840d155082c651f5829564900703603514a41031104d00300f2440707145400b682c0380c40c00c084480300d0300344810503d1002400c002d090f402002c9001c1020400304100d141014407030507229020440b5103152042100040001e41d0007050340c0c160400c6105041030307000400c02e01400a08154040c4034a031549000075443c0b00d09403004164a601 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 588090890 1250 588089640 588089647
    0x70e01060f091d061c150f15030f0323280f020c04050c160c03020301050a020313030806150423030c0a0312031409030c1513240e0709060605 62
    0x445210701d01c49420100172280000500c80c101000c0c000c00321403132000f42282c406000c3c6801000120781000409a1490070200034002c0c0500c09021070310b80034040079040013032881c40c0100180c0a90382e8614070030340509111502034140c4881007104e0f44480c488040054a03813078000414a000401d1240740c0000b400d051981d040d0411000755100e8900b920139200e0751700d9402180810840d1f0b806c54820900050724404200750600b041792a518007440100e0003986880300041c41e480311031094900480174410041000c0000d52000c40302c185000d0300e6030307601400e2012032030b48100d14200107100420300c1200d10f2422407a080005151a01c0e401911402078003c07001040007552041c2d1a401901d82c0120500514118080c048005080000b0f03100310300c040b140c0a204054800001034503a180c5210100c0c0c92054140c03400c0c0c0e58000d0140c44245800101c45107050009100441085aa540061041c1c2c2c4038901c03000807900b51480481c924060b030f00218401e02010002d4050100030b82200c0c1081440c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 588092140 1250 588090890 588090929
    0x305100b090d1401060b190c0201080103020d0c05063609040b1003080706020d05070e030607030e01180c0e0c0c0705010507061401180b0f10080702070e01060f09 71
    0x600d403103996034252107001440c4141041000d20009210f1003aa000000c109641d241c1c000417881d94400501b07000501c8a00c1c40344074a0f00d05c103c0313048a1059040e954214030703918590034010507440c8210100c5413580310b94000b08140d105e0174090040012030f685415541c40d20510345001c058106217908001c141e80c00c03041c51680d1621030010350469800800e40441750348000301d1741d80c151015000100003003000602c01d0240079070358018282461a810040149460758102958924450f20f00b89030550042070009412038000d50150a042c00408008109100b420b0074000180d510034800f00e0f8003040c1d0400900000b2081080280c2c000e444405883ca0480b0003900c665442160303200c1c50b4100003000070102c080000b19040b2120301039041c2c11700d683e2135840300302c0d0003500020980328009031840c102030700c03902e890500383c40711107074002415000250030f103003000b20b45402c0c00400144c190300c0340300b80014032591000c0c0498020011a03442200512003120010041c542704d51001190303401030306a041 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 588093390 1250 588092140 588092159
    0x2031e03190b09161e022404050d030b060403020409081216052a0a150e0304030308270a031211070203060630100e06070c060207110901090c030510 65
    0x103400650350b01180c140f42248400844900d200c01c503417004550244089803001680020b1852000d1200030510301040309101c10b40c42055804490142043c0c0c030a0305010149406940080c41440380034002c685003a8994000c5010f0b142a04011200c12400103280c007802d0303070018003154000c5003450940e0700c45111180010400d00134400078041529010b50843e240c0541c1080310310982d03030114140c0754100c4050400140720000b01410b01b03e03080c14a400d61135400c40200454003a6a030680303400f8402d480d2144561003140c40099005a8644200c12100d07110408100c2c202c082c034441d580c3c4001450420981344140da03405480003031111010300903580103a83c0490303002d07400241a100592012042000c0302c420038466914461010746411803403010b044c0c040b44508034161099003d1100e00c00030318440307a40709001c45e9010000381e001d03400f0a00140d19500103240f5140600708449805a0240c00200030704800e90003c1c103c9540c8005100c405501800384660004106441c10303000c070714207074411 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 588094640 1250 588093390 588093409
    0xf050d1119081e06030c1203130501020607020703030305060d060e0604060f0207240906060f0f0503070317161209090e0c03033403020c091b091002031e03190b 70
    0x20400c5246800034529460402603101001e50050100301c41c1011f44022603220380c8018140d201740807044a001c10703254000145540a440d203640140162440d6807411401040c02500041d0b2298a0f4510400400e40f24010035600c460b41340d01410b42ca0801c4d00d0034404880c60078100344162401405039a011407003120780d00110381d21844102c00d5881c82404894014891548001c0c2411b01d05900800c0c0c0d100401d150505440300764494880c1c403500c80341050b91f0303448a0302c802481d003c8243d980c42031000103030b000340c00d58070b5503040305106048007592078140d82040d410200c1c0c001810740c20200101001c40c050b034071807403481c200a0070030344a8080c0032944a1203002c1039006500a2441200c42807070310046a1881d46100740380007202008103103002511500691070f401d105c0d000e10b81c04140350041011152780024400080d003450f04012400b0300c029000d9850030300003980030038000c600c2009803080e02c144a0040340c1c08025030341d140c070a40c1d43c00c8042030201d01c140bc89141a02c40c104940b00c0b05d800c07 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 588095890 1250 588094640 588094681
    0x15130206030403020316060b0f010203090f0d0221010f1113150c021e0f0303040806040b07031b02010b151309052d100e0f04030f050d111908 62
    0x1490780c0d954030780c181a480c41c405d821000c2c44100a001c0b1540a02045038090646c4617000c4034040344c1240103d004aa49006105009900036289200c0b800d19241601040c4085840a0301c90094150380421541c072000107102c9003000d594450180640d80c1040d03225401901040701d080c42e04054a03c40c0d5031400520601540c0c00310591045013621290260b08030789100c07640142040c3d80340e0080c90010f00805001e07501c50703018001c5840103845c50315021050b14152507107107004240d1907940e901c4516100e100a03103c001459038910b040400c0f20340c0641e00d40700c900d8240c0c001003503079562401804a2058100d501e10641c58080c460070343c03ca41e8a80403941100d0014501280e0f94803039410781c904201e219942d004e0b0f03072400420303659144151a52110701c04c03a01d59400f207082d40d540348420381598400301c1c0d549070001500400900083e00580c221070032682c680c5441824406299070720340c121441910901d60040300402d540c1003404185604031150b4415180010f4542071200810005034196180c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 588097140 1250 588095890 588095899
    0x61804060c121a0307060c051b0f040603031112040b0a14040801090308070912031715330c190809150c160b030c0a0e031e151302 57
    0x420396070641c070415456160881d000c00c200303d034100740e003036128061031072002e038074001c0c00741c580d0010f01c190007411002c00307032504080506840c61a100404e40391481d00094541e00901c1000075011613155841214040e501c13a46882e9180228030092625003911001c0c0310a455804201c00d11058a00100362540044c541c10f050b0480c040c4039016906a01454000510a40c0703484007442c14503502000c1c42e409809035444004a079a1518081c4210180004c405004191401890f0f103a00e045581850b5100d0042914000c0d0100340781e000400c1034596082d01031490420024400500e500203015501c0d040c000b04150345003150500709681c031060f40c004000c945280700300041003030240c3d803c1114030410000b8800c080c1200c0440080c00103804c01c0360b10390388a1003002c045031100d42e080d6041e141074036001201c450843d035904102c00c4070740c2d008d81721000c20001402907092254504120409901016004001e00c4c42444d4030f00918101311100300090707100c3c3c28405e100b40300408420f00210150181c8 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 588098390 1250 588097140 588097151
    0xc0e040b150a230408030f0a0302090a0803180d0f17120a1508060f062b05030703030b01260403110f1b0301110d09020a1d01090506180406 61
    0x5046455018081885040000b8a501d40d0039803154543e6066280b002c56152500d0030007401036020300482c00303040400d920400000c0d1400302c001001e002110344920700035290070000d0000c039078450040d83c00340c0071031742c8040703034102c0007181c0700401d59203601c800d413601c011071881500d406940811446020b452140c0312a40c009d001405442110710142003003442c400d450038911000c4004000141030103d0440f48510041055003010a42502400c0c4094100d04907454800403c900c0070716001d42c40751141c2c0b14000d445041c1210800100c502c0e4080c2c405913444862a0030701505450300c2c003000904115070b15180380c0004c4010109140314545000000c0880d40d03c0f841d0555400303604946022491003181d8810308030b4032001490b442e8071661181640c0038042404145402e0f01c68405200001c4281404100e0050800d540001b01260009203150800742c0d5881818800d084418030360400403d9180040c40030405600440c0c1c0c00c102e0503500500c00e10030543d521a02c03080b018000404140c3c031074 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 588099640 1250 588098390 588098411
    0x20c030909091c2601080c1003230a0e0304030506192003100603022a0a1e1209051008090705091e010e070c1b120f060b03010c0e04 58
    0x401c2440042e0000d801001140f036101003029002c40c450b82d01904200c2150704280c04000803000c1802d0403201c548004040c85400b03201040f4542e03890000207020180c0d038415800603585241c0710074030403588040744d0004c18248203003141c007a40c0c81c44103031201c0e6a00400c001c100050f00002c030b140e40034405940c1c03070000d101c055410714064965285400036424910800101440c4000300950203100b0040e556450640c4e00d1030250107038013a1011807103101e141c4905040110071a110100c3c0ca94107030509503003003049203907518060911a550300c5605107080e282004204100d81d40001ca030f01c001400c000c540a0b2600c1c0000e00322400171140c500800100070042154010304116100c06480b00500d400b1003498240303220381c81c00307010144200500e2a007038000148507642505003405407005940c1c494007040c03e40c58001c00c1038207080c215030740440105000910301c8258030950f03440f03e10170060707050311352082d04151066a0343d20380e400d842a458901c0b0190942c1c0c00103110b11342884207075808160342d00311 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 588100890 1250 588099640 588099643
    0x601030f17030a0e160503120903100e01021c0b03060a090f140c040f091a190905010f0c052a191506120312020f09060a080415020c03090909 62
    0x800d288901c04030000300a01144800c55044054511040001c1321002811800f20f0b12940503184119601a001841c0e50151014010300502e50408007404a03207170b000f4a41d28600860307010b100c18aca010796010598045031481c40c8601d11010805400500406000500003074503950068948214140da0303400b1042005110442c000e680c40e00560583d098038089550583c80c2d0841c41e880c40d11517490081e118030b8410f11849403151460f0812121322130801c8a070001a014200540303900002c02d41070320070108041c2c29001e403100c1d152062001246044190011809480c100c400c144140803080c02910841c20f144100c1c9076440e45c070100b10410b0084440200f500384000c881c080d0340e58202404140081c014000042507190a100d134003000300d2540d8000d501560351009000400050f80302218400c001e0440d0044c02c030092980e8400703403030482d40c04000350541c0c0c44000c400c0040380070b8070100014440440c8070308541c0c2607030a0040d840d20400031a415103a10548038982c1c41400340901046a0310030 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 588102140 1250 588100890 588100913
    0x3010b18010e0310050a0e1504060b120a0c05040f06060c030c021309080c1501030218091606080403020124030f052d0d1707030504051005010b0a0809010204080601030f 74
    0x10007030107440d8134440d00c2e90b40c0d10103002c04aa800000d01d041c000c40b440c003000c00041540050130000041e0060751156510100585a40c280e0540c0c442d40003150600040310500c22030481c0c912581c0124069850f1905000c20350b100a88500d040760720381030781000225008441d04081c6541860301400808803440085c0904040b00c0701e240480b49800000710030001101e00a1100041c141c046a000b600d8078111040850b00902000307410078a40c0c4400440052140c3ca01c0c1c0c1c101c0b0070300d02680e501c0c03203c4e801d04440f0001594450b000103064101488180360b028415400c0400045010199007c100c00d05640595241d01c0003c04641d11048070741c09110003406030100414080da00140460006191944408006020301c1d20078016004010202401124180c0168500c3c55418200e0780d91880305600500c001402901e482c02076004000120b08540710b124060314808210545400b000a0000d0400c4002031400352146c0c81000305000c3d01500041031411a40e0203a07030407640c0100c0303290100c0c1006 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 588103390 1250 588102140 588102167
    0x10b1c2310060f0f081e0a21031524050f031611010c080c0c100e0706020d05040e1b0706020c100f05061e0d080c010b120303010b1801 59
    0x180c0031080c0d803100100c0c0c10403401c43e03120010030f903545512881c0001040c001d510034000c603588284200c40b425160b0740c000c1040c0d0150784007600d5002030301c3c3c0c03a50721800d4200c0e4000d1036840104034040c0e41c10b90300351260340608600901c00c038074060308121030071140c440749681d0b0040c6040d14551411006205008583c04611201e90b156180c0c1441010a400001e40410120105d5004842003092400500c18100d40101076980c202c0c043d02c601d20f6548080e400a02d0946d258010303040382481160103401000000c03100603000f4444c2c10704c3c2c60f0b07000703080c420300d90b1008040180400041004104c201d03803064100c1c081c158050706416684904041500c00da040c028400ca0004c1146502c200010407443c07207803604480c09004040400741d280c011a00215401907110742403142c0000c00c0a030000c6005c241c25005026030350041015114200150403164034000c2e00d81d190011880e03039042442e004042600100c000310b0455050807011101c900070004002a4119048071094560b882180d1180684 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 588104640 1250 588103390 588103393
    0x501110a0f061508150a20071b210b070306060c060c0201140a0203010e06040615030908091c020f060a0503181c0305071d0f010815030106060c0302010b1c23 69
    0x4101d41031700c400500d4125803080b4850303d031400144121700b890001d803001a19808420307143c00b00513620010641c03001c2c40046541095500d01042c01d001d0501c1100c5910071203018016980311901d004d50702c01c100284801304050608204204a9812094889805038004000b251094406204030300414459611111022010741802880034280c3d00550581da60101c3d008056610f5400b0710081d59500c1c4940f084117118004201c00c0284203500840500e80700310760031032070410761100007195501610040c0d005a030303400c0d050008501d00403422040c41d820030742d0100e0401103650f40282c40c60000074021204403003003c1006042001c20300100f105020004051414204807900050041100f00d6103c0c2c0415028896400c84124480700280800c01c0104072407140f805800044032030303c80141c032140300505809000c2e80107a50a0154102512243c0e4076060082c81d42d0030001c0c00d40d038490600d580600e12054072a285842c22002000189401c590944c4024000d00500c0f11251000351000e13069 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 588105890 1250 588104640 588104653
    0x304030b04080c031b0d030b09040b07031e060602012909090f03072f0a1a09101e050702100507140a062f0301171c0305010501110a0f061508 62
    0xd0000081020015045000407100c1b041801c030303030617802c81d280315581681c0600e2440000d00084e2516842c1d65001c8000e00d008124000c0392420601c00c061202c181c01e070081c2d02e1740f00500c6440c0d424840c8031800340040000d010b8a202d058030080740346040080c42406200404000386c1580030800c04540049007190449581d000a4185499019507085c044007100c00420a0700c11005503130050704854100040542d4200780c504070204203540803905150618190501080b58103907100346501c0000d180b9900c5d0421300c08a162408162103d8901480090102c203001e1003000d621007016114a82010f4200a80c0c2e544060400e00685040307110080120710541004200700040c0c3d0b0010080300103c4061a000802c00d80c04604803480c172407901c141210b0003400104040c0160300c40c1000c40080d4901a200005240c040643e01010141070803000b0a80380c5004100e41d50748055550b500045580c040d00300b000041d9a07150082d90311030b00103444191a508070000c1c100109180c50000c145c10740466a0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 588107140 1250 588105890 588105907
    0x30f21030212060306061503070e0603010801060311010804030203120403030b04051905090f0303060907090f0306060e1003050d0f110313080c0409030807080a020f0a05180a080304030b04080c03 85
    0x280d8400c07100000d0040942e00450400c2c00d0008480b40200d0300201403c0071440c50209806007500001c00043c104400300445c141561a0400158042d01d11000081681ca04504102d8803100c4511102810028240d0030000030980c00701c140e521801202000c81c2c0903480c0d9040450140c01041e11150b449858442400904101c1030078801051400303103820301c903c0d42e40d001e09030b455a541c004a10003580042000a081e0b00d00340c0d0342c05a00a66a00340358078207a459000f842c4402c01c454004507072040c1d407440e040c0f000103501c070121070348038081c4400c4880f150f0840d558103454146d0710f1500004d102c0c007c0c10510aa5000e4060110002403040449480d0f80500906840c6450700b442440050b001d401c0c800c0240d41046e01611400da80c05480315402c03616080030454150341d0007003e00d462a9801d0001405407200580203240c05802590380c1515035040001e1854041e00001ea010710590b580142003021301d00100c02d440c1200c5d040849a04541d42e1420009841c4c0b2504880400d503010000c0c4400 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 588108390 1250 588107140 588107147
    0xc03020d0e03130f060e040e03071a010602060c090112020c011b0c0b0a090b04031211120115110c010309020406050603010306150b3402100203220f030f21 68
    0x440308810b031080c0910a44d03640c070018221591806581c001881c800042e2010b4109508210039440b11442181c0c9450300036110b00c0e903182d10301c10410030829441d0004200880d8104190b81d007051204402c18504000c420018103060b450b00c04a1034aa034000c100c14514031000c1d03024003904595419000510101980000d09200004000b21207540405021a2505519114004885620203808455600c5a8605655003034843e0f801010032512522140360941c02040034049a02c01e200d603a00c85541030100b142d418160f00d001c2c580c10880b004551402c3c8020000d038001e4028003e00300014100c400d400424003400660300300a4000c0d000000000400c4602e500240c0060102089904a070f0b48844ca10600c91041c00300702d04000407118181180d0200001610821a041400648502d052030f8007150034880c40d4070511003d40c202140d651510002a031061510f071800000c00111035081c8030a202103010280805007a8011150351001004071842e249140701800085030203c10b460500000e = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 588109640 1250 588108390 588108397
    0x9010e042309150402130b060706061202090606090117091212010501030b180f06060d0f0912090303090e0711030c03090a0f03020d020d06021309050604050105220c03020d0e03 77
    0x160861103603025003900f280751921000d002e164000c094409914295440300003030001c5ca100300340d100e40f04100030340004510b449060000d103143d50427400502c13440d004002d045480140700c540101000c102101c03c2e0f0b0380c400318401055407400700c03542d030a44a40416910340500c4d81c1c00e03600b0919000410009040c04130031458121070090764103224042065007442186910300301400c0d01c10b29600013040c41800c811940ca64055405418241000c07040000a004ea030342c41640070b80c0c580c0d61021950140011540440d99100a50615079112072a658006021114038840c41e03803031071455008119124400e404c60b6142501d00d070700301c0351641000c804983d2264022007400d0300c100d03586100061091500440c6070300300c0303070002e20226108d100d54080c0000c840c503804048039244d030700300281c2e00c000502103019800361038441000915440c20100344000c559040c0c2016210700400907807550701e0101d040380001941aa800c0110700040441c1c82a07000c0d00500caa21600182068140500b500002000d03 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 588110890 1250 588109640 588109651
    0xa08010e071b081c06060e01121808030406090f0c080d020601030c0605031b0c0d03200a1101020705070308030a1a0306010b07020d1b0807090209010509010e0423 71
    0x1000c400da19600c20645000740098194910701111225803000701d4003400103050b0701c2c12600c00030b601005000d074034841242d0468000c0004544c11810703030105960b21446000448182003010486a03010307140c219040f6041d10030040410030000006410000d154000c550620ba003d00c002c0c980803100d1429001214a5000d5550a480f51005004c2ea162000030800d0481e9089903a240b5014100381040705e0700d6000401d200e040b60808008400703025100002098815090800f8054070f080c504801415140b0f18015406d50710318580e0200c8414040c04c040350701da0901803e110400c10301300a04140a8090040701801d503000742c1e0b000009000710103008511a544544c0100035502e80151a80c00400d01d50002503016408030340103002207a410310082440f00d0004180500072903040d562450041c84800b04282070043c240010000d02008001d100041c1001c001c055007405503640008006c0d0150341c2c101c60401503400c00f00c0140380c555500504800b806642c1c51040001e00360b061002e02c031000d80f80c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 588112140 1250 588110890 588110909
    0x1e0c040510080f030f040504050603190605070f05040f05010c0c0f09091e1a090a061503060b01050a0503060f0d060f0c09080c030606040c110708010608070506070b040f050309060a0801 81
    0xa0b0102e204001c41205c48181d800c0d8145c0d0308003070070082404001e2000800071505031149805031510b08001e060854000e500c52074000c06d691409040041c25641243c100f801031190070f2105200710004010054103884080ca41150310020340e00300184045c8950344961074010040801003841a5940c2080c24498002d10700d0701035581d94441780c04027041e0f07191030161600800580301c02106c16001c030a507030003168000c2256401c0e913075610b0300e404542c102220020101c0e42d00388104200160f80c000d41340c200c2000d080c901c0c100720030407030041d29070310000388454840d8207026020001613603071032a51240c042d04004100503458040100d40c0003000034045090208140c20000101c41c200055510300566002e4094842c51711050306001c0a080c400c1c09000520040e00006414000d082240742c0041001000100b1180e00c0c0001050a000d03240e04010b0185004010000115040303400c659080342e8000c00d07100d40c001d22418014214003c080d0381c50b45c42200040d0007441c032580140b0040c162080642c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 588113390 1250 588112140 588112153
    0x4150203040806010e040b040b0c09030d1e020105011d0a020f07030e1504050a091824061a04030f15060f0f0506073503040308010e0f07021e0c04051008 67
    0x91000900d20b4045900421210742c0400041c0011840761619412504d2441662f0070421000c0000e82041609540c40300003801d88144501c0340c0152116020000c01c082c0004c02242d414009110302d0702b50440702c04000b0100c0341c004a005604a0340c101c1c1c40c840d111141c190303190507540c074005001240280031180700c0d0042c1900d0320340d80c030040004c43e02140d6008090042040c40d2600c40d001402c1046868001c903440d0700c000e0004116040091b4401d00c410f844008145900401407000329851504518101e2400b0070348075641074882400c071420380b50840000c040342c11951600c0603030507103041c3e11106d400342400f00000b03401c0082c02800c02925080b4106c1030442d6150402e10815005240015060b2520b9501c40c92544001c00010411103c091901c041c00c83c4000d680c2040a84c41a181200041c503802d004020701e000113142c5a8010340c400d0043e1206080a10000356960154016820342d5141251140b103854810446061011400784c801e104524001e041c00c500b0307141901c03031028240110fa = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 588114640 1250 588113390 588113399
    0x612130c0f050918030a0c030c02030d020133031e050f010b0102010f0203063105010303181d0703050a06170307060c050a17060a0506031306061d010314030415020304080601 76
    0xc040344c1030f42460041d070629810300d00440328408104400e90a2241d00003910f000768806010504a5142540009c5250580d1a0703181502011900a001005150141d41d0311440c3c01e60380301c6d10449030055400d142c0210350b044240002110400018014410501140b0f000c4a041d0094103540f0002d030020411814040401d00a900c811100150700540345110140711464007100c1589603580700e480e0a02001c0c44584940c01c40b0800e81080e40800c181e440469215251100c1e40000350482a611070500c02d544400c401d0003100141100082c9529200001c040000030380c4880000c040c41414079081468906030a5200c2e4040340003610071606010b000c6891034080d104580100c0410381e52060340000b030136644803030150003401c0c0540c0f0121100e4000703550340c0c0b04809103015002e00b0109506100d0580341c10300c2120030581c0501d40f603104140300340e01c04405900b5003d04503500018101795510b592014181035100f1504195180300340034910035405940003005e4801c1d0780642d01180c50590b20b6 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 588115890 1250 588114640 588114661
    0xa0f05070f0807170f1509070309020901050f06030402010327031106010f082107120e2e05130302060301030503040320060403030e040621200612130c0f0509 69
    0x890b0b5150408401507000300d00414082000c00e68090311b1a8200d203880c000c0c690014400740c5c07042d1042c000081c0c4a104a07015444d042c2841d500510f01225071840c070211400100340d05000090004c0d0505980301d00d0050717a0030301c0d4042400c044424402604030351750135240150080c40030101c0d0460510542c0000303d001c11504220100740e52040d001001410080358a80f4031070119032158140001d0140203200000e000303c4603201c0d405a5940b40e01045400200c2440b000c00c48a0610020030152407414155426120074107084140720ad2074200d5550403481080e4024400b1b40e44001d400020000000050100200207401601c3c42682c1c0a90a00c040e81e035000d0b59494940005503000d5000c0008200290088030100741010020b0f0000c24120f5450100c40307000100d140c900038050259000440412540c01100d9181e0820004d00300910400d4070302140c0c1e0707800360600840c20094000089000000306d0342148100035484414103c4407500d50040c099603410742e1080394020700607000451060131a = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 588117140 1250 588115890 588115907
    0x30d020d0e0a1e1b060302040617010521120d020a020f060c041203030b1905030d020619090c0806040302100c020f0604120504032906060c03040501080a0f05070f0807 73
    0x30028a511040980209a0400c0e41e83c564401c55018039001034074000200d200a00038000c01241d100107071240e25054000d003400b449181c10b1042c003140781005002554400d03428114001141e0095541c42040d609428031380110b0201d2032400403008181c9481648050300100f2450000380c2c207a46568020100e0b443c2c0d5940c3c01d90b032a100c880c909000c1402114240009001801c5c06032802040c40e45034600810075039209501d40c3c1e03d03c862401400c0c070a0782410408035018500354801800ca03480e1035a2007511484426410303641090315100c00c5010b01c0001e012100c0900150000d65450340cc052070041d545044464010302d509040c01000d030203150004c01c0607081014241d000e04410764442e0b03504918500b40b1602d403c20b014080c400400450315104e4444100200140b00054840e074500c0ca00b03031a1040101118400c203010021560341d00b0021056030225542801e00c2d2101d61111120b035006443c02c55425402c041c944010000340c2c541c00070780c0e44082607090721804400e84030000d00711130b800c5 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 588118390 1250 588117140 588117143
    0x311190308180117070806040c0e0a05040207020f0307090f1404050604031101110c160803030603101808031302010e011e0c0f0b010608090105060102010b0d0204020702040e030d020d0e0a 82
    0x8100780119010b54048000d203403204601490207000500302010846074654050300c07424001203001d030802074a41028418408401d2090a106000b0141d41c1d0008002c4d110b180203d0740220740104564046484014060308080d1b001820317543d94903111b0608100034202d031110002250305180042c0b00c1d100c45480d44600480d00507001e407503145d480d81c500b0744580740c481688410640da6280e20510aa036920080c040740101e000207841400200c003000e051842260700402d0950b08100248074050343c001405c860a400d040703a0101f00c11020034580c8070b500c81c03400c0c0c010308000c4001042240308002001da0741d890074402d8071030002d241d503118011180303214070001104860200c2440d59401c94020200007213464881d45000711513481582d90226442c2cbd0030b0780400c0101d03505800340300c0c4881081c00340c07a51012081c8000c03c03000120a002a161060250b4007038006c035400940d14040d074076140c00403071741c0040e220202ca907603410180f04c1d00300035802449440162803915208450003000400d00702d084a = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 588119640 1250 588118390 588118403
    0x10b071a061507020a090606030b030f0d0f0c06020903010c0c0b1006200309030a110108012106050c090301060f091a0312030c0d0e060103170703210e01050103111903 73
    0x1030340c2c890700c9652540c0400000d980c490400000001c0c65001030051402070221a41d0114914501c02c003454070705030140d81000c4054003c030301000c0e420365100b18001d800759140d181c5803c55103442e040800c000e12483c42c0c415015401e01c550703902a542c000d544103800c0c3d44514440d045640d51500400d60103070f12400f401e00000d207146e4503004031255440050b9648048001030f00d10380042000001c3c5405201d010888810400150008096801002c501d00428843e4000e60441e11040c9081140b60114032004058940da04040b84140d05100181e6a4850001d0001c22103240c8804050712400034510504410509103000f0f04100c07645007602401910300500200055020725079901c80d5500010900807494106001250803c01c1d94007459030300a2052000e0400d0707504600f0544c042043c0e42e10070651601082000d240080d522080b10074845c440c05403108418050a10f020b4003400507a1041107840d03003880c0010003807021740c43d4000c50250007115401e80041030036030700c040758006500c00603000 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 588120890 1250 588119640 588119659
    0x5030606210a0f03112a0a051801030c0806040b0402040f11120103050c1c0f1a0a02030a06060302030906130318030c090501090c05030a0b01030216050109020102060606160f1a010b071a06 82
    0xc142e40a88411040c0c009040350047c50326500030a56603c0a214504007200e502001081400f00e06185d500c050101c04007e4085c501d0184c803001d01d00755000d00004e000707554441d09568054143c0d403000d0f05c22102984215076503941c01440b200c0b041d03404c1c00203132000d01962003422540d1400e490300004c0e09030081d490b2102410951038001106c000240c0c15689000301c01480c08515100d030103105d110741b0340c4940042c1c403418041440000c03070701a508058103140c41041840f201d568001180e41e40144d07141c0b40055941c0551408444024011080c400c068146031004020403008600010544445020401180c1c0c0d96030011800d07501d09060300741c007080040011070410a81a00842d4000c43c043c1800351034056007203100f03114503d01d02401e98241c0d545000030011580d042c00820b802400c1294282d082403198101003e902c500310740e004003120014a0224104150200c0d1131011041c100b510401541c0e4032004030702d0542c0414812940401c2c1e503400b0b142001d01c40d0301241d01032074025102010 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 588122140 1250 588120890 588120943
    0x1407050a1703040806180723040b0102010e010518010b150a201605010210060e06010c0f0507030b04020315010807180b0d051605030705030606210a0f0311 68
    0x9490355070301584203050004020101e9411400c0201500500f050202d01b41c43d80e204c40c801d0350a180d0760741c000305081c11f8010b03040c044400300c03c00081c246801c100c0c1d000030302142841c0141e00401d12a1a007411550818003000460307010240c1125110403014024054101c008041085440c450308079030000400500039260143d214801c0c0c400e00c801d480395011030940e22000098a40102c0b80f41e5160105081c110a00c52540d0510500402e00c42c000003e011050a10048030305081d8020105030400c880d0041910510007400d03001000a9005070540d200c0d69224107042c03042c903100302e409900920603540301603d16452119418100d882000103492140c0c00c1c10490410300780c10801488216440b11004030061f0754442140409511450040217030202001d40a14160380591200b4400e402455042000d5100820a2980040b0861700070f40d000042030f400190a01141010030510b1141e0403100301000b40c1c00400403555070003500c07115510b9141260096440c0d499138984540d94098002528 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 588123390 1250 588122140 588122159
    0x150b03010b0315070212040b0712050304110402030714030f0108060601080f0406050403270f092703090f09051506180906010519020a200114030c090901060201091407050a 75
    0x3d81004d018810740c1d05c606094000300d041900030b500100c41d00781d400611842084422107a286400b441801d00608514141d02c07400741303206609001c00d000d540c00200094125210f40d030000810445010855160304100c1d03021520314a00f4010902140b040c90013080040d03006501443c414080c005d200e0300e0903504c0341d40349005080003800440600030300c5410000401c0d1040a10b5042c40d9506808441103854108904104240e907030140160318038044071010307110340c003001007181050f0501100d202200d4904d0119080c1105501401c4d02c0b40c008240070502000075000140240900401f000225503107904100c0d0600c1100400070f002c038a8000074070760504182d000399034800c2c4141416810410814070102c1d40c800107090180c0141c000f1204c502c10021070360540207468030340070548054054540700280081c01684d6240106070300100001c0e080003420011922510740c0548001102e5030746200290180001140c2191401c00c035042ca08801c22000490b03c040340c3d0001c10506c4090f03c7d0103e401c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 588124640 1250 588123390 588123433
    0x605060d09080405060a0f080c0a2304031a07090b0f0313170c0a03022b121e05180a0c050103020c1624180902090f030703150b03010b03 60
    0x403500c01c4001d000001e41a0f440d08040c0c00191b22645805442010700031005003d003130010803c201c041400d210704c6100550090311101c01da505c11032440d4050300c20a44110480c000c69100030301142c141c8810044010101d0001401400b107611020962511050010307000d002e11070721380f201d00e00144006402014510300d407800a60007440711610b0125904820318940d44458450724080c3c1c0025095000c040d030421218106d200d6680f241d01c083d07403118a2082d440328100341c136141000151071b21710040c43c0c02503021410001c881e540b8120515548180d0b14040c000445441001c1030468030306000f01e042c04a030307041e10302d9400081d0301185401e00740154020341104500d2107991140d0301d4209400311004200001910031200d41d49140211400c01c0c000002c8034021a10411200540914032640c2c405812025501c0840000d6110b8080380046103040d001065220f43c117214020001060014210358844181c1445809018010945042c5800d94829410541d05680301c0300d01d2405070388100b19039 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 588125890 1250 588124640 588124643
    0x804050d0804150516200a020907090e070201140a1a270c03060405060607030e0f01050732010903020a2003100f061202010c17040b0c01060512010605060d09 69
    0x100c0103a00b11041c034802c1201c40859108000c05d416405100f000b5401040c3d440c000c0d074840312202c80d428809a0810740faa816480028020340224001c2001c80c0c0c0501c4120001c1d000d0107004102030b1400f0a402400703042803084078240b2401d0708d00490000c48540c0034181c146241c4107540d0302a4001d48080c011240000c00200034000045548808804040f101c5280500c40e142c040c2034032401c1034400c01040b40d90140001d031182008001000c0040d821907d0750000d140111207240524080c2d90041e1500d03c946000280701803045601391342e2400a544440c0424101c8484d0b039000051907120709401c0b640350b0b20025000d44c0c4114601c03400501d2003101c4020074020700152640040f24034010a140c14610400b24090903281c514110b100f4103284540c2c002004003104008080341c4680010745405620304000d00032500e400d003032202010801d0308490081104e00c25180c0d175080c402c4440c500038030f143d000c2c00f481400110320000030760744140600003d0b103100501443c5860748084200004004400c0b0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 588127140 1250 588125890 588125903
    0x60604080a0b0c09030703050105160809060a0b060d0204090c0e0111032b0207200a06090b0304060905070b0d0f020f0910020c0301061205010b10020c12070f03030207080d0804050d0804 81
    0x41841301e510144400002075105800126a5040c40ea550a2403201210b20b10000c1012500421000c402c000803010f0300030b948200001480700c05103000c6005403080d9885008840d00020700081c0e10940ca81c0003605540140e61030314001600c880044a82d888550f039405503e51084c0311100001401c9541b141440d4400b0040380400202841a0380690b00030620a641010b80c44661003031001c00180e0f0009501c3d07044840030102c2e800c0c4074000d41880003e0055a4810102000040030020103501c8070042c950404200c5094640c0c0e100010300710f03440111403905150170000d2520701c6025500075500d201c00d100000784d0601c1c88102c1480110f012000011045125454030110161800c0c41a000a4007015405c1081c6c04443d007406404d40d4a8203400b180510307190304070400311075808030b6181c0204000311031000c5d8054649032414a17028041c0c0014240c0d43d00194000101500041c0d0003040b1303a01e0a059a80c1c03201310701c0b41902c04180494000e4465000381c040c0d0501d503840b480000d54014030911 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 588128390 1250 588127140 588127147
    0xd0c05040315020307261306020c060c030601020c01021c0e0307030b0c1e09010909020c07052d01020a120c170310090f11160201030209060a020a0b060604080a0b0c 72
    0x40320844802c90003040341a2042d4008107100c2d200c0d6010082022002e00241c2c941e00d91281c0105010b11610000c080511181d9070030300301d00420079a501210b01c440301e140c0450b00e0500b800c6030034441550007580c042e40503100d0130b03001480e03d5002084d041d007a246541c00850b03010300a80b9054030301e0111041b540342d05008415001c400a284903404c2030080094903003140d11003224281400c0300c00d04071144035107424014020f84c011681d1001010080e40d1701c00c50003580754a085000c25217460400d030409070748107610544410144664800411410004002c420320319420007006988404100001414500c55240403050f020b0080e1618840c65205200401c0c0d18191150f000307040da04140c070610906100c58000b04010351a50150301500910010108020250a040030b00702d072264a800340c0da10700302089142d055a00950680e11141c1c0054803039952450302e104029202c20441d0b0307046541140950218100d0f05000c4144c1782915540001050070154685441140540c010001d030305264040 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 588129496 1106 588128390 588128393
    0x140a0309020a0906060c060609060303020703120c062307031503170c030a0c0b101208090a17030d1a0607021002070918020f0111030d0c050403 63
    0x14280020200c41610200d000c84920303512a0505510304100001c07810340010000b128984903440c20464140c0360b80c1e5503412a0081d0002400582c0701900500024198528015640c00c1c981491b4400303118594421301a0341c01d6405c030102d047e00c2075000040865908a125070024800e0906200c110a07800c2501ea05a40522026007600303000030030b00f0030182050046920b18051701c1c050b655034018610002d440711020030812a04e100007040000c440c40075004940054070f1100c200ba489010058030340340e01c0c980200032907030380c0000d800c200000c031000c55040064031005480c02850710341506c484844111501c11403035240f494008030010307400c4d42e9903108850381c00c0d5044640c00749441031500101c2c45c00716940c11001c44a4034000005507050256040e0700c0e0f03940d00c21100941e1403015400110348040c2060070000c041e81c4188000c1041c2d000d02d400800c0e400096281003410107589 = true := by decide +kernel

theorem cover : BRFrame.Cov 587949640 588129496 := by
  have h0 := BRFrame.cov_init 587949640
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587949640 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587949640 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587949640 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587949640 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587949640 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587949640 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587949640 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587949640 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587949640 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587949640 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587949640 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587949640 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587949640 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587949640 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587949640 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587949640 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587949640 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587949640 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587949640 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587949640 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587949640 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587949640 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587949640 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587949640 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587949640 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587949640 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587949640 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587949640 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587949640 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587949640 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587949640 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587949640 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587949640 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587949640 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587949640 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587949640 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587949640 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587949640 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587949640 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587949640 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587949640 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587949640 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587949640 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587949640 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587949640 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587949640 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587949640 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587949640 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587949640 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587949640 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587949640 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587949640 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587949640 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587949640 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587949640 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587949640 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587949640 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587949640 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587949640 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587949640 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587949640 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587949640 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587949640 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587949640 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587949640 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587949640 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587949640 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587949640 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587949640 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587949640 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587949640 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587949640 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587949640 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587949640 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587949640 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587949640 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587949640 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587949640 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587949640 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587949640 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587949640 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587949640 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587949640 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587949640 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587949640 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587949640 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587949640 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587949640 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587949640 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587949640 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587949640 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587949640 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587949640 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587949640 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587949640 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587949640 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587949640 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587949640 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587949640 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587949640 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587949640 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587949640 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587949640 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587949640 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587949640 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587949640 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587949640 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587949640 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587949640 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587949640 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587949640 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587949640 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587949640 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587949640 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587949640 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587949640 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587949640 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587949640 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587949640 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587949640 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587949640 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587949640 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587949640 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587949640 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587949640 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587949640 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587949640 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587949640 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587949640 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587949640 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587949640 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587949640 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587949640 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587949640 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587949640 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587949640 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587949640 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587949640 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587949640 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587949640 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587949640 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587949640 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587949640 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587949640 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 587949640 ≤ n) (h2 : n < 588129496) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
