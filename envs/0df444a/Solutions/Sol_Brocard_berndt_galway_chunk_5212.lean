-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5212
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:06:41.198656+00:00
-- url     : https://prove2.me/submissions/3ef7e754-5902-4d40-b463-ed6fe472b167

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 937230215 ≤ n < 937410071 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 937231465 1250 937230215 937230221
    0x81e03150114040902030c0c03040807140d02130c03020c01060e04030917190201121803140a020c04050a2003040b010b04050f01030e161e06020309061c091203050a 72
    0x28002801c2441189840e41e02c0c0603218480e0b0301a8851496001c8085052950f1107070581c0e0844084104072580d450310f0388032042c2c1e20704852042c8001d040d8a40402602030428040707a850305a070280824105a0101800801420b1071210905c10150300b80441d8501240901448000b0404513070045d12504260600506500c91500700c03812240d0341d135503411200e0380300095500c040101000d0001c62401f00d440103c035041280304d46020203070b080960b00310900c1b400050a004042c46601c9011401403501900e50f603070f0141304001c90241e007004062001600701504002ea00500030400042d40b014010810f42808101d0751210240c0680031082000308425018058094984c65404500309498800050390383c1400d95030389410907071252007040800303d08120036180f00d035580044100e0070b5158040340145008225100314000189580050030038000b1040700d0003039401502d014913200c0010115440d0540140c00d440f4096a110400e4000c43c90300790358100f090f942680c010405050000000080d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 937232715 1250 937231465 937231501
    0x7050c01030e0703030e0607020d2418020f150708041805270f0706030b040f061a070f0b010902120906060609010f030612030302070b070813020d081e03 67
    0x526192000c0d04010500c001403400c1145e0741450100d0b0101d203040045100d0340902d120094011004041003810450800401d2641c0f00101044500e107525094540e401c1c1d58510040302410300e984489240941000a4002c40c0c0000240c091886055900406907c66000c50800e0b5070401d404502800602e48240c85401550041c03903092240b400c1250b0701c03010803182e281000e024219080c141c003000d54418410b090b00e000264080c3d03a9210b82d02c86c0081c2c041c1400d07014182c41070303241018020446550307219040c180c640c01a4100301041074815868950ba010007810344044412080000000300c1009040c0d020380002c4902580b100b0000440c00c11070074019024003030340e400030300401415458450560f8100c1c5003d03e460800742d09004802e800520154000e0b1001d00310002c685418560960002c100c3c0a1146c003043c1030603602c032241200c0d0301005403054002c645036005600094030b40781102c900d040d801200c50074505054610364800703190021080318810140441001000d075995607403a40 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 937233965 1250 937232715 937232717
    0x170730060612051605090f0901030302060105030727020f190306090f050601020c041d0f0a020117010608160e1305040501051e0a05041b031b06211a040f0207050c01 72
    0xb0003402c101d000c0098980384074201e181017100103e40c07412a130740c0703084241c822002c2c0504140c20f00e58407400d000f51112409d00406002c0c0c42030003800030b503402000110030115040b8000c4030b04200d00f114041c40180d40300c24a07005a805003444402074480c2c036151410745070001900c001801520b001c42000a49840e115403920080c1b82904106c0b00c0c0e6004a078040706100210740004142403050310342082c0340d04040700134559210380041d00410200029100c0e200900036242e140242c40300780044890700f03c0900030300d07000031094004114030300c42001c803030080107426042c03014030380740250b001c58800d5800c21261030740542c40d4001c0c481440710a22070b0701d8121240c4100344c81a40003200c6203102444000d01881c1c0c00c1580e610010b0240154404d0320000301e6164005c0c00700c45035490404d10704d10000b44a08440c2da2005500c00560580924001c6c0400110111058508081d03040c80e2002401c0c1b850040d001c05c2005420504a9661481195110480083c0058031803500b802c001d803030840c007010b15034 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 937235215 1250 937233965 937233971
    0x131109070c2f0a0e130303111204060b0306060a1503141f0602030408030f03041109160f031803120f020c03130b0304020a030f0501020403170307020607170730060612 73
    0x100162582c02481c0d54401c140d180500e405c000d00d480c0850082c889003c216000b54030105070030100920200c40a0300070303800303220103021456040f420545caa8074142e03002036110344005020049052138a8040b2454120f900f03001412065681194000d040122000710740404080841c44a1749140b540602c0540002c0c401141400c1c10a50100d94074800c0505000d0b0a0030040001020420358103060402074001030426000c60600c5981680768034130303410300080404c491403030b4280401d1080c4a031030311840c00c88884886140c0070391000e076560300e6080200d036860364032040b950000901e07600040840318040c00045644082c00c10b4000c148214a420440f4011010428400540d0b500c0110b40b00340ca41054076201500c813289404c5009105075070004120201c505810b5203003221410246101e500706409480c1103648020741211b545448a00514031000c0341c6003c244250f10822900f080d084050f5034203040700141031005042c28160002c10b40455803650028042280e00156520340b088c1021014 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 937236465 1250 937235215 937235219
    0x230105040305030a0e0a150203061c030203090607050309090f011502031315212901080705090d170408070f060912021c06050a05131109070c2f0a 64
    0x50452102901d070141658071070725410b1501c0300c04c1c854903034007c1d8001e0015680a040601c200040c0d042124542d10800d81c1c0382400b0030108400058000c0c02e64540c0c05585821005810054a03030030100007a0b9071440284400245ea0303c0e24400140a1041d5006100c01e41d0300d004200c69403800079600d50001c40d00240081001e0301110348402081e5007401420419801340c803001290010101c02d03020f042d41c211401c0c081d0f1080c1107544000c00c50704d1540d1a454014440859054440b06044416030004001e800092010303445030000d0325081c00000c08441c1460030075156904000319404c40d498038080002803c01c900310742045a80c00402507184030686e400c1c98400c2c00b82c005481889844030702c940100d80300045598502080307061003e000d00c40045c0682909182004020460f040c1040c14a0503010400c0244034181141d011980002d0b600102826402803020786900a0260414000350401c04000916446002d03c050030f013100160b080002e040d0409480000900502070045a510b401 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 937237715 1250 937236465 937236467
    0x12050f0c010605091008210c0601141e0105120402040b0d030201050603070e060102030d0c05120406020d0b010509061803010b10050a02070b0a09260d0c020109090203010b090904050109050a2301050403 88
    0x1ca01e001d13507459500e400a0f28001f0b16000c541d4850060b8000301400f580d0000b207040181900c3c9500d20401c20b5903d000083c1c4000d0701c6080d51866102494042901071007130946003101c0302e4040782c0c02840038102082e0328404202107000307c44403460460240c3d44480c2048080c0c01c0c01c02c0f0384070003002d80300da00398590304107540042c2d00c034498078440b00c40003a10740c003d41e982e4a000720102c90103800c13a4080c00d0b02e14074140c2040002904551403046415080c25031b1102b15610810a5606480d401443c580c541404c190f1f03c28a49a01c003180aa055500e0b04298001039982039a03d5002e18100e03160143c0c1c542e50880001c1c1401016001803c40c9181404a0140b142e80004440b081d10307000031001d034503030048041a01d02503e461065034074078441c0c2500100f00e0343e032018103ca01c0074401e03200d9011158488004109900090054407000c034002c2c400081d091030890000d0360440e000300c0c000a20700400740c64040c20041050b03401e540106645444000300403444000c00e80014000008000d1810140d170 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 937238965 1250 937237715 937237723
    0x60f25020607290708190e0304091808030403050c15091504031e050406020c0a140f190308090a08010b0f0f060d02030f0a050601090308040312050f0c010605091008 72
    0x2e8900550103000d2441103a0040b0f2046844468400c0c08035545002c1800602020f02200c0d007640e4000e040102c0c003403c1c0000d001e02d07028100b440c1c1c0550305003400e2001c04070007001c046004041000442e0798401c0441d40358402540030382c1c02503440781c4d0341c0d407078000c0388074501352030390356581a882440c2c2d040010144c004141c0744c100ba00141781e540b5064580341012600720785182c513a5040c04403014103002d07006030840000c104843c030503001d85600030004807c01140d2281d030310440e29041c400d4240806203150480d810408844001d12910384940030b09400040c1d41d045400032101c0b401c000890300c04514202903010010903a24009124091104000c10041c9072a2030046004030402041003070b4580e1028180c40507000700c0c00045460f86040c00610030081e106907900c035004d44c9010040f8a26500c1250180240ca811480780d07890715181d60340b0301d2454542c448580003004010b0004d046101400001041010a9400086005400c003410080049805003140014600d101c0081003201c001107 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 937240215 1250 937238965 937238977
    0x20a08070b0a0825020c0a0f0e040b100e0c09040f05070507060e120a1d0a0f03030509011b03030b13181410020703020f100603080301050607050c060f250206 69
    0xc507101c80302d600c5030480070350130400385203880103001c40f0405205021540010b01c20b040c408200d0300390280e141c0d40d01e100704d001e2505029055200d012240010040b5800f03000d61030308001118002c02c0f003544e44028004840e507055513a030400031000140f660051030240034180f8222a000c6080050782440c2501806910400300d009208988400c48080c1d40c0d801809898a00400c0c20001591807410314402000c019103403140d200a00c2c01f50320701100300d0400c50206000c2d50407660324808154210b45064070aa041000000c0c100007204055001640250aa58074824401d40700803d03c0c0d1b40c00410007544881d003c41c2c150100c3c2c50903250028510f000555441c0c410340050404026012001c441360500c4244a0000451400060310004059000488031401160302c0191052060400c400d042556044d12010f088814280010b0000345024002030144900c80c0d070803600d286540c2004650a5048070240d600d9640300402c8030523542100800d070101d01140c90250307000b00c0d0b04a50000c0d003203001da0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 937241465 1250 937240215 937240217
    0x1502030c040303120902190306150302030c0118030f141e1906061211120a030518060702041406010f02030910080402061201030804030210080402180c070c090504020a08070b0a 77
    0x1c1013400e50380c0301403940801c0c3c1d0f0340d0700038001c400c1e0750541c0c001521500706548000c0711410b1030001c0320340f8015044140340050b030768024060703c4080b00382030045403c081407130441c2e02e0380d00640b0301c0000061100b032216590b15104030421925011840425810500b180c1e00c00300d415440c0c5042000010000b180d00c1d568440c0624034400101c6690070a50010b15494100b8041001801524801d0112140054030300c0b01003141c00d50f014410a00301c85da00d801d28841c00030003081003886944403280105150b111841406040541410135035000502030785d030456101c8109030520030901c217155034440d85169403100390b03000562400391100003054041c6a4062a4020031091001080466aa6800701c0b20303c02040c007540e5242c2c2d6124100981e5907802803104a100d05241d03058281d889024101c99842980c008200c1900c003030045107040d8100c280203103038403060101080084c0020303040ca0504000307820801000205031030644140254200150840030300b035031010030304002804803c0201c80c094485 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 937242715 1250 937241465 937241477
    0x7240c081602070e0933041217131103070503030d0b041e0c02010b0109050306070f05090627010201060b03070e010c2018090705041104090c0203071502030c040303 72
    0x700ea10120700b00f154903040011307000c0b9040188070034180c0015249030000b00021080c0c0511003000c2203100c4200c02400c060a544581c0000203010404000f01150300c0302507030401c0000c004054800c60b8026504644e0b420361031100f40c540400b030150542410840c42e005600401980c0d003031800080d643d0041c0e0300c0a54010391107455000040e19250012002d0890307814a1001e00c00d40b04034800050901544208010740ca0894005625072082d04036008541000d805040300f41c440b1801120003041528280007400b40030000c1000721749840300105019208100e08019000f224082c0c08803c442481c03001d81103a050070303014065040740504494104006040014003910703904016114000c8840c03018100034034402e03e0000d042d005408200704060101c1c1c0080310f80c80c5a40400f042c03080140da80005aa018031028801c90a1035441040000409010f05007007917a6209902c060303803031003004800140c102044200400141005003800fa509a58042d400c0d8038010405070118003844c0701c06020002c2c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 937243965 1250 937242715 937242751
    0xa03080d11210a110c03041404050105010f050c1e01020702090f1635010510092913090902100201020a080403051c050a0e0c0a0e01030204150b07240c08 67
    0x80c5540c01078400d03c04c803034001d549806400c1402502d90300140b0500111118a40d00041c0910307003481024142c0d64142c640601c040d441d0b990031101a0402c0c929a14039100380c01d400c00000800800403803549407c2c1e400543e88201c0c0c2c0c41403204825014056040c513000f800140b0030754503810320011284403002d152024038584122641c070400c07180c25114440d01500c6c0341030341c241503440243c402d060f07600554000030400b0342048100e981d41a1441012107512000702d00c00f49844c447c400c0c000301c40342406001030038600d4141000c11003000903842100d0607903443d0b04c030400f1400c040c030401d000d101403030008500780035041a015045040003800281004800204004900da15a41a120944542e8000c01c211315003001220020183d8060383d070924031401d0100380d02858500031080c1aa043d031502d181b0142d01c1d550a21020300411a99502207218504010070355402c9080903202c0c0c1d900a121074001c00e4260f2520b0085403041c298074010715814400095546500440d055030017006550450a80761 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 937245215 1250 937243965 937243981
    0x4110607050703150f0b104a040c140a0f050f0307030617120f0c03040816030204050a090f1112070e1b0307090303050a09050a03080d1121 61
    0x404503410090260361565905103200d405948240e034660340005c1c040040ca00e0b04810080180040f03885180081d5600c041a0203a807401146900304141c0d4040451152129649000b0380e9011182000c100300f5000415a01d20320b002e0099015940035420f1503c00c02c20341100012040c441c0c0440a001c4c000036840882842d17100350f00b2205ca003403480007400e8a074109207000038003600c180d109020328204034507114400b80401085440c6e11004c0e40e9241441c15440c100c0f480ca4035003042c00141c140d40014080040d00007010300050004401049070750075181e085204000c02c44001603d00b804c030516006480000a61000c04441455001002c60076a2104070001519080b40141da480c40c1e4000e2020008051000300405402403c00207080c0e54034403a80c180c003d2040c0000c640381c0c00000d4048904001007030041c0c00070081d0241510b0b00e00c0e0b400f515040401c1001d00035138001c4880e1240000c218140d400c441c0301c0c142403c101c40b92142c0c685001662040e0355804290b031424200500c00e0b002c00c01070 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 937246465 1250 937245215 937245223
    0x70e041a13140a020306011707030209150613060801080706090b031b0f0c0c030a0b010e130503180111060402010203040b0f040e040b04050f010c050f0715061503140411060705 77
    0x255910403650111104180b41981d143c085840c0c04900078031840001040070ba210010007080000910010803d0602d5602006417905004e040701081c1d40c40040003800e00c1e01e462009094501c41101003158040c5450401407417420142d0010b002c50f000400305000c07580d4481c0002d01280d13088005c203900e03512410040b1088a1441c1075000080c000052541043d524000141060340303648026900c0c1c80314131800703045e100c03c1301c88030003000c041109005101c0788142d0ba0f071075508940d03200e2800416480b50381d101451941303d215240240450f035100d8014960b485a4144000302100014040380d050581c0040e659000303038000c141d142c481c00f081c01c808130b40c544410344000b048849000903442c100b5042100c80003900b921709403542e0080400c18850b161050160100d503100543d0303110f00e130030440d8050803129007000000300d44080620207095480401c40c02800081c08080200c2c00c0c0000c1d0b08c40025085505547d00792001d808510100400700d410081c1d513040040c030590311b81c5c3d40c070707501840c2c80740c10 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 937247715 1250 937246465 937246501
    0x6020706051209190323040e07050c160602010b0906041a0f03010b060409050402010e09040c03080313060e10240302150f03191505130b0111120c070e041a 68
    0x1010200f04010145a8031580c805812200d03071040c0c1040d460302c46c2501c103a910450160116060f078840c00305400912070002056503603140c00c1514054450401c110020440507444000142c3d1207511641462a020284c20740003001102c0802c11070414035040c5400078904450305e8403540e07500c9075010b4039803403e4008000703080005001c181c0e103d4032031825034003c01c402d030b03400d900150000700d00d50014201922050b002e20340000000980914550718144103030300c01000c006032094045005c400281c0ea90044440070245140035200c03e0145020380d60454003400030f0b19201d10404500003100c50603e007a1300007503c1d0141c4403203004d10343d80d1100302c40500c907a0031851142000081003100d50102311745c088001d0684203005005110ba080785000905080d40100c5070301400e4822807407980d00c561340c080c440c03200c41814160340e84800b240c252810803120700000413140b040007645911601052202d00c019088444607003805040075152200203031040c4400000c2c1c03810900102e003505002842c3d10035 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 937248965 1250 937247715 937247743
    0xc030e010c1b0b12010b040e13030c1202030c0f070510080a020403080307020a061a06030a09060b0405090c01030506180f0a060f092306150703050c19030906020706051209 75
    0x31402e40d8807a00000c5a52040d030110403001600d100100d01e80c0c006400310341c1107400700c09070007245031141c401c0c3c1d101d045542c8000b2001d110360341840400003020400f02d160325648540244d0f444135022240d03582441003401008010790464403040c40f150781c50702c013003004442440c0b801c03041c10fa0f0340304c46540007403091b074102074041c04000c81080030301c6500061118900c2d2141c4810310030341010041c2c4884c00c1181028103a4811000c0c000100c844c002903000c0035079140203200100c0e516100101007012284140c545140725005480381d8103940d600f5001c0c00c0d0700040c007643d070201d00d12680e07400030021070350140801c09004c2e00d13a0080303120b07900d03187c20900c05402c10301e0520354003560f00c0071901d0003000300302e400010010403110507907000040c0f03406861281a0141c8900c00d5600620b10540c00d40d8004001141400004e000403550280e0420014018065858803000d560601d414040c1c081c1016620070002c550101c4400e10120f40e101081d139009010018102119032107a580781414000d021500315 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 937250215 1250 937248965 937249013
    0x120e1b0301180b16030c020705010f020102070204060f050a0f0b031807030c1508150307030206130f090f14041502031b0d0615031a0d050c090103140c010c030e010c 72
    0x1030922411002c500d0044c416450304030402a40b00d401941958a240c07401000b581101e40200807079402100c442d0000300d15840010b140c000c0030750001d0b0031510940c10030501200c1860b024062070030841e4461019020760041d40071287c0c54a409064544001001e44110720480300c00341e07090783c104010440c051035100f06407004181d2181c40501e2002001c40d00100020000d2011494880c2684c0180408000140190004a045409000041e0301610007052018000c140000300514540200c101501b45c045021552a07030401840d4159582500c5541030650003c00b84800550180e11240700503002550258907076a88060001101d907540300c040401540000305000c83c41910381c070a1051f207402c940d400340d201d008807004900300c503001d034004d034201c0c03214840452032490182c4000c07054a100300202e41d03d00341c045001c035885072030a80c02100e4001c0341d50340080b81241d080c041e81c0410b100c20b182940740100940c90080084201d44215410700425103003400c1407103203044141d9a1026144e8010b = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 937251465 1250 937250215 937250261
    0x1e0316020a050d11191223101b1b11040906020c100501210605090106090908040923061e100e011e081b16030c03120e1b0301 55
    0x30030f03503244c0302c030104a204401400803540865582003060341651014522450310664680c0c1c0c0d80c0440c004a207102d410880700e1031311041e690000700482800100c04440100e500c1040301440104040300905000a0160b8041039141e00004804081801500500003200801405020900030010b0b50b0700030700924000194103940c5100050000c041d17010410301003203141c3c0e0354906c1c00003a1583c01c0d4110b090001041c400d0300400c9032500034a80003402d1340000602a80e468101c00211410b60900311a00d20000c1010029102c0c13034070030ba00d02c4001d4942003038442c8000e60300d6544120401417005121380b140902c0081a090000250088014050200803200d0f11540e4041d080500c03000560703001900e2101c40d00b00b4181500080d24190a80341c4582c003a80d100c84803411102b080210020007202400e2040001c04481c5050440d8648e000e9200d007070040b04142001001342e90300540b084881800c102c2225000c94002510b0b40f41034000c0403e08090303104520009014007003511840c008140c1c00300c00 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 937252715 1250 937251465 937251473
    0x14071509110f090c09011805041503020111030c0705100e220b03010216060c02190b070e030105040203070311040b040e03090406080d050d0506060702211e0316020a050d 74
    0x70294503100c111100450400c0c10b00800203143c004a07202e20000702d0601c141031095004040d004120142c00d00610040d6455101040443d501003186c2000606003601c1002996045201d60a800b840750014500d001e140c00d28043c2c2d1a8240d11440d4001c1e151b044042031401d200f1000351980c00740043c071300280c04080c07074010031055071402c180042c00e03071808280b00d405150501c211402c081e800c0720980c0c038540641e03d6510007800b038565200c2c00e600401070340c12504a80e10241c0a40c16114a00094070350a040310000d01c11815424000c1c041e0f0714240c00d20016a030002441411240c0c031581c100490055940401d003e48540d9218036042400c203034544c03c10b01404000303400510019101000000e40c0c483c496540c500b5455483e00120300200301c02103c50419400c4564054000340040b49010559400300c5e084486000039144100e4440d100010206018820703115607043d41c0b54404213034409000f00135100c8c0308031280f101d410f0103134540e00c508549442da0360300001c002c01804030603945072900b0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 937253965 1250 937252715 937252733
    0x615270f0a0f0902010c0602031008060f100906120f030909020a0c021008040c230603090c03070e101403010603060e1b0411090d031101050114030c060a14071509 71
    0x95050300541040b50001c1d2242041c400c83c01c015070143c1d01c4400080060302d910009520251140165990100001c18050303c100300860040c80347d2184884c09140c842d1103204503c059410414803d0b040c2002048100d82c00b044441d503e58000e158200d0714206c924080e155005564000854140003243c0b03508095000481680030500a8410f00041c0b0040306c0e0480e2a490115801010030340c2042040c0800c03800c0603c00c01c03480c40100010310b224240380c0001010340c2c00440e007010f190340c03101e405941507040c24040040240820800030109060580112580800300d001d2120b0b4107104149400c0260b41c2504110300940d00b0503002c0110648541e05a9115010a0003440140400209004003800c0500c60346509403080a1782070b003041541020081c1402c281541602008001000645003a1082c41441d00a0520140140243d0f40b400e05041c140f82144d1180c2c1e11a080170700000e804290405590340000001c16515a9120100c1c0b07080440d646a06201d0f065452a0800342020043c0100d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 937255215 1250 937253965 937253971
    0x203070f06030e0636160312090b1918080109120906090540180f0308040203120a0503070e0607030903060b010e040f0515030615270f 59
    0x150301400700c0d06101e40082d6951303405507110103001d0f0b180c421240203000d4041d100103811461008616500c041c44442500d0824030304882000b03021852420010015080540c10000d01c181c1082d2802c1858a01605103e010f06200c5180170007010b42c010015030b220b600e030344900c244080c04680c64280c0300c000882c02400d184034116100072040721011081c5015010303800407140c041da2440300450030801408011200c1c02041d4402924580200c0c1c6140c00d5807130260800c00b442c801c00c901c1000c28048100544030710080c415058803682d9074080115103d80c076640b40d000c2c0c05081843c9291290700c00f180c6000c02e0a00c1080301800042502d10703d641e0b001c0d0056001d4080755448801c4140460304100151140314002400701d003022904000040043e0021202242d050610702d11070709000c004101940c0e481814803d0440e40d4000b003250100011100444502c001e90042a041c5010381e5401c6c03400d1404141d2920071211041208103082d451144103010340d240c4001e142071030a1100c01d244603240e0035 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 937256465 1250 937255215 937255217
    0x6040f0207082a032703300405010e04090512032401170414070b0d0f15080d030f0f090516050402031017010b030109051005090303060a090c0c0203070f06 68
    0xe01002040d40c2910a0581c0ba0940c290004d0341c542007414102e003020b8074000384c4107901012400c8460f40c0035074040c005248007074003800c18043e003042a4801d64180c060b25031151903410394244028007060341d200e00414112907042d580001c00c452942011480e0425809a0649403140003041140042c0c0c1c0108003050400580503558121010200549582454020105000c030410f0001004600d144130705111224052056074541c0b0340f40ca4107a0741d2a40700000ca80d8040b41c59440c0f4540c0100d103840b5204000407800380400d031507402c00074140d80780c0c03985591080800d030300cbd005200070a142d10740c01440801c2445208221608031441d02e1501c840d044c60780da910469110500003401d007800e000710b9120340c4406d0201c001407800c0c001d90401c50b4000800311901ca40d42c801d1500c105031424454030303010038003440c01421491031010165040e101c000b468007010790400d105010560304c40550305020380b8441600420070f443c4e100d400b143e1154010754040e5041c0304040c03000401c2d4400c000048140c0e50300d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 937257715 1250 937256465 937256497
    0x71515061133090a030c0201050706060513020715090503040312140331020a120f02030106170d11101e0507030e010f05130b040f050111030601110d0e0906040f020708 73
    0x3c0724045922003641820160104c4c2400b00d10300010340c03080d0020300015115400c0003c0803030300c034008104010914142c500d034199001401070f00f4040c06d055664980d507500130003800400f003d0f507501031702c034052880300401c4c00c20549814809035001d9150694503220452800c2c2c1c8a2412910014420305200c3c404980e01c45045c0100c04220444481680c505402510b8403881c00c0c80c3c2540410404000001030f10b80380c00c101e00100041c1e82c207001c0e103070081000d0125944107110407080507003440c41042c020014480c1121404c00081404540001019000e90001440d00c000a0189000d200e00c80a030100359031415003040a07558140d800b074036070444207100801c1900d540090316021181c003500c0071000144004410400100c005c0041503005c1d06c00c490301030804801da6180303401d60b240c101c503d2000c104017104008480d644076208030301d4810004018045500030b00c101404003210174400340d000716050400202030380c40340c1d009100309000241c011507507034a003410548241d0300041044100c00324 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 937258965 1250 937257715 937257721
    0xe070e01060e0a0b0903010905160501021c0903060209010c0f0b010f05010306180209011e020c0f2d040b030a03081b071e0201020c1005071515061133 66
    0x1c421007212040c11409040340f4001414030141c0f190366085020f80a5266483d00020b00008130706001e220401501c600040c010141800000380c00e00c0c07400b04000181c06030748080070503410b80c0312240303004513604404d005980b03981c14401241e49401c132074406881420006c04c0d01c0c0801210a050b1412220403020702c1c0003a54aa100440075038200f8800c41c22580e80040c1d8040144445500a2101c0c500c141880440c070842100d0b244501a51464940056000b5500000ca42d040c000d000046031402200c501c0d01b001002200500212070002c4d0121013107500b41c115500c10780300e9034031a05560000600b103401e05d03412868010042081280c41e9000d6000c25003030030203103207a100251840250b1000b4612218007104481000729200d41c80140e045219094040c2003585034110703540c4c02c0d00d0455568987e9142242401d45102003840414069589000050441d1128400440d019200c0e2813410300c80440c6507119035403414444100048441030321070360b444800501c0960f4400c620b410340b101071314155 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 937260215 1250 937258965 937258967
    0x14010b07030f051c3603021212010608090709060f060207050d050606060315040f06090c021b060706140108061b030601020c090c070b090c031005040c05220e070e0106 73
    0x1000b0340e0101141c804a8510552080c00c00740c12081c055809514281444802e1115800c041c50f17000c50315034500e00043c003c0c0c0e03050540c18440314000c20212001c072032a250a000c0307400c0c402c2c08144202c104018046000c142c11000c14030400c0b0080890150502c4400d440e032000344202c016038480d41c4098031078200d0000d1141801c13205060000e8002c0083d29150341d40e40c0600516900c01007664900b40d60725000c40d12130755564419800744c2001010005004c0e814208100e0807070300c8030340d03480040d580a525070203204e04030312411404580040d20456100c010f00e02c0c0034400741c1051002481800b002078000304d04900005440c41c0300d001341c12403807220780d101c1c0100d05003076101c02c1d1600d40c01030300803c0d81c05540d0b04008580d10780200c4502101480e021558580700c3c18540306951603003a50300140070088951908001e5648036011651040216081c03e680b0001d28582ca48600b0b806003448448075010341c503114611010300b0728245020b002407194861a0f5031124401d000ba400d0341003100002041c41c03 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 937261465 1250 937260215 937260217
    0x12091121010b150315060d060303020102071a0609011701020904090f0b18030a08130b07080f10060c0209060301090b130516061d0f060d020d0c020c0102030a0804050114010b07030f05 80
    0x3a4032280a9a245460380300c0d1045e40344001035242c640104041014007039244992261000460080d400140c82e5816444d05042c0b80ea03016082c000c06442c28010b00c241da6444414003411500300703207aa82c80545180e4a0540a800b9a0561940c00b40c540044d03081840b0151007020840703031283c00c800449603507a00301c403000d120101038031025030340c03080c407640c04264092040207822403074180c0b10404010307940d0359074411800300300c0e902c000088280c4240a8030444a000080c0c02040c0004c80d81c01d801d0170484011710781c04201c070000c1c3c4a01d580b100498002d440130f5000303400306504010058414603000f8400c940f102d00c004800c5410784500400012030503016540f4405070b1b079290340d8058015403c090305001400301008203070760102d0710344662003070743d5180c40040c83c100e60319100268a038030869003400300300c42e5030101000954001c99030038000e0760780c080115031000d002400c00c1142d90715070b81481401006403440c00c4c0480079105001141c4070400e0005002000c1c030958548081c4020400201d0795 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 937262715 1250 937261465 937261489
    0x1005060121061815141c060e0115050105120402150a081504022503030f061401021504020a03081e030a020d0e0a023303150310020a12091121010b 64
    0x40b1302001d1600b8000003080396035035000b9101c002d000c44084036404000d140c5154909001701d0394966242c4d640e46043d00d0078069000300610600144108d41d1030040060030034820341500508800f020790003d0112356452903154182168200307e15150001c080000d0f040300c13416a000c01c0c0100c030031203e00c9040e00d00750003111103501419620b042d220014103440c080741030b007002d0100c091640f103548090159003a44140c40c028081390f8804180d08c02074500181c10901e0540c0c481c1c010254102c20080540c031411440c10840b5402003055513601150348800359030000045500178414000001d0109402558024001a801100003084070385a622041a030311000c5000007504103410010400080c41140d8480100d03a90740c062500c144405d40d410015603030301c1103a90210348506078808003414182000358a42c14403c0003011460314048250140081c00c040c02d50b41c88454a0f8400d9008002c40d10100c103085002c017419a00000c0c144120781d201c02c7d0807494000d046503107081203480c424507240f400c03118 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 937263965 1250 937262715 937262741
    0x1315031515090e1b031e011a010c05060f1017030307090b0721200304151d130905033601080406020903010905030c03031608070210050601210618 64
    0x204a04514000d5581d032112201d991745401030b200901d40109450321040048100d40c40006414403c04d6051100101c50000c881d0402480d01c00074170000d01c000440c43c1e042581d001030720b901ca55507031095000b114519040400161789802c821424941c00001075409646140c4402e122a030b1107080c0000e0b00d0140c0500070301030280e03041008145940c000c2c50b41541c901d10b0725044620103849251000600707442c141e600e906a10002e000c01c0811003e0341c0041113400e4074a13194488030002e2544d1024581c145075080e01c100305404451200f40da9a0380100740d5903610400f902e4640810360090000d01c0c0181c5204240700c2c040310902114001d0441500b400701c04140c540c0d10b0507407030300e46516000b034001044c0103802d0766856283e68045981000a000001c6400e002035551b85080c240421038100c2603140281030000b40c200740507290742c000c2801107440506520005165071070a00403aa08079078030241912000109010041d209843d8009000755100d410840c1400340030800c8000454103400c00031b41c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 937265215 1250 937263965 937263973
    0x103020d1106040315110a1d0f121b01050403030815060d050901020712030501120303020309190819030b0901030201181701090b0906100314011b1706010804021315031515090e 77
    0x40981c83d22304681c00d1200740c0074002054403003540c4042005040c01d0702c0407265551259259840e064040c402c441c030080401e20f00142810b04d160340141c034103200604030b1844400d19841c142c25940ba43e0040d0340d4500e6260708188128142000d850f8002d40c040481070f035101402d0206406641d019001d5241240e4882c0c2450540019548040b0029000600200424000c01001c0522105658001303078549014034a800d540d5031290020071401c140c010f10310000d160520562280f1540c038a04103904403502800e0410108100710719164040f8184e40242000442f0708401300a8040b056010381022031040342c02081c0b6440300d41060342d460008840054443d004501d0600c00500c03440c0c421120320074080300100301d91509100c06000c003140111100d000504000c40b01010701c00d008130303280e000813080c2000d2081d81050b401046c06010458180500f990f00d460303030301c07a1680c08083d600b4015604601d92404e803002c1d0707030001c201600480010114003002c080e80810040340c5481074002a2a0090042c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 937266465 1250 937265215 937265237
    0x10c26040308070e06071a010e010905060a03080702060c12090301060602031c0905031c05040b0a020a080c0903070305030f0711060406020307110109090f0905060702030a080103020d1106040315110a 87
    0x40300c4014501c4c10103034100320280161000214080066500701ca503010300c410f02036040050354445084168014102503041009004940d1200c0c8400019260000070717061307841d05503002248041c481e26030402058031499404542030300b45c61020303240c034200880013070140703583d1103008036500e0140700c1e40d40b4011f1201032010400114540c1c0642c00702d521490907a400c03c401d02c0040c0019290300b0a400d183c2c180c9800070481000b4001c4c0c1c0040d80314040b00c81c02c5040042c07072100102402d0f00141100b210340070003d1140420360b0200f03c0c1000a40e0310600b181d40d43c06c500d8250055603040814226803a00e004d10078890306103000d909540c1960201d900850400480e40c032890340341241d981106c0d0600c40014008250498980075404c10340c49003200102c1d40402c00d203002454000c000f4800000c64000340f010f9940c0d1a805903015045a404880c1117150015030304042c0a05848642d000d40d003c80002400010460f0042c0c10110100100000300003403400c0440015071845000040b800151045501c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 937267715 1250 937266465 937266467
    0xe07030e0c0f0301060b041509091109130e1b040513150f0216030c0201020c01030c1704080d0c020604030206070f05030f280f060b040b1605010b03010c2604030807 72
    0x2582ca040d8002000403030303e950707141d600c0c001c01e0340141c04c2241041c64180e46501803a4100004000500c080a020464920300b1002452140586000c4503c546140d00100c1024982d60f00701a00c000b54180543e804501d000c0c450344071800301150180d000c1d904000004800e0039000105c030140c5500000001240e0101ea0304400081020302c2e0f08114042d400d125101c94607004da150003155610a80707925070403a042e80006490102c00480f41810941003211000c0c90ba07500006500300040c3c8400310040b82d0b1124038042e1824006d8020b150741003031515030540d103001e50004115003e14000c0d000c0d0f603500e84854104987c01003801d90b101010500c2000810304400c1140c00702c540c401d2a40c0c03401505000200781e0082400d9105003068900750719101c40351a07040c2203101e188000c0041c145100d140910341102d0500c64014244040d041c03020f8038250380b041c45000e401803070a00d60f00900800501101d01c00140020b0800d89070420b00070381320000707030201e0790090013002d00507a0551034001d100d80e604c40c0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 937268965 1250 937267715 937267729
    0xa0209180a06090809031501050f040905032110080d08070c1407090606030e010e070504092414090c0f04050709080601090c080601020a08070b061210060e07030e0c 72
    0x104410314400c03a204140880c40d02c1c071445024070710500c03009039144811403c0510306055071018003900d41c4c509004218a039501038000721141c400b0f81c1c000c5955007041c01d00d40d0850158000c400742da550450440c24050b40307040c04280c4101024083d141960b0f443d000c203295101d80c0380c3d80c118080b45148001c1030b84240100c3c0075200403031040180341d1408904c42c0c0020304144499009003d801c0d2110403e002c00c80d0140180d00c0348640e0f840081002d000443c00043e5100024810b00740120ba0300d052902c14083c51002c101c0b20040d45882021800740d90011200c020a00015041103000c14800450901d11020a04d00d1142100070001c081c00c2240c10204030013814042e20070010b10080e0b140c006848901070151a00a025071200040c04d50380b8150003400141c030052074141150000c0c40210300180d5410140e5805c50380110004450365a454089586044081007160940c4103031a058400211315070020b000750303507240040c40c90a4581d0481030b010b5130580112400c1d10b421039000b20106040c401 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 937270215 1250 937268965 937269001
    0x31c060f0e13061b020f0106090b010e0d030203091f0212030c191e050d0e0f030d0c0207180507021b0616060b06040608040c060507080f07030306051e0a05030a0209 72
    0x1000a1100301250800b501c600d8080c01035800358018541c000d1b440f000a124440081c940c12030306220240800c00020304000e480560144100014862801854400c00560f48170040242000c00316613112401c1d0380e07101e80c1d07580c40031005100d0514a254041c070001c0543c1d01540e14001541d00304110111071a8110b1200d0f01000b003000826492401ea14802103881c000e007a50644540d6a0360010511070825107181480020b5036501409400458440000446904090000c00001d40c400406d9040b03080c501180c0c040c1c49500010080143e80e070030194012800f410b041e03002c45503960185042d1621308140c82d1007007580214140400c620041030f44070850111403060000040c04140c0300005103154002d90011800074070b01008000411407101c0c031a4018000d00d00304182460140e6651100134446c89d251040b459502281c114201800fa0704424054100140613601d002c42c43c0c80d07641b100c5c001140441c2d102e50514940020181030200e0700f40461742c1c024002e03411130b958940d00701200380d10350 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 937271465 1250 937270215 937270223
    0x3020601080d1b030e0f060a051c020c0d050d06081e1507090b070213060b1201080a020a140117010915051906031e05151e011e0203040305031c060f0e13 67
    0x1b8901c41d2015070b5036400804003500c00791103003503e808890026149007140c8074a0712200610410800e400101c00080e8803036405000d00d0b0899488113403081c001c4c0903000726488146280b00d60301410b044060010f200e03070b001c0600748040300e40403090131002c001c030401e0170359820300803508403603080c400c68500b00d00810350b040c00504642034a1400014a400b00d03071031503000c12034604002ca107074644600364441d4103004149000043c402810300790000f440c81c1086100e03003d05050703030394040f40d5164082c0304400d20180300744454020706e694070024407003c1c0886d041c28102c034440c080000300d924601040f104080761078081480c3e10103818004141d0050142e4100e2160050f04020b409038150080c0c000c5503c107420190b401e130052080324091102d12481c01e01d5802044141314900d8500c1c2e60f02c14040750b040a03400d20300502028030001e042e0704600c40ca800290803404005980000190900c0740d6480307404103031108000c0d27150713101c4105403240113501914541840042c049140d29032071160320002e69002e = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 937272715 1250 937271465 937271479
    0x14401030b0f0906060d081e1305011b15050a111605120f2d070507050a0905191121010302090c030f241e01030b0f06070212071203020601080d1b030e 66
    0x3030032300c2108058100400c0ca0301c51140b600414429944d1200301091211480500c0b261135491030340d92440aa40c603800345000103035039040050200c00c0c0070f40040080b140c002d00c43c0c0707a50f181c44280610400d10040030942e5180701e0030102c081e56003250400c9844400c4501e06a50500d12101c0210081e04509078000010700d003968a0310750795a1040b00103102e101d11071401000349615140902c40e80c03d21917801440d409281c542008850401c0580e80440740761a0b02c400036001920340d4500c4818011072102008200c0314002620303a00640d0905603050380e008498000711961024001f84003484200c801c2c61110420700045844488401d24419200078542808030f1100821004642e45030042c00203c0c0c103031042260761150725601481018001107065030802c2130903200034046407e41c85031000c000d024100d10114203a1411060241402924104650404074442800c00960b00c0e803081c0943c07840d0303010700e000124015000790000d0301095002c8605c510055410786080c1d5485c250f01c3e090981001c0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 937273965 1250 937272715 937272757
    0x40e1006050414090907080304150e0d080d091b0b0703140310052707080f0711060105010c060e061602060f01150c050a050f0d020705014401030b0f0906060d08 70
    0xa808d10103030020780741012881503481150b0000030503900c2114003017130065494150fa0b5000c50f48800454124450035040461000650303d81002100c00480c0345851213201c8480114900381c019004102440c0280d56001500400c52040d445601c42030300c11340464184d00c4010030482c1015406044508032051400110002c10030900444c00021908039000070742000c1040410000b0b044c1d0a50070500500d0080034074251a804103983c0c0c40306018050500a005150408001060301b10b9015480b4550640b00c13142460920448102c0030701e469800513000ea00002103031104030000d541d04869a4040407415440426025607400050002c165130a018000544000c039104118407003205003a40001d0181e0222010000d0500d009074000d0350400441d1000208a4011842e8640c0d01107198a01c80040c2100c4001c08040b048070025801e40c0141642d0000050018a101c0d651050307680301045107840c1c3d0780b8050305450300301c200d610541c000c0028600d003002c1a01c070f00182545480406898420705 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 937275215 1250 937273965 937273979
    0x3a05040533130510111e0703020402161a040f020609011403070f0f170105120f0f0102030714040b0706151208030115320f040e1006050414090907 64
    0x1034400c0c2c12001011514031020449403c1204401c0e0440c00d00c0d240c0454984d60b1403c00c50f80756550414803000d080c0300802c42c000700080500402d401568010402c65407a007154180303494001c4200c0b000e175500c44031900c0c0c20200c2c50608010034483d66002642c440c203d0300c241d013080002c2c1c0107800c1e4203040103030340d6004480704900140114024200d0b0385401364802d09081c00180201c80c044841c00070041c0c0024420004014580400d054880803542c542c400d212081001d8a020100c95201a2501c1031014512800744190f000b5802a40c2c0c0765140446650052821300b41889036100f0f0640850007040380702c02044150380141c5482e00e0000d40900015070316580c01890301092030040d074149000000400c88900c41c514110809c1110f070805590030400d591b100c0c82e8000d02d42ca90364602840d44449248000e4102040701c40c800000c07000c0507281e540b60408809104000c81300880400b80104000c0380090041042c0e0f0115003248541c019468240401c2c400e10b81c1000d48005007a21a06901081b01 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 937276465 1250 937275215 937275217
    0x24120509010603080315030708010b0604050411090d030f0e180a050a09050609280c1505040306060e060f03011b11030721020d080906040308093a05040533 68
    0x105094804000004c6c01c60081600301801544400c3c0c16a141011540143d02d400f016141210700441b8006000c510b103150000c018415190b0361a44084c908684600305504040306140058180c2c4c1c40c011803a40b0764052050743d101209510011002c030100040000595030040c1e0350001e188440800c03080a1990340c039140c40300c1651415a030f41c210b000c00342c1058100d2030102d41000b508400065541602c5d4642c005104460300032071601170346103e144030716207004008980003503510400c00c1000c40c1c0d136480500c104103001e82d9041c0c40741e0540b191144036440e050080800504245071900100030010100350383c080d480b0280002c03107010030b00c0043d001c10720503907641b6141c8580104085446c9038180c002400d0420003a850010b1200751010710007100710014205030b109a15040141081e01c554508038942241d2501110503000360100c0c0310151740414529541e000411049035505800302003050300c0c103025501841c1c4d00801100030301000d1400100ca012001d03008541c11f0303800c02010784449055 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 937277715 1250 937276465 937276471
    0xf040b03180a0c1d040b1302030f0304080106050a1d0a0c0905030303160912030210090f0605150102010c030e03251218090c081528241205090106030803 67
    0x18083c0c15108000c2020a0b041c0c0500707441041c4030100341442d141e51040a80d580c0507000042c038809550782d020840d14200880025801325104481e1504d658881e41c074040e0016000b0540141c0c100706d000580854240741c052083c1248448000d202e5881c010541d004008080c152410040c0348100015141c03400c0c401940110010700c1600e01c1442c1d64180a000701400350302840c40039101c4070419010a07404143c1c94840340ca07a1101280c10320ba28100482c500c001150f01038451484e0005000c0700c0c5403600420a0050300030b030028010008441d005400300d4481e5180c0300e180d034204202994900c24130284c9400060303aa0700c4100c560706c3c21500d5404407035000c00e0300000828000c1c145a9180d0344c0400041c0018000c101040c00498036003c4028609107010b846500c100700d08900d03107a080d44d25a10001680032541c019034407841034100d080188602e1902ca8400b030f07100c460f40b0380d03200b0591a050004480c89603444242d0041d0041d10244010f11000f040742000c0d55031502d0220001d13241c2e0b401180 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 937278965 1250 937277715 937277723
    0x309150309010b030f0a12030204030b09061e0727090c1d19030b09010608061e0a050906130302120a0e0f0d031e050d020706060305120f040b03180a 65
    0x61a07261015600d400c480482d80c0d414030961241c80124100e010001d40038001030f901c105809003103c5c040d5000c0e0080d0103290001010071a4101c1003114120000030030034860116051170103150400c0365091680248140d461034001000c84035815500c419442c01000d0000260040038042a81d4076a40411103a00091201c000303400341c000000c0c100b610503070949840c00103e031115901d00c920344a0303101910141c40000c0494034004009540880294000f030000c184171015200380c0d2500070716412400c00c9044042c490100308002142d0240701c0d6100d240e110300ca03460000d001c02e4803260700b104e1044550b001308038118410320f800310140c1d841201c003500011895444880c42d41410504000450321a05840b50007220301584280129078400002c0c0103005021081d440748417048401240d1510030005200c2903070340006104400c200c050b50115045902610a0395840440040c41071700314400c804007203686d85010302092101c408060021504414551607880384401103149040c142400303450150303 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 937280215 1250 937278965 937278967
    0x7020d0605071106070f1d0a03121101061d060321070c06172a041d09060112020616050a03090306050a201809010806010918020d02010e03030915 64
    0x5140e6400c07444000307480f03039108081c00d85403070b1902c1c0040c2040d080c1c80344101041510504103c00050802810425032070190802a400781c0382e0802141c00e202501040c40006c0e1100781400c421107041c8507040941c4d40d041200c580380ca840030000005140003900b81c69060203a68031201c0409103a4245011503076007070780410345612580c1085080c400640d8008824441e04400030380a10302c0c0300c2505688219844e81591105d00140c1d03060380e00b080102c10001c034003800010007041161641404544000c400d2000c03a09a94485c200b040d20b4640a2085801031080d01c41c40c1401031429070041e040c0141e9a21700c004c0409500d0b05e40ca0b103401485201540855965842401805400c1c000d455019504000912500181040c44c10060301c0d1282c1c2d14000302e13008562a0400f024003004402c4a01d80100180110f5840d51011610742e01d0a125041c8510f1410311180003d05154101c1d1035400d400501042100b001a0010354030038105503032459250108005528403035aa480740144141004100703d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 937281465 1250 937280215 937280221
    0x2060a0504081519020a1e0302040b0c070306112d13090203060a14150f0d05010b12060405071e09080d032003011a0d0204180b09060108010b0301150507020d0605 71
    0x213485101410000c1402c0309004104034240c0135000180405005440c0b844500800c00d9454218024003898010b11888000003c0b014458003000602c1400c7da030081c44200724030000d80002400d01d00c110a100422003644210840f0014611020f184403148039802180c0307040085801d00c0705412450300945e0003a0342c044140402424104402c0c005051400f2070b194481004200145001030884802004440c0c0020701c85089a06001558040e0b0300c0a1424025561516220403880d00a442c1140030321703491000082d40c0380b8150203078500070181e030389800303844c200f002503240600e03541702c03801c02c0038000c80c00c900007500e11081103020180240c0d90380000f1400344d188010140140318240021410800b48010b10100070029821922251a1844940d40d17098210b0340101a008580c0150b0051580d1401c56503d480d0f15000540281002c0350781c640b441c0e1701d120040d100c0d04e100780129015a801400140049034000e6800b5441c01c0581c20400e00340310060307000030300600b5540021242d080c2c81d00c041c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 937282715 1250 937281465 937281481
    0x3051306120e0705090c090a030f030503090d140304080904201801020a050c0402221e170a030e031207080a020105071e1d04020c0105070207090b01090302060a05040815 74
    0x20b00c101e44804101812540d0301d0035001450240d009051007101000c00205004150b481c150311600841d4041d18100c102e08440c10081e10030341007140c40d84514094280203400113440313400201e0341410240d21032070564541d034446d80d1103a00882159508155900140c49044041000e80c0c501e0420b0300d254580e480c0c880e140f4412000101d403040d141554454810400000e80205070640c4040c401d0f1001a02c9804104424200035107110203420001014000070034420000758403280e07004420704a451040740d8900446040c01c140d8070303140380150055415440000e03c03800d103000c1811402011901d03404000f440e1854141c1c08000c003114542030003d021182e4680a008995120000303040c0000ca070600c48501d040c110f068039072001c04015983c80c0015001d2902d018260700d102c0050011515200031035007550007414162a101c01600c81c0c0341c000580d00030ba03402541400307030303042c0e40cac03a4003191440d0b09101c440d40100c2c08100c1440b00038000072502d003200700003410b40580104140402410a450 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 937283965 1250 937282715 937282721
    0xf070501020706030b0319050a08040801090b010e040308070c0c05040f06090506040c17061f0210060b0408120d09020d1214040f05010e0409051c02060f0717040305130612 75
    0x2018000b81405e0035000500c0795804101360200b9494110401180455072030100e05107204ea03080100b000c10042030105400005510101201d403140c12018070691721410070f84e07001e100403280100000e900d600041c968504c908860203006200c1d49d0030194850310303a0001012d0300c2903865085420340d5116001c1214290900071690821019501084414502e50005040c03840380250156000100004140951101c81c240c40b480c83c0c0b01e4104d0014040304e940020b45803c84038541a04075801c0c5075002c80d0190381e06003107504881c00c02d0010304a8803521903030001d45400185905021039500c1200501580368240580c0d4140d01c9101040d030a4108048085d1222000d0400c1d4910444240003c0c0055050310840030180c03903003400e000c0340c0e03580a100000c010703044c81c00000f00300e8003031800940c02c0c2c41c2d11034505840d1495140c082d078205547d5000300e40b441d003c04856084c0094284908500104544d40d0f80300d40240c082e14040345040c49500e0300300000380e00e6034801000a1820710213580210420301c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 937285215 1250 937283965 937283969
    0x1401060507051606020a02100c0204151403010c052505060c120a0b0105072424060c080412050f010221070f090501081801230609130813080f0705010207 67
    0x120898030f86403d2a90003907950291a100034001c0e80520104600741d40185071100d98564010000e22141a003000e0400d00d82005103c0c2c0c045030030580d03190308020314041c0660b03d450b900c940d81d0903041ca45a242982120b000d482020b00031000c8203c06000491000e02c400d900c80c0640f18082641d4440f04891017840c2d902c010002600c403482d0486000c1d00d81c0c2d1203401c40d29625000104d0204200ca482c2c4654100100010311303001261402c0540080b400e4035005120881c1200c540005209640c0c3c2001d640388000900000c060341c2c0204014060201d107000000c0300540102d045a0850b000083e10508a03444110504c0d0f0306801d00ca00d03441c3d500d42c0c81184035800940c502e405510651043c5019003240d00502445061042d030400017011403180f050038030803103402e0800034070110200c41c0c0b04900070302c84050b07103a061408200c001a01414940c1ca407070b004060a940000840096448251a81d0420440b0500b00342c1039102c006040c3c142040b0503002021480050111113260400280c6080219 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 937286465 1250 937285215 937285243
    0x212100e0702071203112a04231b0c06090714091512010609140f0c0f090609040501080115171906020904050103030207091103061012140106050705 65
    0x1800c0001c25580840c01004580c5240551041c11010b85001da40080c54140048400d00c98160700907104040034071189950b80d00e400001c020003c0300001e220503501036414004404858032011151264885482031b44115800c0d20a50f03041d045001c0508154001070001c0015480b080510040030024041c43c40104440c3c100317030103417a9120010400451000b840e0700401d81050101e203040361260a81c03075900c1142c4900070441c1c240c64881150040c843c0d1000c0b4568503103c2000268101441585180a1402c1c01781c8282454511107400715254064807103140c01c06000e00004001e52141c1c01018068503540b40041011800781200c0c6400c0101c1d6480b034100951110902903400313001044880c00703142045010320050700d1070b041500c0a441041103207604103144c44000400c1c03650104c1d0080941e40c100707409005600609200b45250b000c00c0e80c020f030744200f4410402c1d41840c00350340b41108520501202007002030188095901268003640700801040307000074040e0800170140980400c5840c8 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 937287715 1250 937286465 937286489
    0x501050418110102120a030c2a1401110d1b0f050d11040315060e0702071a0304060f092603093d0605040f0203130209150301021210 58
    0x29409100d01005204401501904400d064829140d10910140207000000117441e991200c52410003802015607025810000c0e649001c416020b0140b211030090741d88402c3e80103101042540c643c201c91504d00b103410482d540d83d94520300100c038001c40c007401180c1c0700d405002544070a13100030341502ca03207440d00d6001040032402802d80c0e541d4110302910348a09580000007920300e40d50041c65242d00c0b40707400180c5403240d80a0b00021400341074010750140d44410769902c441d52280041a80d84410070b0055100c0d0704560303418106812040c1c00038583c49030241d0300209145c808000801c08031424003005aa04244440307c00c484040841c1ea500ca4480301e04507078514614005038010b80392a00c004d030b14425003402422680550b0404070700881e040c481c10104018040986008400900d102c0c0b1400d40960f00300b0b00921101c0703805100792403050004205881d2090126400c0051510000740307107000c8007e450440002c140c03401d20140c400075010b2039078a0b1003401c110b040f0304801085580640d070320420b = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 937288965 1250 937287715 937287731
    0x1c03090213020f1b0106420905030a0809041803050f1e12011412070918142401180b0415140901050406060f050c0705270f09031b210301080105010504 66
    0x3089035600011846c400410f4003002030090740803941100c59a1109d540740c0704482d4500140481318004080a44007264100003074a03810480869074a60707048068045003007400341c10740d8020181d0041a00c1c6094108440074408000102038041e00100a00302c0e1003032221005100280086400c6181544120364002c8107030f002e10780041e034a071643d004650740145c4940114007c0070b02c05400c11000d42c0e1001084503200800f441213551008100e400c07104012020b03d4207454903002d4912507061307820907510b03150188c04100180019003000074107590071550f00c00b80312401003891890035003c6d0407072061241075200c0900400061080681046215a1604008200c00760b00615203440c2c140b401c1c10010b440d00c81036030310f4506009040e4051604070140c0c5032191380001c4a40c1d807900e0305110b201c03403050b0301c2e46621880c2c110151080314103015581c010480f08281c84240c007042004284060100c8d00c18081f081000f00031a940b003030445a42010100040c0803180080c05281e014001c103071410026070b0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 937290215 1250 937288965 937289039
    0x402090a0909060f090516060f0c1b08060705040503010e07290706020f0913090b071808010218180903070816141c03090213020f1b0106 60
    0x15040d482403030090359a0720500d03001c102143d003005440b040070050030080c8000e1070a29070384945071111038500c020f0081e04080b035110f02400b110720506e01680c0d60200c0f441100d81d1004c00391291801403051240c00e4040024001d1002c0101d184501010b079103107a15540ba080615082d180c1c51103521020703403c1000f0034000380400f044903400c82c461a4018040c100241d580c05501c030b00c2814005440103000143c0142040c85440c01002400300944a008603002d6508078041116110a070091180710108081546a40f1447d03004604202c4450340c0c00c0c865949010007422030b4015481d8011044282c561902d040c030300f01c414014501c6044c0c1402c3d105140038407825031288540000240000d4010074500082003005114406660b802800101c4075901c0c003020607595030001154840708200640402c010703d00c28000d8030300d400d038007801c501d0101d910032031010065001101c900814a001b802039a0030b01a5034400d0045600c41d040c0001407a60905407070410303020322515905059080140000c903d2 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 937291465 1250 937290215 937290229
    0x20706180308071b1208040e250e15030a0905061812030a0608150411030f0c040b12190c0609060e010e130f0605030d110a03050c1603030c05010506040209 68
    0x8951001c01008400e8400c01031420500c41d9070000017040e03020850a10400c156000104140c8001800024403a603503428240d07914030f00607070341d01c010781d05800c8803110540c0124440940d00c880104020010b607007104184500b078000f1a1125940307526002e03004240a130520106400a0007885c0a91159942403180782c1c0e0349a040c1c803025134074400000007461032a0a136101c1406811520280c90380d001d14011101e0302d4a006460961f00182444056003003844c0c005050008126984041c020700e11b1803908020081a41070700703294002d1400c26800c1c0500d4402e10906c03403024482050110458030600300200080c0d080d400030414010111414452142c00c000c111000303003c00d1030904101c0007028045101180341c030146480b82c0f4181307599040e501c0c3ca95000318041d12016811a00007508000301200c4c0800445c0c03407810f02c0d030850032a850110344108020710190710f84008803040c44400455451149200342d1080e0006a88141c0c010300f000710a01070244c001c07074110b43c01c0d4109601c40c0005411 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 937292715 1250 937291465 937291477
    0x4020432150604120f1403030601020d020106050a06050315031c030b0f09150d12120b03010212060d081608070308071d04020a09050a0801020a08011d04020d05010219020706180308 79
    0x6080d1450702c2680c00c2104158404126580c82281c0390ba0610001441b00d42d2a00140d840c02d0140c0900e13a1060406881445180203e80005241500b41c80c0b80c00410380c5c440e0300c0601300305081c803d07600003280325403030400c401d810306961991720003030b84808000014101c40d0210300c1c2620407004120120f0346a0394000006404c100401106503059640c03038000b4807d619029801480242940c034920012078000005500320404072a05200041140c1c04050807489992804c80c1803481c2c03103002c2005420406a4041d01a208006441c60b05108541d01800c4940d0240210b4140d9400188442010ba0210400340c015065051680c0c8001165050b001110b401c0e556485c099a4041010003581340300322052001044041c041100c801e0304d4408690203540524003020109054900000d01891510303202101d420201807040f219460700da0801000c0f9000c020190760640d001d10000031038904039020224882600c2e0003e002907446c040c4007800080860704416110405040300304042600b0708104e45d4 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 937293965 1250 937292715 937292729
    0x1080d110604080f0c06040c05120a0c06030b030f010f0213080a0c0303050f0d05040b0a1b0f0e0a1d0412020106062f1009150c050a030504020432150604 67
    0xd101e81404e050448140210311003902d01c0d01c22607041c48140b1600599910984070256404a103003000101507555880b10484024108524008104850f9110390700040800b80002d054403104c8186203445802c4d24905030032903920300c2d4000b54241084262049640080c0042c030b01030030301c107050f9807141101b002080c400a400d010000a02d0210406130908403400d00c145c0c0c030010042d80c1803504100c0855041120400400c0d0716289030740700d0700c4103500d2100d001da18940e40d60f54269100707014115640000328403d990040c000d0f40c0003042102c488150010302101036600300d84e0b40c0c9000d0501c00b04141e003002901040d0792512009010050380b110411543c203c001d800e41500503002018965800307808020940071703001e4200c02410411854018105240c050302c0c000241e03504041085007221410400b81d80410800c02510305060b0080c1c0050b64805c0c001000010300c641281d00c040b50381050381c0e03041d0311033b1040103103003254480003914415003114139107200f0004108003070089044c5200d680500701d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 937295215 1250 937293965 937293967
    0xf0d08090910060e21010c0314090309030d0c03090b0a02060916080a030c0c03050105010b0a3009050f030313021503100e04050102190807023904020f070b01080d11060408 75
    0xd407098000307448031790301e68a1000800106141420040003480d074020821002e0a0281c00305000b43c000000351a003010303000340600100c4500f080d0554507034040c0c41c4220203024002c070000074803074a1100a8124148650081c000c503142c01c802d400d041c005010321290b0400d0010206204220300001d030f0607000d0b0741c1414061401d54460074444024070055200401a60a020010811000d060302410b515130064581c01c910285440c00c0d4507404010340d00c1c014a010220604c03604c0320406170000001e05005806a4281402011469095502c121405084511120800d000f18100085600108100100f84034150709240b18074180c0f02c030141c450200404610700104081c41429030407034000801045007147c050f10045800f61203090125100d40150040c9507540324500e2a40075298446024400320322140d0034009100303001904804a15034000c0d84c2409140041e158490041c204140141c1d2021080c0d0300d0550710360316011004c42a4800c009000502c0364203600001101500158000001 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 937296465 1250 937295215 937295239
    0x15060b030a0207080f0c0a20090727151107080d181809170304020f0420030c0403050c1e04020a050d14221a04020f0d08090910060e 58
    0x60202401004241c4114481c0069000762104000401540982c45411414206581c6086d02031119120001d21500542c5401c0014065440f415001d4003016451000100c0c5010714be000c80031020031030300840c0442020070300422846812400014003143c1746002001c860303080000f440d445106484840c410b101c13481c01401c020043c0354851f580a010f55103800c56000c804000303000702a104400c004d6840000701da100103c050218030440c1c1c42580c01400c0f010303c3c00c0f86d000602c00201014031040c00405014680c1d805042003840066003d03802210301291610b00718104241001c3c034603941c3e603210f54a920215081e81e200040c0c040a040c1c0110303001622620855802e0303916105040c4281903203031401079038080206220392001d015900c40300030b00c103a046c81c41041c0c0411880080003d000005624018000c0c1500c103c01d080e402403000e061107000c2c00704600440e071a4941e0a80407200c07103d02052000d05410910100381d4130010312410b4032040d40c680500508806000215039000d41c06013424 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 937297715 1250 937296465 937296473
    0x309120203031926090c0f060d020a051201080a0c030818060706090314041d101220010c080a0305131203020901090518062101020d0915060b030a0207 66
    0x541d42d01440c0007400c904030701c40c1e480d00100301c0400a0490070240100440c4465804c00d460020780c803944038203005119003071b1030408110300103d46043c060380c060f00401400103401e68074000703880d5000e481d0319019114440b40c0368020300c0d880160001d40c0b0692020340440c000c509082202403c0366003080c20255204144214403450200c4000e440d034112400045038000c02101d6400603001d02e029586841c2d41c07400610307802c102c602c00c0d442a1200082c60010b0741c2031100000d43c4054020f00c4000c1d21a040e030340c1c2da0140a00b00744c00c4100550b554485449645104881898512518071092070040440e40083e0b070355246038090745406104141e507520014410705c1001e500448142e41098440b003031800d012000502a40c4002685800208400000501e504106203105540c90170400f296000c0c1d80d99506200d200388041203050568111041c81b040030307101c20300c024903091500c0b5a02084a44181c28020b03142001d007600c1c0040c07a880c201042104680b400152504048544070259480c00c050034 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 937298965 1250 937297715 937297717
    0x1107030606032a0807060302090f0306010f0807060e010f0c03030b0d0b0a0605040b03030405010809071a2107080f101e081c0207050d02040e0312010302090603030403030912020303 79
    0x1000d00389400004018482e502d1400414800f101000c00706500100d00c0d0412a03615900c01c42c0e8465001c0f11051210600036005040c05110182c42400304440301c000107483c0c00d5003a840a039502104490074804101c081c82044040e1446040030b05010010b400020000c208118103002085490042041014070a40008001c0701000745980c0c8401000d0516800071070060300c90301ca41d149040000074403400e00e0b008903028220010080c50426240000640d80000c004007800c01a015602010864500c1860248030100000783c445494510301d02c0b1a544000340240d034000c4600031407040101d2194011055036018031090480381d0b9035124550050707401c468039007000040c910a8101a1200f06e0343c41e1402c0b003203c060303500f142ca40e40c422a400a00c216050a921401608801002c1c003507802c0c6031030b5461801d8805000003880c5402c0c141100d040d0340050404048003000d40b070040056180a840b0160050340c120082c0d131619146a9020b45020070760301c141604514025584415036400b80 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 937300215 1250 937298965 937298969
    0x90f04090b0f07110111030610030b13060504050606040e04140f010e01150609030f1e021f180f030209060d0b13050d0f1719230c0f09011107 62
    0x101c1000310710b08101d4420040541c1c11a80c000000b03e100c5003180094005000d98294590790f10442032a5883d644240113074008460720520900d03491710800309049e2a0b0441c05141c00100c1180080e19505000401c010380c8c1018000a1003044144070906c0181c2001c1031054000c1ea201000e01104804141020b0803c040d85038040c0047d480e08804d5012558190403102d6084d202080c40b0ba215625100159861030590102500400c284090440010414018072100c00c0c1542424484803a440d40001c0d0070004404111503039882c010030a01c1c81c140c0258105101442d8040d41c8a042c80c00c00140c024202c0322480064452110a4046502030b16408405220160008007042c101e18101440100031814400c08441034801c1001c0c5d0201c9034401d05441c5026161035440d00700c1d411070002800303101680a00f8034807601c8602d56410451681c00d1003900d00c24801c000c121503111903002c1c001034508000414184200307900300280d1810710922411a8640e00c0c007401c0c113071004c000200909150070016 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 937301465 1250 937300215 937300223
    0x30c0901110d091701110702130b03060c0a08070801031203020a0507140c1c0312110c0d0e01020d0207030b06010807260103140a0b071214010f0f1505090f0409 70
    0x2c0b020150485520044103030a5a42e24413503000c5048004104508a8511407500c81c2946006d101c80c100612700031022104903a20500e02080c1c5103d0305c0006400d0100c1a9000004100300240f40709040760059216544018241045c819941c55510790307100b04142c00c4443c03000c25a0020326000c82030301410580365140e030042e01c944116a909140903070b981008040ca1846000501010108440c2040080c1c11080d403541e5151205030702c0050b030b9400740658000051000780203210840c1883c908000144549115555403004c03031040c580003906109105030b0860864002c0c50040c0080340941400541140c5c007880c0410300c559461000f101c40707040c000064811408140c10031808044040c25082c10f81c2d008a0400d840c1d04e12158006a4500b04104003c14912808000440c150701401401c06507000c084804281d429101002d80318449007600080c414400c201420f2140403503900a11020700030b1041100f4543d03811200192960240420640c8103014411041c04280c84980280100c2c50380 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 937302715 1250 937301465 937301473
    0x1290a0b0d1d0a020103060f0b162406050103060b04030807170f0c0304030302070e0103150c120207060e0d02071a03060a1a09090a18030806031c0f08090c06030c090111 74
    0xc6095a466203d4140c00f43e002a040150100c3d50303802e0240c401f011140c1034180c86181c0f103004150035040380c0901a05480c003070709010302d14090005800d65024002880000080d070281004005401c6459540214190503c240b000b480050303030744402c4403401d54018901070303c10003c4008980e114480c00d85000c980d001c000c01c5202790040c0001c06001a60301c240c080d1188591590402c40a9420034407001e0001150800c2c03904101005600c510303000549403a0052105d00d0b000b201200381e03404402c2c101c4030a42d8070599050000014010700c514482c440c4040c1c060103140c20341418043c04104403042c8d000c01e0000c003081c440d50740c0c4840d580003445d030100c0030707480d0b024604440c000755000000c07818099440d0000044980b102ca2003070510320820300f07110203e180d8540c0c40850301410003c0100f0380612640c440c0d400d0301d852840f200038482511340e4a00c051111160801004c001015107100420f0303105458202c01642c0d600c007030f03036030140c4481506d64a5104000040b1a080b03410040044c483c00703 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 937303965 1250 937302715 937302761
    0x150b0a0809010e0a15020c070e011401080a0e0604170d09030518040c020d050d0e010603081b1c0e041506020615060310030f0c080303010801290a0b0d 66
    0x9041288107100720900c0c4000c0191111020200f601c0b42c403c04030003441c200c03080105c442c0b0148144d0203040c0e07a903940411035042540b14003072285118000c0c0c101c4101c009850841220710741e4001b40181d48010400018010215819185943c41d84040e10040c040f681c01088034007808994001d49411000c0800d05010f9001b4a0230054480d520010b240a01c04a207a440c0c180142054002c0d4030130445554000c19404032080030072252034001d5160040019191381d20180d00c0c1c8003d000e00b1000d1030091039047c0d40c1d00300d0072159041e80d80d04a0070b004041d0708110314442c03225071165419500068242020115509000b000400a04038640c0096940308403810111310582c0c00540c2604c10521400980ca40102d14410440280000c035500c03851000710240a10010305255600e0b101d6030f214401040442d03899040b4141590400d811803d1241e41d40c0c040c40c1d4840988001c6d003188000259004040014034001158120000b805802d0051900180d51540100c170b90340310741c000010031140344c21918 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 937305215 1250 937303965 937303967
    0xf09010c08030403090303090b1903021c0603080301060201051803040506030a0b0909010b0a12110d020301090803090105150f01080403030b0f211c02061303020c04090803160f050904150b0a 83
    0x1c817103800190001460354201040b0f260f480d00460b007024038003a240140c40720130120220082d50040c0c5030384421980f80c5071603141c0d5511368003945000c1c505c20306000d526503041900c02801c4544c01410315007407440003420b01905d0240801243c00303841c0d054510558a689000a88015140b681305c811782110701d010400841810662152040100403104010307503a5442400c2e4040112401018140e074400e0031000303c4524118440c284250320203000420490460348600e0710b607410855180c000c59444004100b03080066034540000c018044660003214a40300700002c0c602e80c0000c20040034180c2c1c039074008100e9070726076150605842006250090403a800c0d9100d00c24080010100c61041c411580090b50551035030114030030507070f01d580c01015640c0d981a55820412040d0b0016810343c0281c01c605400c5403280c2c051041101d009425843d40da09007510540340018400d0701c05c0c0c0800a00c0400f521a440e448012100360020846000c640c9800f609030b502043c400b664003600348058009100400a = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 937306465 1250 937305215 937305227
    0x30c020d0f03091e12261b01091a041b090f0b09011202060748060f0c14010f0903260106030e1501090f0c140f09010c08030403 56
    0x1d4030070381e500b0350b85075520348030100078580b01c0b10040240c0c1615282030040850702051440f04a00490243c440101c0e82254002c82c6165440100b40b180c03000180750300300700e051a06806400c101c440007000311000949403a004495507040c1c02503141d000401003028405610040c600c2c40c1d4008100c2e03000c6a59554283d4000c0c0341100e820500503041046040c0b0610305403800d54100e41c6003180303031919841141d00700300b0103034000c8404480c1c02d50f070110901000341c03c0e44a11901401180c4040f0303090a040001070000002242a410964184620512805500c106440d0101c00c513410540049815803614030441c1302c456904021030740c0303081000c948071800e0b5001002113501a03140c2500804ea40700c03600340c114091003541c56004548100405c440d5120b9409102c004607904103030b403003800804148a0001c2001c1e44031040c080c0e1035840011f01a601c41c454070702484003038282444000c2212802c007009004230350080180241c04540c1c035000f84d005e08003041119500c46460303070380c3e8034140c034000d861 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 937307715 1250 937306465 937306493
    0xb04080d08060d08031e012601020a021b0102010204030b040b01032f130204120b0f1e04080702030c090c12010b0a0813030207080d020a06140c0412030c020d 69
    0x494462454810080c6009440c5140214805000100f805440b80c81c1d021443d48050125400c41110710191414181030294560103030400080c401c980b0701c24150f000c4903240560a550f40b042c0d1042000b80c01c92900020034440c0407600d141c01039101c00030070006038024016540040c02e1111001c1c02c000400c80c1d039002940c140c91280342d0401000600710001032035281e100029012001c29850004070300d141001e4601003480300f82501600e0541c4420011910304030a1400b01d50000c8101c047c400d9101c40d5642007640008246424005001000c0403034120710800350010f02403080001b81d00d01036440a01c00c8803400c69010b8011210380c0be088200702d10b039501590b017080a010801c800801e10800a104550140c4880e5a0380e50094490310325130303c016140b01200300c041d44100540000c203a00140b100c1401d05045402a00b0403044a00f082c0c03064074032090101c00401c64010402045900301c4042e00c090356810302c1c074000500603d250a84034961400c10281d4000c4810307a10303600300020441c07042c04d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 937308965 1250 937307715 937307729
    0x7050f0706021c030203041b030f17031e0603070f06090314010501050d150b030712020103060806060108010e2e0504150501091a091206090d110d05031f0b04 69
    0x200c0c0d9448004030b07150074100002000c5441030142c3e4002403482a00950b0b0094080c05604102c07041c204000c050a07200c50b8400c48400030175a4190080c00b103c3c00a803009946284641859440e02803050085c0c0e0016401c4065280d00c00c501090f65503e0400c20140908190652620310a40380c0d200609600c2080c40704036104440b5500f0702d0001503060140d0380c100c1c0d01c0500624a141003a0b5541c0c101d21070100c484080343c0e07a4403240d02c102d85c4c1c4d041103c1001403992400908400e4240e00004040d203d0b16001f402d0380b58000c109120702a640030103003c0c1110503801c0700c0500f58682d507a03c04002c40e04c014039070305450a4010100070468410f00ca000860700111410410f000c80c00008000e02d07080c81c800c06021130b020300350420084117500400302180c28018416890490440d000883e411200e00100e00c4941c003100c10846410000c0007401c1e14152070741083c50215804c0610700750f41c0c0c3c00c0c024516040203004404a03501d100350307031454a103e900103042c0c001119190386085c2440c1d0054030400e1 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 937310215 1250 937308965 937308973
    0x9050c012303070e10230a0c02031501170f12070f05011e0f0b09070f0e031009061d06070521090f10020703170403051e0c060c0f0a0f0509030307050f 66
    0x1450346c010500c0700c4100108104c140c3c1d0300e04130f41700701112980000c5a980140504e02d40040010b980610002ca407044203034000150a505040030882044d11369941d082e1180d2001c0c04010441d0b100064001c0c41c0001084500c0d55a59245017a11151b080f00100400e43d6003040c0c40388011400d00300d0800600b03d001d001c100506401914984180c17100701c1d141c142c01c20101d501141c2d840e482044102c800c22000e00f80748082000d440b001c41d145c12030a07401b0007941a642c4071031004000141c00b60400100c40082000c0403480c491500742d0300c6003409001c82c401d1200001d428000090002c42d0030714049800c00b00c2d002585000e41d01c2944030040e00c115152035014001055505000354404d43c0d03010b54055030350318089041300d81300300145480a0001e5050000c103102c0f0400e0100d0403003c85407035001c107202d59501e40f5039044001e0719160002e451088200800c1c04682007503480e903070617215001120300d0021210310740c0c2d0706d0940d020701c100c207030864060000059600c1030040c0003c88184005103035080f1 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 937311465 1250 937310215 937310239
    0x30b0c220b09032a09280e0c03010516030b040b1002060601021006060f030e0f06010f0e01050108010e060f0d02100207140f01090b0c0c180a0f09050c012303070e 71
    0x9214001c40d03c5901d644c80311400f51441c5400d0611420240d4080468000756031710300d86144464012107100c0840f108600d880700221255a1005e00030f0040710f0f03c1c154001e00450401418900c101301d40586544e041550f603c1032001c2c240c0d0303960407140c036003400904103c0510031200340081d201e9804641050141c402c607101100030f8040341c4220400c4604a43e5109034000d05800114003804021020115034854074040d100584020701c5840d0080107844075119030a4036140182e01007110503441141400480c8004001400c11100d60a03807101003200c0c0500300f1513070800087d110b1221100080d400841c400d41ca20381950300021900103480064901002d918101410020440000340245000600c400c4040080312a640060101e529110301a944890a1480403e088000440107102c55590300004c1c82224484c0d03205140702c1d40341403a02400025050340742d240d82e03400403081e01810441c000851610118142c4c204422042e002900c01340d6a041c486002096520750040da244510400848 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 937312715 1250 937311465 937311493
    0x803070315050a0b0d060f080a0506010b04080618150a0b0f03030c100c170408030117012c03040e011202030106060c120318080c0f0f07030b0c220b0903 67
    0x5400c044400040c4524440f90910000400343d41000c00110840364480402107480c5102029500103010404010300561a02d0300b805494030b101030307000f054540803c000038001072102084441c0d1255807503a85540801d01c0b04981442e280c12807102c0c82c0c607042c0301c005011041c1d025810841c1e1000b02141e6840901311007400b050b8032407240d02c1244600380d01c0307820f002c0b4000a036500000c808010300d003001c440b014105c0805101c14101154101d03944040040180807400e040c81c081c401d03110f02100204004c104030b4040340389040f148040c1c00c02481c1e16420043e45447c007001168003600080c070780030349a0359541500d18007610014004078032a50a040002c21024804d100200c40990403c100c0c1e10014100303082500146400c40c03505043d01e03034001070b00d8040740c616001481918210401000103109802d00d01d81458421101d061072904840010400b08000200240c1c01c0215207400668a420411052010001d5911003d001c403c203e50000355500b84a0050f0201c08426010b646641e051660 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 937313965 1250 937312715 937312751
    0xf0608010f020c0c090603010e1005100e0103030824060a02070f050d020108010902072f030106050f130f0b0312040905130b071b0206130611030a0e0904061808030703 73
    0x150040150304c01d5613201d080c0c1ca4110a1190400d001030000109140407000440c28070200c5080012116255018402c419030b4405070040144070a194103d00b071b506695000740b0240000d0508420b08180200d005039040d00d5490f842c01c1d0070401413645540b1041003d02a4a950b2103100790b54000030500c00004290600c0c41448100c0f6905039500380b51a800c140c050030094014000503906186180880c40c0804500c0b000880204119030403200041c401d0070416095840ea40c02250140c800c501d000300898840070f07607901010380c0c10800490300c60103061031503001b85034185505925110b1a180e0302d400d004080000c005a03441d0b00001e0020f944e50b80b000c064031080006000707113001d60a0340014000b5114140c50a10800d0034803815045284035000078150b0703048045081d504c1100020b0410420303401c0404c3d40315411904020b142418120359016254940804c1e5640c042c203403032070000c1d00700032103980101c095507a201c5003446541e081d81040800d13a001290980701081c504402c013081001194 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 937315215 1250 937313965 937313977
    0x703140607050a1404120c050910140607050c0d0c060f020c060409090503120115030b01110715210b0108060d0b01090b12030f120601050c120a0c05010f0608010f02 72
    0xa1151490100d800c0802c8500c480540c030740d20130b451418840880c0140381032a0341c4030b0241c00380b1815503059040c4800c000000c030010300301c07040880c00604100030700b9000d1007603001d030440b04079003241c1c8591550508500708011100e1613030b88041ca0300044000c0000a0150800f03641d4191b8482d8100c05044405a130789604504440754040e4041c042080304850980003001c2540c4110150303402e01c6010f1071180f40c60b10083e0444c002100305202000f403e943d26106003402e801e824a00303c503a42800d8040252180110b0003456014060040040c2020340521660f80c00d07c005803480060900800c0c402c80c0051082d0f0000c0d900294406012079190302d817505c038002c22150014032025242e440c0800100c0200300341c10115400000071114440150400d00242c000c40c00c0c3c0040c22607484e001070742d80e0111140006c02d07241c144201807100700e8407250001825540d4060740c040c0e440c2e95980c070035010740f580c260b105001410b96003042d50680c61002141c0011085420540c001d11000c010790310164241c0c0114 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 937316465 1250 937315215 937315217
    0x1051002071a0904050901060305010f020f030a0b01050c060702160e163b040b19060309021f2105090c150d0203090a1124030403200703140607 63
    0x60302082c015245169000d2101c9200044690b15200b104004101070f141c0c1151049080d035542c3c0402c00500c2400c0c001c488500c40c05000c1185801c81d0070748120400d00024215000d00c9640d414845410307401902160f0382e0209842c102c401d81d103045003009589803603040e204030b0307007402c20000025a82c41941072103006d001100f42215910752444d0089441c5650f182000702d008185101c01d03078000c0e16034102070510314441007411041e040c0311810f10041d1000300300503902510a80300080031104103104290b056a2007494040f824002c2400000c049200c00000c00031301034002c54a090845402c9114255038818020911840002a4400c03008446c003c4411100a030003050b00b400c50341c13418100710307422541e0a07a545803c02100130110401c90b04115040003071603100d16031000a000400841c2c2d100407c1c115120000840519042c8030300340c00517900301007490800b1000c501014041e0802c003d022002d00070104803c0034031080d0782c0e65490240300561326030b00f400c44040d0400d04c000ca5003500c0b070070403 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 937317715 1250 937316465 937316473
    0xc09060e0c03060d0206041d09030f071202161d0f070509190b0a0503011a0c0304060807052101060e010c111c0b0a09110103052e09020d02030f01051002 67
    0x380000c0d8004552008002c3c1c1d900c402c4070b80d1440011382d6144041d0003d007400c02d0840c007a020790751032000c20503500500598205e6105001c000d86e0b01d1212411070350074941c0700e01c14040c50150742e0f00507403030400710001042e0744224000c0c0109203481c03105078402005982d481540c00c55210b1601e17000307a10310140d50312400585e0800c02051b050400e80320f5142e40a0540c4511141c507075035191107a10301d0308281a00000208004010412a007050b01880d01c44540100f08619142c4860039040d1360f449144034000a1004500000e201d55000b007060311134040603501c980385140708050031413040700824019080881c900424040c0070b5407250703199000080d4003030b403c0303c00d00c2e07000740400c25024100e45040385120750380c41104000942e039610301402402d00a401295202d0b840c80c101316680442100d00e41050300d00f000308072544100d1080e18442e11003007468180c440e42e90204a10300c0820340d400c03800b240380c00003c0c42400c5084070b0740118407a24482840d48143d90322002001a8003134180c455100581c0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 937318965 1250 937317715 937317721
    0xd1a27040816050111030403020f030f0304150209210d1803020603041e05060f0703050f060d1b060903060608030f0d02090a0f06080f07020c01021209060918040c09060e 74
    0x1118000d00050701c41c16003400c61102655185801c0d1180b0090817060088040140300c2003640410034000409510b8001c3c1d070a00340d1a503080c05060200601c0074101205102c59a41d500215070f0440d07140b410054251380d43c540000030800742c0c2d04090070741780c1ca0a2051040c00790101d40701c2d88000360b96408890013000030304d01e0340c1c08018554201070403d44079045003484500c2d00d1904004186a170341d1080001d8402c502e410744070301328682802800142810304240400540c00340d00b481c56a07000404503800102141c690402c044c401850142030040c2e8401501e0129003140c01110360340859105400a02000d40c403a0400c917124002c0d8007010b20704440900400038038649070380103401103640191201e00301a41d191307071110011100d503001001240e00c00043c0001d54411a0107594001c0c00d07400142804800180000d603070300200c03800c442c0291000300e205090790b84c1e08000caa5400800610700c03604002d02500c50030405400b9102190917148891707001801078040d00803c42120781c0c080c07541c85655 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 937320215 1250 937318965 937318973
    0x71109060a170102093a0308010306090c030b101a0c0c01080a0f290f15090103062409060c0803060105180904060506030c03060115030c050d1a2704 65
    0x10300b0b4049030700400c0d502407010020944400001c0c40d811846400400c2541c0c66038244140801540e031115210346042c1d020a001198021400d203044a40c08440080c4580541c2000030300c400f0a90030050250340d0328011300c030305c505011030381c1410b40d01261192840348000595092251013a101c0d4545d1542020b03540d0302c1d0700d602405003142d101e03109810105a240c2d46510003411240290345d81c1089041c1c1034400400e1805044560710a4078082d0b0701e600c03045402c000040e1031600c01c5d0a11490040740080c0c0250303540d00c0b80d0031020043c801d503219560300e110007180c0d0b00310420b02a9994000216410b0f00042c00314440c541c201c1065402903010307440e6031034400c011a4950f02451741440c01e00324800c61000c0a8545080280c0b280f0f0080d4000511420103008050400e003c00ea83c40f44654030420051100d5100c0b041160700e5070f40c60b030a00081d40c000b4103c050381d450245000140c001440c1c1003540c105000c2640d03240400701c80c00c4a07400b0010340b1804a00c0c800101105010400d0b00490700002c0c002 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 937321465 1250 937320215 937320239
    0x8070509041218081c03090f02090606130806071404140603060a08030d050a050c040303050316090e0106020c01090f18090507120f0c090501050904061a09010b071109060a 75
    0x84070b07450905115a00c080c072800c06559194044200c0f644100301d0440200300c080c41c2100088207510342401084026110a00a2030079004d001e41710740c2d01c4c80003180d07055407840c5c11101e941410f02c4218403d5591580c0460301c2e400212598404a0102d0320703003103200c900c1d1030122410759a001c440368101d11044e109011003a000200000c1e04040d8035107000c50f50600800c05054080c80806020130719152040221040d0340000d0301d071204540c000d000038000a50000c007500d50081c0d0064101c140032416481c21904200341e544004040c1060a0000c2010359012800010712102070300d442c07103859903038040c4c403025400511540f40380d9142c0215003103080e8000d400c20a02d10f0302450071292030b281c0740c40c410481203480ca0011200b0881d00c4103a1001c104103802c41500600140204000170740c5018040303103c12000400081095565010411550011f1954464000c802401ca01c44668403040324602d1548000c0003500e00f000c4e51064071455107840d84026102d194080d1626011924000c005004 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 937322715 1250 937321465 937321493
    0x6030a06110d06080303060301061e09090f08360a05010c060906150f0b07050726150f060a060e12100222060f08010b0a0507050609030307090807050904 67
    0x4a510411142d24002100d001d180050064480076541d6401d10204041c00c544007948040e9100850324920380c0200903589254040f03d814880200b41e992244c60901075002600360024074801c00840d0088420001c2c25241042c2c4103560410100001e025400c800c8030048008501d60050452809100d00d510915003036019603c02d60000c101241d00d5500c1700b00b604c82003100844c0280c0180c5080004403a1a400e4000400503440d9491400101c0d807035454440f4114010784010302c0d0300c0d0359000b0b480c49091f2502e410b03420040d030603640f8018074042da4056085051340e005000c4451103000ca4440e03d08a00c2000484089454154181102e5814802000d00002000005000c0c622150310f80d40102d00003010688180020084610b0340c1c4020305038034008030303040103040142014030b4242d22904030110a064a112045a54480e0b903070040071140e80c82a140000e1a40c05034000340305986c10300002a50080345192200480d00c0d407521b5040c1d03629603440c4201540029042c01250124042c0202000 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 937323965 1250 937322715 937322741
    0x915190c030c02130c0f17061002030f030c03040b010503010c02060a0c09090e030307020f06150d0204090813091109010c12031b090905060913030305061c08130503030306030a06 78
    0x78a41a0001001680481c2c1892221034071040d50040e0154882c1b82c0c1240c0b0b46440c1005001c0094190310740d151010001c200c24021815542c0d401c80c030b00e008009440740c808818464a50b03925120321310740100e81003520100c0d5a60490400070070b02e03103818068403020f20030710b42c000e162a94800c0d0300d507005051a540f0079024841c2c0c3c48000b041421043c00740700c000241c440011075481c01c04000003880c043d00000030b9003003500540306001114500d0490329180060468101c12100c0050001030002c125580c001442c0c3c40d00020100b1546a0f21561281101c5840d41c1c2006a5100c81c601c09602d48201c59410307002590100d2484001200c845c0700d01c6540d5180d180010780840c110000c1400c1e008440410740114070100d00400003001640152584102e043d11000507e0800c85c0c040c51000030700480003002c1c1501c8200144203070300c402548111610800346040c54001e0241400b04aa81c00032a4000144404c05804611400c0000c01c41f4040c560113001000712280070784034030b0014240d002000e4 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 937325215 1250 937323965 937323977
    0xe030307081008010204090519060e0403080c0d14090c150406052505100e07240e04020a051c0203010506090607060f02030423070312030c020a02040c02030915190c03 73
    0x100700c1c3d10b0244003410150811000014050800b10700a030160280100806500703400c100f028040c150038001e00540141d8182411281c03a200c96807540818060209400003251910442800c8603003920382c00383c0584c100e03c05844c0040c0c00181404411600c101a01500e80710410003081124814801403100d03000149003120b00010b000c0c0c10014501017402c0130359503030703000007d42c1701428038a03c14138044501c83d000402d00d80e0710f03101c80017090b078400c2d4403038114414510030401040d50150744651a0300780014021959050500c030050039540202d440d0b494602a00840c640800e0810b00c201c0c0d050314070060580382020310760350801400c2d80c0700b0079080b28980d031515480114000d007030000c0c600492044032150140200c0020401c0c03002079140240006500003201003010400044000c50400360502e000700781c1100030b202c164038200300a400250070034502034a22500035808005044d2010080b103d1064408980010403003501401441c0e0019144030038684071018010200610b8482c4207090074 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 937326465 1250 937325215 937325219
    0xa0210031a100e060d06050d06140c0a0905010c030513080f01060e010f051c150f050c09100e030a0c030609030e0901080d05070f02120c03010f02070503090411040b0a030b01030f0e0303070810 84
    0x11921088d1545422107801e6114a6884a5038042c42c05456125484032103007030810842c804010020714880c8645814001c481c05048149403241007118840c20b03c144d10700341820786c0c5180442d50340c9460009070b0703072551809402050030003490740c00714102c0d07498040c4050034500302000c1003240002002c3e100140348030f0b210480c00150200142c000d81542c3d1040019070b2007000ca2a040c19140001c00c000036000c410060107106070345200340b0f900c0107082d0b850300c80da0750b00d1554040b80c40c2c005480406001c0c441c90180000400a80e40c200c4010148240d4404482c400b80100b03005180200307001300001c0da0801241070320494441c0340582015030044c180001030020319004550042c285000401c4560072000c0780c648203080c24000c1c00c20b40c041000046140401030303102c0c603403607005019400e4440c603180c00480c0d100001001c1a40c0180c080d0501540c0d0390203d959018000380800100c150100381880014413032443c1511440c0c05044440003d141f450780c17117500484502c0401041c9a2114101e0080 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 937327715 1250 937326465 937326469
    0xb012606090601030227132916030606200106181a0f060d0509071e030512030402060406080718080a03020c0a051804050a0210031a100e060d0605 64
    0x100d4081c0e0788090240c0001d50460040c410f0081c2040c0d900850001c020001d02d00b84e09441116961115000e850781000170a60300c2e12181040b00c110a000100c032a1035851400300c00c1d1100b80d180110140058095101460801a015a4010311600000c603d9800c01020306401e540c50140355200c5150000840c50b489100c169241c84605514000321992401d40c0350303070311941882c40081d1001c00c075640d001454000d40000d444d8460030031103802c1e251300d4a022901040c8100404006015160100507444244d038010121503074080c401901d99104a00c00803003001c03030050840380125000b40020785010308007002a141c0360001b40c0000100b080480c580e101058041f0a0a0007521403580940712103a06810020324000f20746440d607114060004003048030359140d00002c00116407103c0e080c0500c0e0354904000b03090160104001c3d411a001a40a4010036450b0340200c440041c280080c5121000c0710045c0a80e131184201503074003003000c10b0218145807415201400ca1000c1c001e402160f0603443e000 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 937328965 1250 937327715 937327723
    0xe040e030a080f0702060f090a0b010e0412030605030619061d06090f01060509040506010c050604050708100203160309080d0e010b0a080d0e0f120703050c0901170c06030a090b07020a030e010306030b0126 89
    0xc42953340800c0c41042c0f004201d00c020f00911685a80d1030b050041d41d06002c0000e03101c14003d00348003210884000390721140000342d00f0940c0185070140c0071100f42c10395001c00314a0124102d60071449a440030340090f610045400c1214142d4580755905401d100540050100038540500044e040c041c0d28210140050810400684524070550103054103516100380341d0325100340c0d0042c611205005204000d26080180002d8242082c50700e0040b07256419410424414410100700000031420051a20301d40e41054000115601e010303103001e520301e9038442c0a81c1e1206002c503040c1001030380843d100d921a103001003c8034490380c40100b661084601c140175140c03400c44d032540122465000003104200d1861303e1a00c00d401420b00000c10112100284804c3c1c0d02d039100c4941d514401d41001c804560192000d910205290b90300422201c02401c0401e0b0180d510304805000704c0004032244203a180951090007280c0449601134608030040c0d0070100380400304803040c48400c3c01d100444014501d2100d00700 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 937330215 1250 937328965 937328969
    0xb12030d0b0d0f1208070e130f02040b040308091306031a040804050d0606032d080c0a06020d1a0a0b041428060f020d090b0306010e040e030a080f0702060f090a0b01 72
    0x9402014104103400024160200081c031b040180710800d00c40405c16296110005200301041100041c001149040c00e8003c1c00b8039044078402c010007080110400901000a04c00d001084802407403040e462181d01d02a0b070040c3c0030040c031080220601d11800900251a250018807170031645041c00d441e0008151441c00d0b118040c2d03005526130000b00300380101601d03a110109100d1017034500402100300d4185a9902901c801031008100007000c084403001031012111040d40701c00259a601102a0240301400c0030144c41d49410501421302e0360589043c402c140c00301c0d10a0810541071901d0039910341180f085940d074150700504005100e86918000108000301c4002403000004680d0134071100402460201c540360042d5807041d07040f0303888160080f90101c22642441c0c03840d6541d13680d02004807441001c96402e07503002410300e440c00070422404405400ca05900c2d0380c6800a80d075400c1b030761b0200a907040d11107a0150b04944080b440d0440c81207401039004090030201d0f1000c41e207035a9001040c0d0800d07 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 937331465 1250 937330215 937330223
    0x30b1003060e010908030c0721050318060103030e0f030322031a06060d0902031e0105011a0f031b0403120c0201121b05030702010f0e01020d0b12030d0b0d0f 69
    0x58102441080102c0c071480c030580c58203074000c00140c10183e9a1a140c5c0c0710140c4165020140442e8800c100840c14a540d40f0400b000d180b1749c000020490406044c5420035a00d5030260f5000d416450b5200300005056070489800d6503412146800300307010b001c1708030441000a501070108012880b036913800c4240b4060300298800e4000381c103a00c1e40c240302c213248950380425100c0202410a102044d0b40d41420f94912981c000d400107451010781c80000e142012075040d00b2081e03040c2d101c004403840410752155041755009440a460b440000d0071010062041c0300442e0403212050003c11a00c2d46040d200c180546200d821841c079164403516001250007180710a100002c0da002e0a180465a0090060345030034103030002441030034000c41ea07000b4449c0d120240071040140100c00105030074800d4100d142c8484441c00c00304005401c0c40b2646000c0d40c0003154076482c1504001003e00c0e1130404d42d21541c9500c150740099424804083c2e40a000740025005003030b80080203803903d070041001001c400d4141c1344a = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 937332715 1250 937331465 937331491
    0x32a0f0f03090f011d060c100920030601030f0b1003150605010206070903020d080309010207050a0c03020a0e130b0402031f150f1d04030c020a060e010305090105101e15020609011a010c06090309030b 87
    0x4042b0302036921160240f24034002c0c0c101500400010380c65124100b0601e83c400d120703c035a551186c2c200c01146c0e60076403010704401d22440ca003031503102c040d0380220280da1003030f402d03100c440e603403402c040d0380041c501d1000940100f9004945404510404c01a5420504450000d45440c2e0f041c0c40d020310307001000000341d400702070031401001180341c105045001843e015031004070518250b50701544c00803d510000c0c050f1000680010115a0240494405205820b213501d0f142601c140844005102410840c0700c0d0300c41e07105c4046180d0080f8500c00046a04000440d000008403480f62036039030b01c0140c421010301c1504550340c001079584058036009041640e5400750f0300e83c0350000040035035801810310411030745480c040c0300005d00740d60041000c0e86d40c0c40841451226070703000c0190214049034031416608007002d0401d900140d0205819000c0c02e040d1000f40440450848000b0410702102d07140c50125124002100018240c0c0d0407003141c980c007909015a165030f07662501080041d007140d004e44140c00c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 937333965 1250 937332715 937332743
    0x160606032f0102060106090605130b0301180b0301020f1905090d060f0b100f0c1704030305030414060f0415021308010c02010e032a0f0f03090f011d060c1009 69
    0x106072070030304000c403900f44000c1855501d08034019140380b2260140004002e000140082d14450354944040104a2140e5050342c030360390382d6808545c4400b0164601d00903405c1044000840c0381c1402926410118001c4051400000b100c0c42ea2030900d182d0403120502c40280175112107a9a12030280e40b103107000d0311b4045100c0317a82442d414202c03045118103c0c42001d00c010740700001540100101480b1045003030500c107440e0b1904050b650640d101110243c070000006000c010035500c9005103008030310401d01c0389400c100e4110690781340e43c0125020702c918a800000030b00442c10141d800c1e4840214900c0040c0b41500f01c01080220000c41e41021100d60b460b03001c069551a030900c14419040117207000f40d401c04001e0038807800c0842c0c40c1da03c0203581213051070b230100c01e4030703018416920000620011503505000c60500305440b500026002c5210b82002030202505500600c03009403104405800c5014268441003001181c4d0080e0310f040401d0300c503076850340724141024030441e443d881c0138844038a0542 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 937335215 1250 937333965 937334033
    0x1703130c0618030605060d152c0c22050708070e0303120c03100b070f061406030a060e100e06040b0a0216060b012c030d1416060603 58
    0xc54180d2121003008080190406085001a5024296640301001168988175000002d089060a07880030304500341c02d02039030a140215510140128043e5600d12045281e008241d458003030066007030082d6a08601e106004502c0c00ca820300600c2800c0045424040b114406507100f1100c00300c581d900441c40707100c144407240d90418281d40a4003403c80095103891043d511104c2c407070901400000a81c05c001c000b055640c11b00d6103d0038090302c5159201e0340c482d0440c0c1002c2c10364141000080d60312a1800440e0714026400c41c6031f09201702805402050000c00310703031303500004000b144180c150700d001d0088070010381039581c040d0760301d400030321402451542000c2c2000500b09202601d1503841c03510410100900f9400c1d013484080c055001000040c41040080050301c004103807802c8071120101d00c160305075010b4085c240811080205030110340d0030194443d001e40d404409500c0040f00200c09008200f1000076203500c004601e485050b020880d2581d0741d0710766078000280d00c4c4000b1600410040036440d8 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 937336465 1250 937335215 937335233
    0x5030408041208070335041509030f030c051809190608010b19030c0501080c0f161a0408090d0501090503030903030603060f060f04020d1d100c0801030c050d170313 72
    0x10071001d001c400e440103020090003506000021aa0341e41b00b104e6000605100c45051112090701e2a440c043c8241145454004d2180c1803000d4480d0101e03103400e01d071440141c410001c1c0c2c0c40300c49032a6000003155a40404000000d40001c203a0300441c407011614000114481c0103410007028100008a02c50024000300000f54a5051410000112490b030820101e0454803605040313030300c00c1c02e00c0082620b40c0c0c1c4500c00940f0442c0480c0500407000200c0703107140c08240d03119421540c080c0242c1202c1e03000d101c5c0320030520340e000c2d2001340c1040020300c0511100d2515014011680d8800d000000b5400c0c201e9403800e0440e001280c035049607420100800c42e485c02d00340542ea502070141600b10700c043c41c240002540c481d8814940d180a03035808604000b0441e0300e9800400c042011508140061a07140017a55442d140000b160200c54200014624542c0c026542641605c0d8401100703a0098101014884400c05a10050303c000700700402c1c0000c0000700100540c054848250414110070242c1092044 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 937337715 1250 937336465 937336487
    0x60c030605042009010c0b090706120e0715020114090606040506030616080402062205030d030b011b05150109091b05031b01022805060606040b0a050304080412080703 73
    0x42d030074080c501942e40b010203c448102c000b45001d840c0c0b14403000b001224480304a10b001404940f0400610408070030008107a070460324595110349440a24410660954001c09401d0001da401020140481c1807074889018010100384000a0384094107181080300c0c02050382c2d8000d0940228051110720309040c050702d07a00c41c0c0107030002c08507420300c1e9801c08204441c04859408001c421008542150b464200702c41c5100b4441d44c0050031031300072034110f03a803048062059910910502c841b0f405c03114041e0060001d1044140c46250400340c00160081d000e4103d0201102c80d401220035180f0301e08a156005406001540701c00602d0410b00d1a0034040341050712203030b800700102058108456600003404c0300c3c1d150f003840464400501d5000060389440584400c13081e984aa11001e02c0d0b8100e03044c0d50090301030f030254003115400e843e0700c000d109040c8114022f4500b202001c11040070f10030300500007180c010340b24140141c0380540e0b41c80c041e00c01080310481100c410784009418410325500c0b54540007 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 937338965 1250 937337715 937337719
    0x1810050702030604030e0a0314010f050702062217040605031e0606090d050c040e100b0a120b091002032e0b030604090521130608090706030e010209030a060c030605 72
    0x2103092040d4000aa803148014802020080207080007119500c0b0050340b40300465002203220141030514403040e02916030030910200444c0380900041d421480020050b006a8110f11685581201c0c0d0202c11a405840035040c4d4074542801c507030700301c201e0303611000740b005005c3c0d036a41075264142880c94034913440001d40c141e02c0c3c8050100038024150340c0c3c04221031405100321940d288614403458130b0b0f07060040c08018960b006107090040003101d0360100d4000c002551003070040001c0b107605001c22410780030a0080d89100349110220000281c1003005454024060702e08440c1d6000c0d00d41444020b80c1e000f225018855442d4a180c0c0d0303a80d44c540882c5003a01c15003102070030121801c0008621841c040104001c0c462070300c800307112081c08014400d20311050180e80a50348000c80740400c02000e0717070161411501c403000c0240300156072481025a5406129004064a000d0386048402c070060540581001c54555013041001c05690b800c000c1c0c0d00416100e44804a4001607196025080322520781c4a40c0c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 937340215 1250 937338965 937338967
    0x12050a020a2d0f0501030e010b0a0e0a060b0309100c0207030b070519050306130b0402070218060a1203020d03050a230117121b01020f03010f030501050c07110f120102181005 76
    0x8400072101002c1042079620a28000403101115907047d4050091070328490741100400f14041440004509810b100741618502444040d58800522640d0f00c0308480451054204a10740b040011141c2c1210072000da2230310448420390303241d40307c1e50407030700e415514200070400000c6d02c0c140302818021066504a004d05046086103000008144400c1d0035150204410703640300d0348040031703645d2541990383e290340107080103c05005404801c107201405035249403240e5014900081c07003440da2280c6135282c035415070141224810283c0260301800019102e5102d003503c0300c2c0c903a400780c80f00e400201005190312100700b40c0b81d4540085649140510451107406411151845890b01c80d205c0840b00c180004141424031a00d1003000140240200a00c1a1401800000004032000403240340c0c42541c1c01080200107e4403540081c091078410340100034010282c00484800e1440c00c010660080200584140222420084010308a83c81456080f4041c1342801510486081c00e005401310042c43e41446 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 937341465 1250 937340215 937340219
    0x103050c130e030d020301170a05030703080c07080a18090e0a0803090114011511030703090b0706060905071101050f06150d111902160f12050a020a2d 66
    0x6291600038804a1902501e940d003000800c1800c1c903480002c01c0c038071540c03c0d00e03107075441e102c00c40001e0750080c41441384e104650541c800320004042145040703070f41d0007402145402c81c50342d41600d00190003064034150b15001c3c411840440c50030001007020501d16030700d041c681c00040c800700c0c5482403030382c00001c6801e01e0308810a002c4100042d80e51000c0d030b0044022920b03030791a048014007415900c01c001e1000170707111000084200c4890001207811516488107648103c052100d03e68070b001d000030150010b2907401e03040015051801c000e00b04180103c60110f6816241c02501007692019680c4100050448540e4440303140280b08407608603488000c81c0700582400400540200c0200b00c1d8010102000141c10309000815030007403586071644e5682c2034494a0b03020880c50a1088040e084000d4025491107081100f991040070050358201d1466a07101406d00c0004055220442070855183c0300b0100917502603610407240100400c03202c4044100b4070101c1128a151a00390740050124800f140745c2 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 937342715 1250 937341465 937341473
    0x302030606060d060306060323030a050a0507021c03121a030a020f0d1727130509191118071b0c030f0b060a050307180c050403020a08010c0e06030103 66
    0x180c0d4205004840c0d40351911200700c40c50005000720781c0300418191600303000008000d403e81c0f102c8015517901d2400700c0c0b03440600361324548074440c0da46c0001c0006d0081040d85661800b6070068150140040d20510b41180c2458003441d40c2d840f03004050340401c45004481d2641d0b00703070b40038540d00016008001c215000d0107002080d580da401c00d00092081e20580c80d4075005d030310346111801c60260842c5c510070050340312040c100b620340c2c41004050040342072580c0009920a49590911704a00054810890402c50642034001805c1c0030341542414014041850002d9806903000e44c089400385111100301d091200802c850b100011505460b08102c1d40104207d440d0401c0000e1042039120328400e00054080c50101c41c100c100d904020803422040030385405000920800903c141020b90b0340034099521001003643c0c4240034840c0402884c000103410f09040b81c03942100307041c0e0b507860605500303150b26640043c9000d401c54000b00050b0b0b54070001244060345c45260213400d080150740031403540d4110740b1 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 937343965 1250 937342715 937342723
    0x304270e19020f030309012127060501091404020103090602040b04170f0118080309071a030703050f100b1312050f1006050a030308071e03060302010e03010c1b0510090305031e01030203 81
    0x505034108048d151742c0d10301e14444e50380040c60503040406180040c0700c07420b54120038480e1560001e6501c1c915207000810390003a1442400c07006001c403207161441d80c1d11640110043d14460504031040760b02404000751010416001c0c00142c0821104c418140d4440c3c81103510b00b5190a0901c4402ea041400d1500300030701450725813050a0304082025a240d4484441740d1404075940c0c00202030880e107420304041d0302c0b044409903024214580d01030103182c881030350000440c01c055a041d494034044080c2009542c400d040100f005c01c0e040840346c12080c0d0399000030510120300741c60903200364021141c0703d04031400500006401c0050190104821410314000c645540040d00004081c42940d41c0420a440d002342c2e211f0485515003003000f4660000d000000740980b0480c80100e000c2420300d1040c03e0140f80600848a1444d031a640d0820746075114501444d820381140300998050054001540e001100382c001c411074540030362502c40d0350b41003943c49103151001070044543c181001c03400600c01070350042 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 937345215 1250 937343965 937343987
    0x906090109080619050901020f0426070b1207170a0911120601081009050712030c0b010326090d030305071701090b0a050d0c031104060801021801110304270e19020f03030901 76
    0x1158414815a180f030701d064400d1030fa402c060307040d100d01480040e03e190200c0050403108010603800ed5542c4481d0b41c2591000034809141869507a03041c001111030215a0044c4212809101a403c0442c2d00b103020a020109001c21981d09801c844014030180ca0104107510b264006298100701440190721850b4441e0101d00a6842c24101c84003e0380c145407081110440041c2c00c0401c070f5169595900d031001001c010060055908407180e00045410080c0006032012244041c00456103236025640460003040d005054100740020100d050241000008016019004008000071200550410084500410340c0320038800c81e0007442c250b0009004681160072281d02c0301d20903000e0b21401c4c0024001d40100d4108011644c8003081c40f60718074469600582c1e8015080c0c0f64400d40d00034083c1540c0d220300c128000c51000e1461813000703000103a441102080800160700d4000340481e40c80125a0410314007440c500e98800c8296035640c15407800e22007010050346c04030001c6180c00d140f8800030340901509 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 937346465 1250 937345215 937345229
    0xd18060302031e090c09130f06050406061706091207030c1101030608150a0b01080405060f060d0b130507050121150302040908070308090a080906090109080619050901020f04 76
    0x102c00b2901d00700994100f030803010040c08841015240c403645455850494182052160f00000c0100b66180c0400c107a144801c0d40205000d41c00961036162540a0030b00500200e504c603640b00400520710090500c007562841e1120003030003c505182d06220302d0980350b1861070101010400c4050000b07078100b212106074950240c3c5410500c01d82030b005034010070a690040304a03020b8070f800040031003400d1000d240300700e554040070802d000180004440c5800c003113900410550004010500f114000000c0750341c0500000c20007940c1400360380d02c0e044045130690321003243c21a14044003003007040921014010300020710b00110f844025007100707000c504030121116052650f40b41c3e101d000b0840c285000c0b020315005002408601e0444c540702c06268040030060700060074070400310701c40c0300010880d0200c1c660010695410507062800b0008254051030341203040c00704070000090b42c06418440c041c410315044420854025034481d48100342c0e14020450030950b44100100200d1140360340948055401c5 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 937347715 1250 937346465 937346467
    0x1a0103050601030b0907020a05010516021f23010504140f011e0518011701020c4201170a170304020a0e011514090907140f070f050d18060302 62
    0x15010043c0c0003803003007500094000381d00d1010060b080fa0001a240d81c504e00c00c4001b008655a060f2100e447c03040c50903254001a00081c03e5402031104044401c175001c90f80032400a4406808200d903100c802d54140b031440800d030302400400141c5014400c070074402c1e10080307000b140b82c5480301b81901c501c50140104084010034000300c2d12440070302d4612101070314018045409507144c2c203003c442c1c0c1c0c1c542413080090240709881152501c00c0c040c026200341320941c2006181010070030005640d80604006880342d803444999401011000070405113100d5034081e0f4091604d54105201ca5410012f01c500c0051b956204444940c0000d03c244224000796000e10b9041d510381d19a440000c03084091507115144450380c000000c1104000d100c80d804540300152030b4440e000f4030344000c415060044240b2154001c4c41000003800e0780d40a00840b070212040300361643d103890113081102040342c00140c810b450080f94018101e007000020841c00c0180c0d01c446c20400c140c2c0b0b2000c2158440c0715006d000f45001c250b0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 937348965 1250 937347715 937347721
    0x1103031510090512070314030f0418020c1e0712150906020f0a02010e07050d050606241804060b04051e31060b0319020f13061709011a010305 62
    0x12041d442c0c2005010024030000c81c0840f407a010942d40c50403400300f6070700e51105800c01d1281140000031a54010005100241000d18260310a60100501340840202d80d8017002200101035007071000f07100702d09101082d80780c166885060f1915122481d0003094004110b548400c0c0890060700d00d007034072148500e1000c545040c040c40d05802030701502600002c0d021020600b500001e406400600785500707403104030303084145d48504004080d105c0150181c0300303030030100100781c50b801c00b220843c00300100c0310100080b115400180c580b0b55441b082d6443c0d10021906945cad001403404d802031800420003041560f0500b41000b001614540c1c0107800701d02c1c191440040a80284c80c0e04540b10b03144036040c600003d031510700021402c1d2002d283d50690300c00d42e01d00000466810410300c04c0c1c0c1c1c024201e42d1300c43e0500c60040c0c07204400a611038986040000c0b0144001710400f00f28200c8003010b040c2e1607850011007201d01440d079505800203000b1180527410101c84c00702e00d860648085503a82c800340303000f040b070341c03 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 937350215 1250 937348965 937348967
    0x15140114031f090b011211010c020f0906030c030f0f01060b04060e060703030902090f09060a06380406030c11120d020706020c0d0f0e0f06040e04170c0c011103031510 73
    0x10303c0c510020141000c1400009421010400c5940302d680142c010110184900004640009480c0300c003d6103c483e001400f0018200f551045900c804080c088801500140000901e403220881d810760580d071080e906142e0305d420a02585c0010500603480506003802c121024111781010810a4014600490408203040c07094005409881c0c01074165441070400301d031143c1d40d0340000c4801c1051032250341d0118904001500c03500044a03000080c80d142c41640e1a91948070541c5030640081070b246405031110039805120041000f000b007502c3c0001c2d411904c400c050455441e00100504581044100c90008041082240e180184400c401a42c0310700c20300e81000280213020740401d207403141e206001e0081d50814a044801212500c50850340a40342041143c02c103080c0b854541c001206010070450034401401060300705200740e0403400c1c480c03c4100d00300450742000054003031b5640035601e1503c295802440c0341c0c0752521048051440c41c40d212400c0c00d10442491507090080400d681094409 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 937351465 1250 937350215 937350221
    0x182c241e0c1309050a0501120c0b1c020d0b030d0203030103120f120f09030815010903141c120606050f0a0e01020708120c10050106020a030e03010915140114031f 71
    0x842e18500c10340401a448109020080c582280d503103140341d00c1d000021030407204414414000540c801002c20042d4100020410a5040443d00304025559510221382c11950743c001782c50500c10240c030015000d40d81c030081514061006405c0020340d0010001400429103020780b0341d800f01d040741000d040101e6162000c072041c1ca2900141400d00e40742040d61015001d0581290400c580a0341e00c0807566191816000103031400000c0c000e0128446550070400654120b0b0442a03001d031481c00d80c6d0103030404c0f0043c50f2503150000480c00005d60030490020b0a40490301c1124043e04041c6885401c2103400400916a0b210368032905040c081c3c078220346a01c5078800c00428001e0078641080e00c1c100312000551b00d0007500908070ba480d041c064140c0220b5429082d20030541228220f0f030080100320016141922043c03103801c0486d03095500d030140e0102242030000740a0031800c1000000507240545800b241e4040c90603000035108016001050445a800140d070b428145e07c10b01c6203404081d0444044402 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 937352715 1250 937351465 937351477
    0x322020a1a040f060518010306060e09041a0108030703140307080c0c070f090231061209060203190b090c0f0c190302010b1801182c241e0c 61
    0x10240b200100e01c4e03c3e13102c0040d2051042d60a43c85d483c0c1e8800034015030548046004540004543c3d0144840c0c1c0d14124a1258015004500002c040301902d444000010700c00d8200f06178036440020f48004055100c2e002e40001545000e0361819400c0c422030007040380d040540a40584840031960001c05003041c80f9032401030004500c1504042c4d07599031024042d40001d1903920740d26490351a501c0c40004030702000c40034040d07001816111203080c00810344102324a100a0300d80243c2d41c658290004c1d000344011800351010881100c07028610310307000401d03100509817090203108c83c041032200550410060f5a08001c10710380e85a03c5000402c00076240140d041d210600c00141c01401d4020706806522101607104186c0b024105a00400c4242d260b42c10288103211a00f80806060036400c52a50300c0100b2008101e0000c0c1c052520b0000c10144403c0b14103c01003182d04405001e081c00540c10740c000e196000041103100007031400070040300f202481d10310400c80c01d503010400680700c16801c0c0e0450310 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 937353965 1250 937352715 937352729
    0x121c020d0222060f2105090a060203010306090b090c01022a04150815090a061104120c0f1a030415060812192c0406050a0305030322020a1a04 62
    0x290511240d0000d040580188580f802148114280c2c40072544600f120600d28645a0040942d07008281c9844004001c0203000d071070240640315000d000600310340015802140a003901140000c09800d00401a4501400e80c440f950312601c0503000da6600400c070b08100b84c20700d03040c200700302203070b01c010356220522498241d511900e000035001c07a407038100030f40d54113855880c8101e13000e503801e0421031003540a0544d000f40c1c00e40e000344508400030701c0c41c0c0c001c50313585040c0140c0241401c0c0e440031541c3c134a8111031000c444200e440c6100340402e1442030103244c0100000542801440851180d00100c1d20000e440580241411181080c02e940b594004100600740c4104598820141340f611520325080400c2a1942e85495102c40341c0301e61081c16541003500e9803004406400040f00218000948004207151b0461340f01c2c1c10000340c6903103140c0d80b01d0003503000e0800756559151400e5485d11408203600510b1480c04280310600250b2030701e80303081c0152111200f65140350781c901e4600010b54003450b44485 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 937355215 1250 937353965 937353997
    0xc2c0d0c03060b06090109030b0717011202031005060f010302032a070b060d1a071205071d0a141c02030109030905040c14031501090305070f050102121c020d02 70
    0x1a0800c250311810404480c0120070400c1002801000c019061142051050010f21402c4040c8040b0390300307400440c0c100105007400c0010583c0d40b00c001c0c000201c2603222b0750f20811464003000941c10140710354092194440d80401c070074035114002402c694543c1d0390316410540d0100005114040b00100c04d543d4110388120783d4502801030052015951001600702c60000c3c45002040d55818000080c00940e640300200343c44003c0e13107403600d45210340000c144904101c0a120880701000d054401d040c0078124950b1410142d50307035113600503580c8004065140c0a40b141e8001081504001c0706200304800303040700c204100303007006078460050111420019602d0b5203048140c02c100b41c1c01022050031904280d40900c071043c00c0b00750545034440725526040ba180400c000180c0c0c000321b0707403170401c00c11034050502c14001e641326114580b80c88400c4d0095802070744040000e01442d078042082c2d1112481d015030452800e0b0000241403000041c030800031500700c0d00070170215002c2c06290151000301c40b00d50150 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 937356465 1250 937355215 937355239
    0x90f0204060906031709010203160816050c03150f0433091707030807051b1606080105090c180103020912010b0f0d050a0b04030516060608010f0c2c 65
    0x300004210f82c1c40115910003000c49040010390044040d100c5503031050b0080e6007004c02050203102c0c8800031401c11100c980c4204040e529600351201c050a20794051802400403101d441c0504d031802422504000c100007001c0c1c100b00150100d15682544213038002002c140d0b1106615100821883d07038031580b0100e101c8402146456034590740813000072400750701210248256014403283d240314800015002404200008417458002d500070032405889041341c4d03411442c451081402d1012114441001900221082260561003c1040c0c09404100c40c280414109402158424403500d400010444001001c0c254581c0c0039605903a40c01c82c000e05041001c00c6001042402840804146031007004105008442414600d4008800c140c1c04402404108070343c2d16102e2203281300070012402c0050410082d41e220503041c0c3d000781e2961240b44003050042c20b200000d42910b00755034042c0d101614080c101d48c492644029490913000d025511000c0d4000340021000d03442404c904d11681240040c229 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 937357715 1250 937356465 937356479
    0xc110a23070e1f06051219060b03040203060907060f03150b0301170d0e0112020f0f1204120e0d08030a0e070f0504050c0c0319170703320a090f020406 66
    0x165440b40103030400326020b5650040c0020f41e4405a4050800003800c2440050000c0c071004c0c0c20147c0017410710b81c41888142c1802005800d81d6840d411a944110022044c041103090420146410100030405080e88604080005045200041800042507100c50341d11000d10020000d00c40034021f03171884030307580c0d40e141c15100e41c03040b5661105101d00e224526000103070a00c00d291003007510318165180c07004860880102006500509003950030580e0400040f4100501000102030810700c100300d1450b00c2c0707083d00b401a0641c01c10b40c8c1150078020b1881a040d07580d40c41040390007005a0205100b51241c40d01050440248003e00c0e91203e00d20403240c004c654103880c803119030101c0320101d500b84090f80c1c459018103214005e44070711407010340c800e0180320120015410f60a211201038500b0b100c403c2c2c1c28483c210a822801da40708000b182d9244504607510843d03628a10340b040b202c0700c40d25500d850110200b09036003801000701c140d0668561600080200c001400300c100d80e001441440016140c4c81 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 937358965 1250 937357715 937357739
    0x1905030c0c0a030e130c050a0f030e160e010b03090a0f0f020d0b09120906090603281b0f080708060312120f131104050709051801090c110a2307 63
    0x151611803c10341410700c0700b1740140c4c0a004403d184980d200e909100a029059903808820110300c02450746410300581061001c001242080e041c10065282d003915040c03400848100603048024511420020450740c4100041d0072030340e20354850450081c60059081620608294504c000d40c82030851f0000d100344480c080c03080b80506600c0042c1c400526502600210500c14003022a400078030522a20781640b405d1310245500100708403503580312005000741c040308a410090721442060341c510001503042c8281d841e4555500e26801d01d41c6890141060207410614010600820401c642e40040e40d1901c007032046491010030101c0c1980c40c1c2220b540400c10011045500c4403049070010b000805500794044a18203c64000721014218000740040c40090000100280c00f1300000d442c00080544078123030142c1c2c1548103c40c0c031000550524001006491340000c9101c100104d508089086490100310a4441070740211610600c210300b986461a4110058544419010740311000a296003040 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 937360215 1250 937358965 937358987
    0x609122f040b012604080c0d050a0e042c03090607031706010203211f0b03040b060108160e1f0801030c0b071e020a0b0a030f050c1905030c0c0a03 64
    0x3901802071100842c01100c0038400740c607058000808801100300514004c51019401c40c1c0a018006c2c80e05203a5403c2c1c41c80c0c0074401640b0700016a0005038003601650002107045240070841d8280a880040c1e0849264007188421a204911404007000c151150030421120408405800540c840000d410007401000f0480360985036121b600b0f00203801917101100319107503912503480962220035024048400080000e0050341c8240ca0505002d1001d220010988020f007056082d8039641e140c07514110000090180c81d10781444001010f01020059000c804a00900146032030310586402c0b100040b01c0e01c01c0042034a58169840036580aa203901050041c140c9002d803686000103a540c01122030180300d500005030030b030b00c0c986094004201c3d280c11102c0f4071500003008c0d640301940320000d480c1c4580c4405500004070783d40d221405001601d50041c4d681c000300b05108141040c0100c00442800342c1340c01c1c020400c10100000043c48040540d00741c611000001d011246c410074140750252402c0900 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 937361465 1250 937360215 937360219
    0x180204060b0a1e1b0f1104050624160f03020d050c10240b040f0f08070501030b060c062815140301020d0e010b01180609122f 55
    0x5001144800700c0800b2114820500e5580c981140358480022000100c441e0b0100704000d1407194460100c01810b400c2c0078900d00074080100552907a141c10714004425180807400b55080c03004000f0b9982d180074070103802810015004c0401e540300035488800388203a145014010310103c103e181030114542041c00e0140c0709800316a51030700244010b0394a405100c10400c02d5901c561400785054406401507445034603039902500507481d45000050030403056030003101b1280710210b01040011600a48100245004111000c030242001b1103e61125a03030700a140c1819100e810000180e04c481e411950000b04107000d40e080da00305005101024241148100c7c4045540c2000034045809807044809000e01803000c280644d141001c0807210003144181294035541c24042e03907090508034060305440f600364000009403120ba04001412038200409480d12110844005109081d0000030f6081075070f01030700701400c00c44064600130240310780e4480c07000314211491403078141c2100000101250041c003 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 937362715 1250 937361465 937361471
    0xd1110030b040f2f040302150c0102160201020c011b0b18030703030c12020c060f0603010f0c17090304030302031602060f0c0d032706020904090c0b0d05011e060e01090306180204 78
    0x4c04500c540c44130200c0c030f500042c0d0030030401040140b82c05c10b2281c400b0b41010301600d040c110300041441c22a000236600c185030105104883c0c2c210340e81800b44020341042404c00c4444500842120082c42c041c600c2c00401c00314000010800b90b1800d5400c4001742994101141d50703e80781c0d440d00070f02810207007100c100440d43c001c0080417040868026a40c14000b400002c000c2581c505c1c0303883c040554040c10b51a01075580f400388143c140c49030700618441001c0340c0c40e010340390618465101c1c601c50b8020f02c0800903810500083c000268017200300d80407006100c18080c044a07590000407101e1107804d00c00ca950417000039008a11090110300c10711000411349042051441c5010084110711020103080319030402c4c403a00138001642a80906290ba1000e400043c03621095a10000042c0b8190083c2c3d03001c2d403001c140320040c81e1850250501526540055050000c50001d00e0f4401884c2809060301380000501103030300b940d100d92000e41c000c64018800380001c001181d00c9066034507811100f82c3c090340c1 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 937363965 1250 937362715 937362761
    0x5030c1f090809011d09090102090319080910120f05092a013204050909030705150606071703011401050304020a090216050715030b0d1110030b040f 65
    0x45548100764407681c110402500d400c02e448011540c6580105010031310a1165070f03241a10f031548801c191161140308001a0756400840425180901d003c0610180c0094202c403900041c04100030b46000100a0b40c4110010711419000c2c2e910b0100d9220340c10040d03140007410105008181c00640c020200b1005440c0407541e929800640380070746c150498040380e401e10241c42e403944900d500c04e0380d180d20a00011101566241a5020b405503042d426826090103d8103000501d0000f540b280c01105190042d0310b4aa140d03514992214409843c041661070039a00050007a02ca0008881c0070719400003400012100d20341d04118039400038004c40d110074101900700300c02c650050003140e01694008042030582d620b05288100030307601542510314062001d80c1d0001c006070041001c0009000900600d500f114041480103003282c0390128070911030440c0d00c0c1c840c0701103001c038800016401802c3e69521400000c000055019084a02410303410902e0001090000e0042c1d43c00032602c02d00c605006a8181 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 937365215 1250 937363965 937364023
    0x30203011d1605031008070e0103051e0601030201030c110115031202030406140c01090b07050901030b060403080304150e072421020d1509090c060306060f0806030a05030c 75
    0x24411030b120b105160b0307006518000395008401444d03100007040c4140980d2a141d0710541c0c1803801c20f5003da440501108018404c03c002401a05206a0420702e40ca880c0f100034001c007551041d0620020341030660382c0d040c40e82594403d442c0b41c1e107036800c024003d0142c810030f03e90701607405000d4401503c004e014910031004161022048500300c3d00e40b6074400c1c08900c150070f000d0000364070500b000c658940d03079442144000307151041c1c00361142c0910345402da2240c00040002d401c1e40c5500070014450181008180300090720b100549400c5a0070800110080c0702c4010340c50001c1082180388621442203180c0041c080b03c0032146032410580c038100ba944d400d400c611080d100c1c80b0100380c1288983c4820340740d050070841a9030241410004848000c03030840c146600c0c40c4952191508410f03030142c0c88540340810301ca017044c0c0e500010b0950703140c208481440e0003001401560840d1454040241c40bc01189060b90200900b800040d08001503039610f445201c0c0b8103070381c1c03440041140c020900718910841a8 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 937366465 1250 937365215 937365269
    0x210f1407020405130204050c13090902060f0313061b140406020703080a0203360102160605071b06080402010807030b060406030e190303020d0b031612021305040303020301 75
    0x400180009081004079800c20001d003d005001902d5403800b10540d0b405650b5901800b8050b0110b0704200b03946000e00080c4001c0901d4a80002031010309200404006031250011210481041000a5284e841c0c0b024040d034035100c60000036103014141041c0b084028040b011401c10b070740450311102c0d5900c0d004259066180124410800581c00038041000403030070100040110758010300c103492510001941d600940303840e0700c40d8503031080054866041e84201100f8001c08045007400202003a5203000c140c1010240240220000c00002160003410804e041003100200394131480744100c5a503e513100107200c20800c680581c000703020707140400c5072240280304150890310060322603490f203818000c058010744192580341e51030307114040e501d00c05505403007a0041e1061007598003603030300c400710b8260b80195900e0806803807283c1c005092400a948141010100300c0d000c0803410b0a079a070540c000610540c50403110044464208001c020403d507140c1e000b03606803110039100c0450b42403410400650 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 937367715 1250 937366465 937366487
    0x40c030612260a091d0412050a02010908040305060609010b0c12030601050910120c0e1f020307050303070801210506040b04050c220b01020a0201021c0c210f 69
    0x1c0e1610102100c0003040308403003521880380381d207002c1888102c400c0c041c180c020303481980003100046000d14144041121640841c082c010b8180e042100d900b41525403207000300990002d003051080c000382d188465070003900050700a5401c9908581c4965590800740d40700c01048500d00c0c400e1041100101d400c0c0b5007042034400d42e1141100030860000300011107040342d40007800b410305105081c0400c1d041503883c2c850034078000741c40f43d0703d42e0341c1074002007810000d03130b8001e4055a042c03145003040d04110741c4072134403c9003507040e603074103412250fa0000c01c040c2e065100e04000030703140340000406c104109070030110030340c12107100d1420103004d14a0040d1900c4015004a0014400d82040002ca004560481d01d01da400a02a20903207a260300d5010020308010480303410f90f01c600140724040300c0ca92140c1d10407004011801e00142c002c0705210342c0000d4485500e08a1406260500003000d0b2065101c2c218001a0035842040c1c8440703001d035502206503140010700200300081030b0440f0199118031403000c0fa19 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 937368965 1250 937367715 937367729
    0x20c090c121504112a0604110f040203040602070b0a2f0408010e0604120306031e11040515030c090618091606200c060315151201031e020303070b0a09020a0b09040c0306 74
    0x104603100d668032300010080a00e08680c0c0b041e003000d0556419a124401140182d10401b40142d86421518041c40744060040c01c03018914545800426a00345e144000c00000746100241c07064911080500700550040742c218102561030b02074540f580e84800070310207000714020038101d200c416248000301d00b40d52460200074900542500c0304868940b1141c1c500c05124407400802d5134000c1c0000c0481c0c100d4100300c44e90100c041143c90110807505040c0001800c0a8096850380f06034901640880c000e03d02c0080c01d03040981c2d84000040381c068007880b084800c014000001044c0903610303000244030001c03082403002411012000d440e000000040c04100204000e404907043d50b54004085140b00b001c011038542081841840b404140108401021085013014030901294113506007110354200c150600304061030090020310250f80c0010a40b05501c0d8071558000166541ea01403c0241206000003508004180d42c0880e1201b2904040c0c816800e05031802c000c80d2020341c0c000c6054481910507a8 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 937370215 1250 937368965 937368973
    0xf06061f1d0423070e090903030112210933050c12070804080717060a09020f1801080f030a0c020609030c0d080703020c090c121504112a 60
    0x11507407880c00c035522541c007400620024903004001202145640d02c110401400e501110401c0400c0e50000200180032400f074545001c6407070440401a52840180669151180c40765208020010301d4901c41c0114000c074102120401c50820b00a802c007401b6014604c1102c900e2919a844402d107550401c00441c03600307124141150640c4010b40e01a400400c8000382809034410b1070742e14103e07540041440070321a1181c0703655070b0300c0c064000c0d0500783c00c0c7c0c00c2102e03003852599081c440300400240480d044410050001251081032000450072002c41241c15007003200c807403a4031403194200200ca412941c180f07040c0c540c04c000480d049038480c8158840680441c50003412a00581072040207440f40303810207001c4035404e400c4180010307080c5c254000122183e0500159460030154117103c04031022200380c1e000c09050900c03400640990084a1001c01c1100d6440d0006011404105c42c1c201c1441004d030040110280e2403d11900720b070701c41030305441580c020344045c45003440e4a507561201d01c00050050 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 937371465 1250 937370215 937370237
    0x10e090403170c190909060f0303050307050d0b0406080c03012004031506050301020c0a0501111e090f060a020304090b09040308011a0403020a0b04060f0e09060402090102010e0f06061f 81
    0x380d11a0006002d0501114084c000d400150a140040e080c42500c59250440028500101441070b600c0340d8200c240000c0e02110304000080d008001c1d00e03000113107410321903181e003400c1440500404460304120340c45800d14a00142c028804900c60689540035002440034055402c3c0300350f41801d1106082510b0b0a08000401c00300e03551503400d00c0840407495011552954680000b420398111007034442980d0080d42405c41000424440d80159140a120345400d01d40d2244680d9001c4038070b42041103000301c0c000303528406617990822401c00d042004141c50786031045204000d42d6030704203020340840103240c00c4007400c541c41d014400c144103560680d0f5044642e0b003000340d100e00d03070703841c2140c03c04c117000c02404080700684d51204241e010f483c810240d00d40715494003000410501c81c00d040407060128001c01c154061301c0c1d450100c0e900038404d6601594543d240701c0100c0c01410840c280d180d003400303007500001e0135043c0446c1c803e00440c4211201e04609a07414846c4603005030003140100400c1c091440 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 937372715 1250 937371465 937371497
    0xc0f230f0c040c17040b07080906100603022503181d04020f031204180c05160b0606070b0a050739080f0c070608150d0602030a02040807090b010e090403 67
    0x144080c01840c0342078039500a035813100ca070030707007400780c80840d045100b00d8204510544c0c4001749940c400040c5000708800c1c1041103907a40c10000c5405071a0815400007031f0070300c0004541241138920111106410582d42e01403e00800c1401d00300c3e02c0003e8861143c200180901407071501240014103c000b49141e600d80c2c1d401c000039040100c1ea01a054050700351061403009a07140a0801011040d50040100d442048050304585090f000c42017889018810003100e45072440c031800b640d42e4002c1d040141c0d40c54a4000800034010020010402c2c0428400c02c04400c05030340105005015546440e0350784001e035114081c4a480c0e42000e141100c40300540542901d162030785082d1107501618a451410000041d80d4038184d0046444e114075501140c0308100e03617503001580990181d44201c80b0080d0100c02c000280904070441405041c40c4e030040040380241c00154110b4000702a90004c41d083c0568400d003c0000e4000e5604c803c1c0801c0801c000e0820354280540581c0c465030b8503540782c0c0c42074024800c0c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 937373965 1250 937372715 937372721
    0xa090305191a0a0e0708060601200a0318080316050709060e150105120a05060f0303040b0f1e040320091605031f091e0e0303070503070c0f230f0c04 65
    0x8460f400503150251405104814171044c409050401c01800031460054009880c0e0f210040c1d81100008007501e80381c01e11480881c07040411a490310304034441400c04402074101c0c0e482030b004031000b07010028107114240103c10310340c0c01ca64410303c10303103100f5540c86480e86d0842d0f01d503100d0104042540400511100c41640800d950580e0504000d82001d070360a55801c241d400c00c4825030031080d0303644207010b080d2803e00b10078032a411040b00290314050074091040d00500a03410a510f6803840481c460901c51b80724001014a00050030740d068640b0740e24202070006158844001c4c4412030300404001311800c2c8147c4507482595400d07503426880140041c116840d61006010702104444403908031500c6d41e1641c0c1e0000141000c450124580e0304640340c240e0740385a0702c41c0403540c541c501074030240034144c00300a480e4016072605010384c480c2e450306001d9076454071660b0001e01222998405c4010400204920000029807902c0c000a43c2040c0c1070a0390380d00e000390a4103009502c40b590150b41850300360 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 937375215 1250 937373965 937373971
    0x150c0a0905061b010504060203041a011503020a091203031b08090309010509060909090706021203092d012d150b090d140c03010b100e01081003080a090305191a 70
    0x1001003003c410440ea2080e00b182d400b5201110519000014402800440303844440da04040a480142c0707035241c2203000b00450401d1403030030103164020503030392542401403c903a80146200c00b6040c10304442403030001c009101c0228001c17804070034540301c59025481900b0040c81186070900651500c100e42006591030380000c03003081e40c454001c10241b1201d03100c540304ca07406840707080002d08116041150103802c003007001e2050303100f4000a000708500d5840005180740341e4507103001c0c043c00c441d060761044140000d225421480a60030000c00e84080e9581c850755104400e40950403108458854101c00c01b603842128400e1205051604148100b865010090031b50050003020b6a00c04403a80da103803040800100070201c000d41090710f0281c1503040070302811010800c11115a0034075030f421600a001104100d1146040011410005000641180c1081e02845e041107001b600d91121900080182d20b640c04125158026806c0c1c244d0b00840329039441260540c80405440740b10740940141d440060f0003 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 937376465 1250 937375215 937375237
    0x6080f1b16031107150c020f04060b0a1e11063402030304020f04060b03040f030c021c0201020d1d1210050106090e0603120d090c1502150c0a090506 65
    0x400944040c803800840307540e01c0c94440c0c2c0b6140241058044a03071300300803480c0e00910f0500c4400c659400c0c660b9110032220865039044a01413031110080012600030443c0350000c00703450000043e6505c1440d0010050581c40207422074414038030700d60403c12074900d0f086010401c0e01b64420000714001d0440310b0462402e210020ba9045104d15103400c00c1402ca200e070746003a501603080042070009604000140540008054030140b20355441c00703005031100c1c030000388060700440c00f600018040512940c1540f148940003002d80e00c4031b11b088101310302e664140310301c100e0141c07040740b5244000e50b0040018003011048000404e207258401020700c40711440c0c203032210300940180c450741c2e004004248141c0c1d018040c181d0b9035082c603500300b168050381090b010344024400d030b200700341c8407080d54180c00480710300f00e90032080411100950300c0d10300c10750202d17504901007010042d80c0d02c00d1629400100403261050001308076280d42c4880582209a2044038140d00029403801414440c50400f0002454507e40f1 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 937377715 1250 937376465 937376467
    0x120203180304120605060d022103040e0c120f09031608120106080f070203090603060f1c03021c09080703031112040b0a0e0103021c050a020c06090d0906080f1b 70
    0x5010001401d540c41a0041420100800c0240d800c0c42078610a0913805001600c803100410030a40004044a001c5d45500740100c01c9400707184074200086c401c1e6001801d5440d6010001d00b001141b81da40d6802009080403000054000207002c401c026500600030180b04002d980303005103044d03154500903088007050380c0300b2504000071b004001380c0f5a110f5009188079900c030522810001c541603164070700604443d04544c410320072440c1c0da596002c1100d42203e8211098201c100107900030401001d404100b08841d000850946024140c0124008106080f82c030880715140103040025500380050340100d150540c004141440024003900c18903204090040c101c030b1740f16215081d0b41c1800d074002c1d04004104680402c0b405c000580203030660740d03040c2c0c09080c103504100a50441c50134450b00008450711031600d0f00702144040341c1c1030b811a01d044040005032021450220030b1541d4420100f9060030025030381d00da0000b0340030f00c14030496000300440011060140c9610744d04204003e2000e03461040000 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 937378965 1250 937377715 937377751
    0x50408340507032f060f090d06050f070221090a0b0703030e06100812030403020a0221102924031009050f130219060c0201031d07050d110d080d0b0a0501120203 70
    0x8c0c5401d185140d1512410303011685182c54200a002d2110107400082594842c0d5250580e200d404032511442044c2c00044540701d4400800250040c3d00c9980404d41c1c503000056450180340d85a000680d4044501c41128040e441d43c01300c1071030750101403180724402d410030901c400113045000c0086d03411600a1040314400310554001680310402100004070001c840c2a01301030340141446070a0041c5d020a10420042c0a00c0c100815024000d28125500d50003c850540140d034a03154001480c0c01c0d44503d015003568a09890b000d164425200301540d840c91f40e1001843d00300a015641c41090350000300c1c7d901e612050b015040040451000b01d80c81303142c0b044409281e0820303c54100c0202460740c1c840c00f04040c1c900014044a40801c01115144603c01104c030a07401d00103121005c50342c0035560200100b8442c10418800a101d9032071a90000d0080e01c1d1406206901c0d01400c240c25135540b003002034900b448100b0010303541e0742c1310780c0c3d010a08030100d03554502155800366030f004149030001800f00c0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 937380215 1250 937378965 937378969
    0x30f060b0309070e01080105040f060507020f10020430081b060a290306070e01030e01020d060602100504020d030e06090a0305030c01060603050408340507032f060f09 73
    0x28000b225902c1c100d5009480c1045504410400b043c01000e000300200054102622403503403901c00c6600140c241034541c03003c522054030030000714072203800c2c030b000b41c50319125440e46e030318082d6200d80720302c1003103903441a50181001600809440d8980300034074120900010385d5100d010075002046913540e000c2802400300390800701803014510484107840d0004001c0a0a484160241c2c1302c0c030181c54100d018040001c40c1c0f03440000305141c1212490508001a444400040b0f026010380700c5d07a111154000300b900140720120b90406401e47c0e8a0ba0207594101c081c4030400340c210790781150060b40c401d800c03c241c080481d000d50307500807201c800a884145410521070205a0b0803007281c0c401c8549038800140042401d4003841030070040c0c12315160620550420380c03140340722402540d43c113495141940c0c8207684245e003e030424007403036100359034810446605418010f03260000d07488192140040e40c0c00000e0048540300180c040740b00c0c5444108444141c54003031110f550440a010741500e102001104c0c440c1d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 937381465 1250 937380215 937380217
    0x605030c03161b1b0b1c1a0406030b1b03090d050702061b06041b06080406021305150307030507030605030303130201020316061a060918070e0d060e0d0e0a06030f060b 73
    0xd24082c0c991818130b901c20800e190030203071180c1c0c0040901c070310500c43c0e003407241c45600c503540601090b4000400e924480e03201103910002c030140d089071301a2401c8000020486101c0c1c0142c400c4684403200012001100c020000394402200e0341c54480d00581c0341050403a00406c090080540050302040c00c115016030000301c003a00241d00d200035940f09104000401000e040300c00092a01109580e00091514a0103489410040c000614554010803c681000e90020342c11f4000c0c40d004050000d02410440c1c0184164420389181001030f09010008554074028000e207402c9400141c0298650355500c0d0520842c500440805c904500040142d48001c40001080031041806440700107410103101184031001807218613210b000c0c80050006160603610111030003141991031202e44820317030317664004079902000c80ca42ca1780d0001e111002901402040c0d80610050401c4074200c1d1a100c48071481a920360f0b604110069110540f61014080c2501c00d402200c207600820310702181080d215500018030b = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 937382715 1250 937381465 937381517
    0x150f01090c12090b1b040501020a020603060d0b040b07030b0105090f10020f0f010c02100c020d1206120803160c0b0c0706021303050c0312030105010e10020c2101060605030c0316 78
    0x80070111400c0c440c01e9803010021710840403040450034646403070800003135210005100080c2c411480400020140c0d11907034080051241d00c005200c0a0746400c0c5080d50010905690202c0080c3c43e08001d5035565010b20101c4070043c070300030101c050000c2e000040080000e10641500110b001c0e6080900c0c1210301040140a180680c0c1e0000c0390340c00d41003500078034105141010f0740d885410502c2070480944c000c40c20090441a07031a00c408418a080e001d60040c1210385d1261002d0b40604241c00c0900c862800a50f0141800184603100520102002c071034503c41c555001e0401400701012030400903c520040100c0d40c400c400250030584a1811a191a50194001d0f41e89401802c1d1281e82d5140078007408032002c0c00c4140c40c0c3d046504203c0020000d02c0d0b1800241d0280492881d850000d90080015210710880202040d031a6002c00d2442207540707428501034080c40d070030124042034441c001c00039648600c0c0d0000406040d6038440d2a4049003000908145090220f07183c100042d84000b000c0c1620 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 937383965 1250 937382715 937382723
    0x190b150d20040f0b0f0301150e040305041701050118090b06010e0f150405010315060e040b06041e090b060a1b020d020d050a0c0f14130609021308150f01090c1209 71
    0x91840700804c140602c010404200d24031a034546030002d05c60341e2140e40c03000d080d42c02041040a083c0e0316443c06440c6486582c00c04105c41c15590300c940644001504001c1c140c1e2600c02c503501818035060003c00c240ca001000c01810ba080400004587e544036809031282840000c0130b0f11007034a0700e80d02151421201361040050fa02000405100350351b014000c81041d41402c083c00300c034207843c0c004010030b15491040424482c549483c840030155480d413090341c016181c402c0180248014510690000e50a2889148400fa00b0a5842c00b0117152141c2980d0008902d5110860300c6045004155104c046500040340c3c0448151401005a140c614140d120359226100900c408151400e1801110b0060392000c2481e0b2018202481920f94441c10603404420a94401100c0c8044600707180107400c80340c01600000384041481c0340c04040c0c5980c40d4046400810540d0b200c19144c2400d10700c242c90442d02d00340c045610900410040985034040c40303c07a13034186070030303100004208990001e865030048161 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 937385215 1250 937383965 937383971
    0x70308040506060d02030601030f0305040f08030901110313050d14030403080d0513080a050c0c03120a030b06070228080115030308360708190b150d20040f 68
    0x81040002c12100e030300b1000440b4132018069403a8000395546105000051401581c1c80290003007500410a480290800c2d4140d043c0d4a40c071484015565045050f210740003034000301d881800f8030004402c44003900310168010032030609190521000b02041e5000719234004002192540780c0d01e060028002a520502c45036031b99583c1c81ea00302d0103561002d040c803840c0311021a100300000e81c00b402280d10702c01d01c0f0b090a80c0c0702c0159050315800c1003e201c0015415010301100040d9885820b4000d10440820392170411441a140091044902a2242c02908030812001c01101b240b50105e0119110564840c00d1032890340310920142500e000c0d20302009840200d1100b8401c1540080321203a00890746a4603c0190107c185c0d80083e80c00380f520440d200411440c00701519650600c40d0b903018064220448640f000c00341009100446100030540328003841d00041004080c03403103100708500100030100c040c009816140d654041c4841030280c809100010000f08554407076008403510040800000 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 937386465 1250 937385215 937385221
    0xc05070c08010917030c04090513020d0c050118080a03140d020f19020d171b1b1504030e1504030f0614010b0a17100b04082503122102070308 62
    0x9140a03040320110034440b0800344200444c4e00341d41b40550b0104ca038010808242510340241590010790303001c0c0d000e500040940b41040612468007200001c8410a99488040c00100b04e905201d80c0d149005d601c415400400d07002c0e02007849200c24256807030718021201c1c0b0740b412060803501240e104140005400700041142c21303020200f01c08181d245003043c00904081400c4043c014075a0580200d048612010000404c80340d24403480b041080070074010742141e6500c01e03a4a00080d440814000344694441c1400d80344481050707003c51801a94140c8400ba00d13507455804024124078136190020342d10405200000215030400f9080d010b03c0c1c000c140c0000d050400313104040001005800c03c1080c1c150812200b4001e903800351045130080c200710200001510b9071032550010758100e034426442c844004c83d0102d00d140c0d01203411012100c801341c050300b440354040e41d40c01070f04d0001c0c80081d1032003c0810032000d900c0d025003041d80c5c91840c1814445071480c070200c803d100f203030442c070400d400040c0c1c2d041c20 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 937387715 1250 937386465 937386473
    0x12120c010e011d0307060e01110a0203070c08150a23010303200624060903030f1909060504060e031204140922080d0e0d0f1e0504090c05070c080109 65
    0x448103600d664601000f0202280521107a481c82001c0e001401d1550b104a0390340390140a6000f10800e0500700e00456a422096000940e65004080150f803040801c45000841210018150074480710703184403184143e441c9004803000b481c5e4040b0031802e409881c00c0c0d000d01c0b4102222880d018605c25203c4968000055072003580140003070710b021a4aa00441c1404a03415880b00711a4009003048401ca00003509403020840e140212480c09405200114654802c0d464000142410f0008070449220300c1e00a200111501008c82c402c41011850421090021a12a2000e103103d014061b0488074407207201c0050b00c0d01a07200790b00c226000301c1510104e036618a0410100d94110500f036004400c86000440392400280c03008600070510100002e50740d0001e0300f9070704000e441b11064400c1c1c0307442e080d0161000d0200c03250100c1520003c2e04048019040d5802e2040d15603805420f9902c4a0400341020300b0a80107104090703017142070180a2000c0d10000d040007040f0380150100000114021640b403070 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 937388965 1250 937387715 937387721
    0xc050405040b09150106320f03041502090108060603070e030604120f0521100f2309070c0b0c07050307050c0109120b060d020f030610031202030a0e12120c010e01 71
    0x180110741800c4c81d401040202d03481035040c0d550b04480080c50b40000e022403040b80000308143c4000d0000000480e81543d8005040003542c41a40200320b2000301c0416000c11500300e11507100c08a0125050502180d8071707040c00c0c030203150b01c0a010705140c040d003060200007920b00641101d0848102c1800010460a198482c600e00b0b5254070a003003490903c1800007803c01e03410f08251480074080b5110001503500d801612162004000301e140114409403100000c1d07030001241d00c1050000382e05104110180c0c204641814071070b589940c1c914550281d90358500007071042c0540f0000c103424062201c032000c683c0610050000a225500510610000c1c1d8005401302200b84c1c4910000c1c00b0803201007012903214241e072603102d04121901154014507200040d11001480c0180e50103100c1c0d401000a0b01a5182c03a0f4010f1301c2c00340c0c65190120011150890303036446103103003c3c1f0019a04031a601c0e0542403160340740c07004508030800d071036034258800910101a000030032819101e81d117803501c010b01d04a080c4 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 937390215 1250 937388965 937388983
    0x160b04051f09020105070807031b0c0503061303050313051f06090c02191419110a14031002031b0c0610081c050c0c0405012c0601090b070c050405040b09 67
    0xa07010300000000d030300040c2403800782d160301134103042000030843c0405102d03045020910f1922100380e544988941006002c483c3c0a000e021f000748907140125a0151000003441480e0390706540e100e1466a0b1100d81d030701c001048007070484d03441c0718210441c00c114810706200500c4000300000016000d00d04071041082d80c48100c0c052055400402a11040c2c40384c1044215402d500042c4005808103e000031600e80b000d4407041c0700881c208002042e041064548100c80c13140720482d9009502e075260a8030311051800f402d1074980c154030100b0902c130b51880a0700515400694180d104405d0380040008075002d40c016102c60f40c0c3e540021041201030b61803440c14502808890340207201c40344040040382c0e01c0100081e1010140100800c2c40701c02480100a0b4550380e0301c0c00741c814001540e40c0c0c043c0307400d0b20854a403056588046540d07103602100c48100c00c184141e40580d0790b18032140c40c21010014a5000442c10344041d04010310114840e1940e01442d400b4a20914076440c180c90000800fa0a2106030 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 937391465 1250 937390215 937390273
    0x70b01050411090d05150f070806040626030706050112050d020d02031e091003050a11131208040305060c120c07020a0b090406090f0605010f050406080a02160b0405 72
    0x2c0341c840d11010314440305a50503000d0556152020340c815041c2a854854288080c001c1c00e86560104800c19101000060240e102901c8581390307501d412081005480890148a190f800d10000021042d2101c510380340403803403650180ca20b002e0b2951624000e9507000d03084001d44500003c003140401c0070030840d00c08a80e1044c4003070140c0c0451000000c0d140e11400100d58200341d048541e02207000b01a4045500042008002c179140100c00c20000e00a800c00720b602284191420403603001c0c03c402201210001c1d070991201307288840c00d00310301044280003120243c030803c50030311010002400400c510b50180c0e03941c02c0c0c0f03180c69044680d040544910f00034100300e40e60106001400061716850380307890981d841040f00720744801403040801d008151f158400f1109604040d456080117803664800401e403842a80c405a90081c42c142c1aa2184030364407a581c001a181400250200f046a000c0c02030801c4030354614501050a03180d501105001f81c4080d5103981103801015074070b8200040302400e442c42 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 937392715 1250 937391465 937391471
    0x15091311060a090905100503010903021507300608101e09081c0b0406090605030d0207081005130206071b05040506030d05250b01090c03150b0a0210050705070b010504 73
    0x118100040c50884548200c00d0780340c1d21000403072031b84082681307a03a01130107002d4000c000c1c28140b03050003940c60750030115155402c0780c0e190201c3c21092082c510b41c0005c82c0c0d0440342c40a800c502d00c1c840d5240210304007542c81d2155980350301140d1100c3c00d0200c65581280c0d400c000c1003003401c844402501d1001c034804030b0078440c80c001d484800600d200055441e0b160140e21294283d0410604513009001180c0459278054036007003000c207804030301d6032291081d240160201d4040000e4400166950502c90040030349950256840036000880c83c0c1149602c0002c103a00c191803480b1540c04282c10350400c00d012551313000880301e1222a50007d40f0944000c05003183c0c1032001d8140f041c080398540c0d11040200c4100400050460040300c05504820084030101c0040d481414242c18030b403c45000a01409001d85e040c00c10024066200340a0400803080d00c141401030356141400207075856025410b01410342c003680320000c082110034411148100c039651203407a95446103181440c40030005800044c031480c9 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 937393965 1250 937392715 937392727
    0x22081308060103152c0d020c100903020d14011e050619061d09010b030603160e191401080618150406230c12070c020f01081509131106 59
    0xb08001c1c5940c0b04c040000082d5081e040383e0940305062080101813811031090584403440c03030000400801c6100b05030f02341e8800318150f00801c00000d1906108000181d14180148003610b000c000c0b02043e0361040f25006a200144007242e801e40300d00c03401912074030003c03422a00140c1842d01403160302050803a4900b002c802200000d10741c00d80140969010451117100500440105401c0c540000e10010b21a22803582d450a82c070280750f1080320304500234042c0354440ca480907021203044080d20041ca0000030260754210440d40140d061002c5a6403d5482c2c0301e08805e144074000400d170182000d0b070b028001c1d904c0d100f00345101d0b0846a69104d005540050600a0b8903402c01a409401c158840300c08600310075001d85502039a039110f80001b1100e1640d40c03c3c407941084180080c004801c0342c40303000000c0d07510200c0545481c1c021f0580650444c15282c056145580b00d90401030303005900624061072031147e800442c40b4520300300c0f0203084154032802c0ca0f03c2406286644460500c0c0b040721004c2c9440 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 937395215 1250 937393965 937393973
    0xb190c110d181e0305070509150114070204290627060c0d09030c050a05010c0f1b0f0f08060c0d1802040f14060114070b22081308060103 60
    0x1400482071000c10103044003819850303820081100007014030061080c581d00f01c803540743c08a0fa16a210480301c40c41059000500d6007040c4860030300c9522261003010000c1e00070f900650360201d0b41480c40445080402c011001683d552003802c0c18550050701000305880803205c1007100b5014045060b104250600c01d000d03004000004a642e20390803420038285d600a0790780402c4850281d04011842801049004d25802e07a004210000302e034015290703c14280c0d6100d0034050181c1d60b50090900041c2961000004100c08070204002c49214414801030940c0601d00422413101580059a48840c40c01c2c080164250095034000580040000782015040922800c41c01d84a214203c0c0380f80e42c0c544241c0d99224042c10070300301115802401c148038400710070b41080014055014101c00e5100d406001c94032a52055030082002030249823428035185140d01c44ca90b144800178079040c0d02d0850a1503080c4580c250708040000385205040140d252040e45c103801480c030806800aa07065440000100046 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 937396465 1250 937395215 937395223
    0x603050a02012c040e070b0406021b04020702010507020402030402130f0f050901050906070818060c091e0310020d09080a0309030f02010e030307030e0f1b041a1e010504030b190c11 79
    0x5403c2101c001501a040542d0a800c05038141e0108542100100e40040c2994000c686283d422034403660a081403510842048200d01855002900080d0240502001410158000d54005000078421071104520581241c2561001c0e480709401c56200e901c0b101c1c1d20307107890280300d40188000009001c1c40c90851a260b1351540020400c1d000c00000c44085010210382c0140c8203c0c8600540659950745048203012820380e022088180c040c840d85c50086981e0700b040d403110a00c00e02c00a01501c000d45180c40000081c1d04901d86110728113648032541800110710200404146900d501c01080c403007050300f0050030002d000c101c02029a41020642035804801100716a40920075082c002100c04080400c2458003054813002c3c8050321035280e4544e40106d22250f0105005400ca40c00d100c4900c0b10360100520f0070b0310141d480e4001a821060781d0888000500c00e10704240185002c60910782c0e245c403402071922081d6646181b41e00c840c40195801552402000169a1181030024240358465911030759 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 937397715 1250 937396465 937396547
    0x140f030d0f1205101d040b07081801090609020f03030a05033c0604060b1e0f25150b03060a09050c0607140c040603170f0403060603050a0201 62
    0x20045220300ca100300d540142c04000c0020860402081203142c044811000c0340b0b5540a40121016205055205d403150041d030207110360b07400072196040ba22040c100340c030055400b400c58100381e131925410f032a44010134440d06d40c1007805100c0103c1c5568860043c80f004a001041031070080e0004c11210440300c6d00501125044100e07031201c1900504000701843c00d04150280c400c00c645401101da007116054004401c0c0110030403142041582c0e5a06040000762040048240403105801824210008120080c05401c41040c80d03207440d24840a2904441c1001400000c0746050703000743c0d850034000840640c03203038071782d0051040026400d9040001e40e6214000e0606c4212515011041c0c10442d05009058031404040c0c4140e03210415841c040401c012440c005a500d4491081a074a0910f011300a8404494211985c5203002e030b6102d0008800e41e03c88082000003880810001000840a03c590b00040d4095000b4098000705440010a0003403c148102c410301034480d41d100e00c0743e42d654a040a = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 937398965 1250 937397715 937397717
    0x3010e1005182a0d150b0415050d1518050f06040c050d060605100c0510200a031b0509030c040b0a090b030109052d06071409010c021306140f030d 64
    0x1014500b9000703030700d4030f0003444490a90002101e100300d40c02c0000c400120824000850000e0003100c07020020300c81112034440906682080300e40d800c000d14284205140407244c042c10040d0f1410b0764401c000000e81d22901240101c09161440d41350070710009212000c2c40030620360103001c150409440340c0313040c91114003605100d0564090303804100401980024002c140260096503c02c60030a00a0300c1070041307420a40d81c600070034044100503a114812503460745c507203580104070b51420019a180641003850001d06140d9a40c03004007141164541c22b0b15010510b03590181e846a5810900d130500e01124002d9019034140034111400f81c2d0742884050a5942d0500300080f0b92440200003400b40c0300b45040500355010300241602c00203014481d1a07c02000810000c84151458000ca6940d841c211005400901501095102c0702840c0e0010302c0012014504603800c0c240e031303800103030050a5008000144075503511081195602088030410891f0040320410170710540d000101c0e4880000300241c0f0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 937400215 1250 937398965 937399003
    0x1201090e150103111c020307030b0402060c061f06110604060c0c0c031407080303150607030903021002010c0f020a08090d08160506041505090d0f020c03010e100518 72
    0x80da940e007001001a1041005100846542d503418890f00001022405034003c102d500001182408150000e2400641c0a0000c104582c59502d4216001e940604200d9115108002890648404112550280040c10201c07003601c0c0501c103d40b444004c00784d0010007400b1188151042c002c8000c2245507109400c10404100c1c0550082c048500c44041c7c44000d045100c1c07460007000780300c0c0d0381081c52403141c103100c01c45400c613440e0000300b90740f4002105c1d11125045c0c80703e0140003508000c405461501c0c46802c25011490f101c0d40025181d0b52504a0b202c0140c0d0b640410104140c3d1216000c181d481550000e40f00d503070090385035001684901080140151074000c004000c200440c4215144440e40f00741d8119102c4080c601152984415078068070420510b0400e48031100f41c9205446c024550744000300940e500b1106e041d90301f85a4440c0b12403e500036a811007030b05071401e00621076070690840c003410007050154580000c494002d0301c4640c1c02c000200c1550781280001038a2844000220845 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 937401465 1250 937400215 937400231
    0xe0a1d190c0911030615130303050d1103040305030f06091302060f39060606031503010e010e0f0f0703080a08090304080a03050903060604090209010612150305060609010b120109 78
    0xc00c0c0041c80a42c41402c8452810400000c0d044070030001e54000d0108840f0290000480702c44140b141c0101c01003402d41d007528100c1000002d002d03100610150181d04004501d20b0f40c1e1100700c0c4150f8008a4050300810710000400c158074450450456004000700e904100c03604040da400c83c1c1c0000c2c0c00380024000c2d2000150318125a0004041d10b00d0941c1c0507484003102c2c034105440b8580d25101c011a03504414032080000540100400c400d846484003900080c10341e90380601803d140001149c1c039a030595030342d04100c41540000e0040010389055480100f4469542034062440c10b0f90525801c0519004074000303000184c0c400c01115148403007850044481c0d11203801603810342c0314591210820b0310404e100e4800f0150804044c0c50900c1045013942c0f055a03440c0c1c02c4c030043c0c980c540b10095002070040300510406005040702e0110307500300d0a00040c45070070542c5280034003440e60000d64460f0702c05410415030b4940071030300382e025103400c020b007a00304010414240300c0c1070340600480070020745035000 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 937402715 1250 937401465 937401473
    0x61211180a0e031207020703120e06160f0c030818091308091f0315060c11040c021e03070b070c05071a07080a0314010501030b0a140a0b03010e0a1d19 66
    0x142c1d0b5903284d4010010006003026000a5a281841c0c4012100381c84581e01914855002d40d58942c000d0102801d95450310034107140e062800c280342c007812503210010780c1454010505501c41e00028612400c3c0d015074035507400451520082c2d4a80c3c0071841018083c0422500011500810701840d5003d40072585840d81c02e80000d40d00c054400c60041030b00c54800300355081c154990004503211007102628000b45440d50400c9804480460340a0011000d0400d00003035410a035000900c1c0740d281344140c50303842020344900030004405080e00b80e07441c2d001140c09018480e9644071940c02203510300346404003107410f9942c56118992803140168552411a044030745000748030031a4030241d441240c5541d04d102c4604040c00404503080440307110a42040003080c00d502a100307045c0f203124000e11030100c0a00c1d012099125426068003150880481c070400030b5202140b4014501821003003244801c51320700764200d041198420f041c0d03068404030001d92603845c44e8000c43c55603014042200c00111b4918207080c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 937403965 1250 937402715 937402717
    0x30305040e1e0f04120e010f0f03150602011506181206090b0a050a050f010501051e0412120201150f12170a0c0b1014091801061211180a0e03 62
    0x2001c00e8510030b44204007080540b604114807840c07050741003e51400d54444100d41612a030001035001c01c80110143c41440d000d07000c00d1550015902e404101140c0054207400c840c2c016501c0000940c0d103400c45d0720b107074003040d45c0800081c0000c4e10304000754907185060142c60b100070f40300d9011042c031a82c00660030710035982c2000343c60325003001c918174060900b0340c3d2400c000d2204030b0b054a426890603001c51100301821104030b0490300c05a499a00340380198020102001c46101d0950310903008010005101950b13040508905004100c00d8001e40c580c200e010b03007564002a904104840380d12400e000b90130404203000300780d0300041c0420703c99900e00d103020650291001400e2105560109040031200c0c2d2000d25010b05920489240030103880d120703140c803180d0495010300c46024407400501c004034288100d01c541c0c8a21160a4150700f002c2d501501c40c210b40158118400154000b01d026052010f80d00c0b02e50300740c680549034a85840004111b980c0311610240240b2809074449981d000c07880d800f08 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 937405215 1250 937403965 937404001
    0x412090e100801050f16050a1704081902010e070621050108010e0c0609090a0b010c060c05030609090a170f070221120310050108060d15060302010216030305040e 71
    0x2103451030315061941001091020520031640c082d03080000217a0300f030a500b03202d0b9001d0210092200c020f124941829640c17034120040200c104a081104064100900b162982c000c1d4051760b9013503074802e0080e4100c1c82051250145400356030500e07100314041d000000d4210122900d80c9410030300d03041200030038020b48119050b43c01106040c0000801c1c451010740c0038410004080702103030304480a550a00401d0302482c0d0072540d000c6102c40c00218020740c10742010180c0141494050300c4541180d0320042240c0e20102d80d0000a0404020800d203070902c58901508043c001004040149190360385840c1c04c03410240b680c5003850081480d210824080069904407640240201214103031000303020b0b0030544c0c070240107005100e4100806038914041c0e040300d000314041d06903e01002e08040c010340b100413010f00031540010b402201600820032034100001e0358105080003203401803a43c00024504402c101862210041d0346004100003030700481145c0c1100c1c10b0a111401d1640d50910f0b02d12035482c0c00f = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 937406465 1250 937405215 937405229
    0xb131505160618060e0f010606081609050607080c01060b03040f061e02070b060a060302031308072108070818151504151a120123190e1e041209 63
    0x3180c110720401049810a091500005e000c564441100301100f90907a0954421840032a000801242e240d1184e0408180e00e081a4100400132a03035940c0862141d5100910aa50081021074003001001080c09260300038500c950040b400c50800e51034083d000b41c0707803083c018542a070324800c0404800009080e01d25001d84620115258903603428081e0444004030b4102c0c1c442d0300386981c0404c265000c2c0c0700380c0380100a20a402c80d40070b41c40c1d030303a00700e1245e0002c9402e84200302c903040c200c42c600d1204146400014207070f6071740c5e96090810003030140420703001410450302903914070012030819038000342580d080d0f05075444280d000d4a41104031704990040b0b01d209a0054148103074503400c0f102290700d000c201c9038091503284101019100005140c09100c00004160b02c80000410090011007400265080049509164084e0f1007000800c1c6902180c4581c10302c80d100c03001004014581e2807690740c0401410300e40301544410681005400000410050520000d280490300c0303503205190f50b0025004c0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 937407715 1250 937406465 937406501
    0xf08090a050d09062706180f090608010f1b030b0117010b0a02061003030504060e180702071806050f150d0203190c0e030a02120f03040b1315051606 65
    0x100900083c0000c2e00360003104081441c01043c00d090100e0300505071400700b040d8207078004c0d10707003840740c100c400c0095981c032918188112400800c0103168a101e000041910100000d40b407450170003402c3c2900e0b0801d00c5c5440c11813070b04001c01d4680e10140100030741c500c4103140c0014001071280059075140840307142003001c0742c0028004034503007048000400184d0150f408030b032100d45d41c48900840c202c106001c000d00040f8207000030003003503005185008412500402543c8942064110807450620480341400146d10040701004040801031030007407a00c0300c95005204060a107008991000c5c40912041d00541841905040b45664241590003510028030250340c2c909041d0400c45541c2c102081300240c85d4902070381420920701074000896014400790180070140350b15000c1140315003046c0c509078128002ca840614108100340300030400740055045440e01d402d41c20741362090170310a507046010342644a2881c16011500502a2080e541d03d46401170303100720280c903080340540201ba01403592809 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 937408965 1250 937407715 937407733
    0x60f020d050108030a050f0306010912050106030b0c12060d03021c030b101e030b01120e061e060114030a020915120903161401091b21030f08090a05 65
    0x115002003420400e00042844aa41c80c0c59a140d101c2c856400800c0c007251007000000482c5080e41c001d158480014185203110540d10485140000c650860803a40c6035582c01080c400c000301240c49075003000340e0006040c14072000e50704c0142e4240c0054041d61080203c0c5102c44201072081040072109940720224610b00c2d00c0640c405409009a00c540501c42d140ca039040306103552113249514202c0c400c681104000c910031140660007001e03001410360400041c0c80604c003ea50340d50098800c00e2544000501c510700e440c021182030700801e5040c0200c2842840d06101e0380d0b80e4040e41c090000d0700c0081105a41e0346032251700400a1140d200b18a40004c1c8912114004004103005001005201180407030340f903490455442d264455141a008010804a030380d0300810f102c1c3c61400c980d0110b41c3c000040d211100c1e260b18034000f00c002c10a0481c11074004090210403501504214040034650100341c00101d60742d40508200d12401203101003041a400182aa0703108112070b1203d1900f280640d00e410b2 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 937410071 1106 937408965 937408991
    0x105030609060d0f0c080c0406050a0b220f061d2e0c0503161b0303080a18021503090c0a0311120f03160303060506030609010e100306 59
    0x10004c1c03103240b0015200c5c1c682d88005d8007044005100e130040e19010401030b80c04035045907004281d081c4080001e10000d000b07403a12003043d41403040414041c003502400400c1142e0080b042107004000004030550014051b100300c861900c080040d42e84c45409001405200300c41049034668410f8048070b681c580c001c51014203128610b0849004420354803038a1031a0491641c0d0380c0641000b01c0068100b140d0407140503a410a9000200d8005140d520003916015005100e11041c0d84c403810f040300580303000c5000424071039004011144110b59410410129002180c0324401840340c0ca80b20030403490715000050850741e1101c01031040381c884505000704060585070025040c49081c07180c41c011386c02030014003480c0c80c0c00d1803032403030300491828010269251035000300d00400041007408030b19202d0510380c60656032101c600c030312151104024458004050b6001810051030000c0c050854 = true := by decide +kernel

theorem cover : BRFrame.Cov 937230215 937410071 := by
  have h0 := BRFrame.cov_init 937230215
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937230215 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937230215 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937230215 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937230215 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937230215 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937230215 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937230215 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937230215 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937230215 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937230215 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937230215 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937230215 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937230215 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937230215 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937230215 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937230215 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937230215 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937230215 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937230215 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937230215 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937230215 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937230215 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937230215 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937230215 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937230215 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937230215 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937230215 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937230215 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937230215 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937230215 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937230215 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937230215 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937230215 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937230215 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937230215 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937230215 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937230215 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937230215 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937230215 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937230215 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937230215 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937230215 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937230215 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937230215 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937230215 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937230215 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937230215 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937230215 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937230215 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937230215 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937230215 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937230215 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937230215 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937230215 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937230215 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937230215 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937230215 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937230215 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937230215 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937230215 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937230215 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937230215 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937230215 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937230215 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937230215 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937230215 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937230215 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937230215 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937230215 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937230215 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937230215 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937230215 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937230215 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937230215 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937230215 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937230215 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937230215 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937230215 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937230215 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937230215 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937230215 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937230215 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937230215 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937230215 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937230215 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937230215 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937230215 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937230215 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937230215 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937230215 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937230215 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937230215 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937230215 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937230215 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937230215 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937230215 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937230215 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937230215 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937230215 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937230215 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937230215 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937230215 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937230215 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937230215 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937230215 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937230215 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937230215 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937230215 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937230215 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937230215 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937230215 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937230215 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937230215 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937230215 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937230215 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937230215 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937230215 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937230215 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937230215 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937230215 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937230215 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937230215 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937230215 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937230215 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937230215 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937230215 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937230215 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937230215 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937230215 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937230215 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937230215 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937230215 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937230215 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937230215 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937230215 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937230215 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937230215 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937230215 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937230215 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937230215 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937230215 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937230215 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937230215 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937230215 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 937230215 ≤ n) (h2 : n < 937410071) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
