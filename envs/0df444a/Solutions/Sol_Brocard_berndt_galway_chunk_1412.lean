-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1412
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:51:25.940969+00:00
-- url     : https://prove2.me/submissions/de4362d3-addd-4809-b91b-5d76fec6ff99

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 253776978 ≤ n < 253956834 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 253778228 1250 253776978 253776989
    0x60907020a1502090627040e0a0308010e060111070303020c0a0608010b03060409020a18051b0c0618160305010c030f0b060d180602030c041403010c08130f0c080f1204 73
    0xe080c8421226a543d4081c04a07082e026041505d4550f00807111006084054030300b64001c10000d00403507150400d0711a00b40c1c020000401414400c1c404e40b0064210071051244441d51400000000c400742d200300c11010701038184000701c510042d10392401949500088240b03038041c2c20003840c00102644a84001e504859500481b03904d1504c2c0c10082c040a0b0280300c0701680c00c03245400b40040c540c400341420040f100c600c0040050746041c5119112042800034110306442d80040c020608811000b00f4441d400512460340602e0f100c20101c482410232902c18408441c006804000006104040d000980c0210850740d04210400b25210f0510484078588101600300340b09105c80c0081c850340d58020741300001c1c0c00790110940311881c1c6c0d03450b00340e81c42100d80611941022408009800e418143d5080780b1404500921010059034001040418018100c1c1c0102c003200310140d081c00084ae08140601342c005002c2c3c5c4402d0744031418141c0d6040d401e06002081d200d03e014900280c03080b84262010358070b = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 253779478 1250 253778228 253778243
    0x90a170909070f090b0c100609020304020105030105091801020a080702010e06040506010b0a030e0313030b0f0c0304082a07050a17100e120a091505031005011d0604080105060907020a 80
    0xb1900541110001c44010b886402e201e0450000304c0c1d5082c00d0310291402c80b0100c0b006103c4a24500b5400003035403003503885540c00a0062040c040141c1c2c0202c02d5a0550b9016141f05c0c21a0f62a04805d0b403407243c0c9051005600d51000803014091503206079541d10620b91a002481081203840751140e64030800c80d80a4000c0d0441001401402c40d200d0040102c84603610f0041141e2108850185c1564052007540d070400224180c1041085203400449c2c5d80b28100e403044004524040d1184c507031178170005100414040c000a118030703a0f04000d602c1c81045a024581d42c3da071855602c11000e54800181c095148030780c8a00c0c90014002d1036181046d600c04100308080c10410354030b411000003400d42c205001209000c0c141080c140003032601c000e05101102550707071049052401117072001800042c141078013007010800c00c000303942421506850881d0000c2c030f02a40d0b9021b80030001e0041c00207180585a20020014002802c410b05406c010f014400448524003181c8a1807001d80c0d03112a1040b000b850007 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 253780728 1250 253779478 253779481
    0x1606051812100f02070606080a050610080607050d09061a0312040303020c0609010c05030a03140c030c1903060f18061502191106040303050a020d03020f070b040c0e090a170909 77
    0x340d070766003000f090441d0a080c0542403d00d2030340d0f0f58007501d100c0c2c1c11210380d136070040d500c0d081070040804c051504030101d0040c98980c241014100e40e12800300600d550306004c0001550b00403040d29078407004000d90000d408001140c8001c229400d00720b42071501a2003440b841c2080c0402500e10002c5404480d4190024108030030f002c0e0070311403660030050a16041c400f0340405480440c40a1009022000132940d00290030480c3d15903e40c00c481c0d001c0e2004c0301d110070600400100104140c00c90369104540304007410442c81c020340450141076581c00811818581a80000c2c4a4200386e030003203030101c0440c3c02070208a80b01c07109000e94417103290b1002c006070300c0100c0c0560f11090035101d00303a007030340541d03104140490240046030040d071259008034006400001c02e0001da580c180520b5180001920301980340c224200040c1e0514066124040d00500c0008003140c100f010f01c03400358004061164010b082454207503003035916010021815900c0280345051004101036010440703401440003003051046 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 253781978 1250 253780728 253780753
    0x40501051206060d0c0206040309060f0903062016020f04090c05150d1b02010e0a0b01170a02031203160908150a0207020d2003030c06181606051812 65
    0x4110010b46000c3d00100204001c40c50108240114040204c1d550000c20b15070400d468000e11401069200004008084451440e0658012601012030350040b1000c504021200001d400c0442c80c81c44144400da4001500c20303c0041e44c2454848060003101c070214055003513009e0205842c0a180e008001d824110418482e61610205116810442d1240385052020001c10704d41210740c0302141803204101289064444e80d424083d104c100d8070010043d14000b4019916080c1910060240e660001c4524250001c1001d040001070a40c940003000c03104042244140340e1380e40d51098821a250010070307501c55000b1030240e40302801b110617920080c012284e14403002d10301000c01420700d41056408001c484003503501c0308001c041144c0501a00c03030095580d00b2000b00084103054581f406500180301e02c1d03413810000f15840da40442902842401100030021803400e040308020104c400380e160083c0854459407000c040e00030520301c2ea0b2280141c50034102088158048150900e8842c1e10609036203c6 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 253783228 1250 253781978 253782007
    0x100f0509040f05071805010f06030e0604110103090c09090501060602061e040804090e060a0e0a020607021014041d010b091e0604120b06090708060d030809030f03010b0901030c020304050105 83
    0x84582c0107000340d414581c2c54171911018906100100d1180686840046c000343d00e4010aa90040c589030804106070781c5040c00183d11007900030700107401098410b4400d21180d01a82143c0c549950190703210b5200c90321400e080b0010a103940302030b1055880d220300850b0032400010504d0040c403007515a030a2104003031450a002c00002001280d0b0b4203010700000840303401f1801a410450414001340c5941c2c07501c0000741c000c90f404400d000360a40d2000c0c03401c50143e103c0404440341c060b0140c5844c030808406490a4079080d00b003501c1807107543da0004001402d115410300c00326506440130343c0b090090341c0e524404540b9004003a6040c0d4001d108461407817a00c551590100b405000140c000781c202a90b5100743c10202030310402c255591116001005000d2501c001021351240c09130400b414107086c82c5000c02c0482c4031200004041c0014840800c6180701c0c1001650143c400ca140e1940d41c03581c40c0c058001164202498150100782003010390b00403140084141d030203446041c0e45032403c11004491424 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 253784478 1250 253783228 253783253
    0x308030703021b03190e15091c0311010b0f01090b0a030b040608030a0201050c0c030403030503040311100b01020f06090613060609050405010c1206060207050d03050c060f100f050904 80
    0x40901d81d003000300181c00760400d0094507500d10924099510f038909203561104802c0501c0c920382c00c22000d01c10031140da07030302c180c28000450503c40d500c5498028110100d00d420904080d220488119a03070700380100743d0f00100800d1555020340007440650058814040300c80000c40c0d205002c00c4907404203010084112000d4100c100e481d14020a022280340b000ca011034011b034010103080d8000050868560341c090042c03540101c0c17580d03009440c20a803440856241d0003640002420080000040740c01d0502c20700b45094500c02103003c0d22003074158908070500408226072698054015402045440c030b8012034100d02c6410404043c003400d68881e90f4412410041d100b00300e40c03056940d400440c100d0514400c091145d44a00000108124030400150500b1038480310080c4950a080c2c0500400e0360105e6010200d43c0f003a296829a05e0b81c0e4a010785090081604406c0c082c41208104501007141c865070b94000d2009500c1c000b1714a071038000c00341201c10203000d550380014401000c00c00150200c2d1010 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 253785728 1250 253784478 253784491
    0x2103020901080a1802092a070804120203070b180907022b050c03070b0a0510060c02100903080a08180a0c050904030c050601061e09050936010e070f08030301030803 72
    0x3040304c240301da400540141c2d0213841e4240c24144510070035003000700d403142140c404c1d0821480c0a0900c2c22650301c0685a1099004200300d42100c14138200854030104032100141241151150701c0341100160034010420648060f8821031160010909942c0042100707548c820f06070b0401e5443d041c28070306032700300c1440c180d15140400c00104100c44c1034000c1400604400381c0f0070b0345041c600d420a200345105491000d04401d00709031900100300074294000c1002014294140c81c290344c8400308000c162400c00c1c00350300c050b204100c001500c0c0b0450342e103d004a271017800c1c0205692100a4412204c690b1440e0003c00281000b815400611451403d607100942c000e11038902005818140d07920103042120030703404a8042540081995040c0040e1500000d00821519106c4402842c00340014031414010704400075400c08412907850b804420f1141d030b101c0b0290a0070400b8070000c041c0c0b2250080207495002d04041c065004c0108040c0e4035500c1c428200c42d42a0001c44c250390a60b02c40e600d560f031000e041c0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 253786978 1250 253785728 253785761
    0x30e0d0302070801090305041d060619050d0905010207150e1905031306080108070501030c08010504090c0801020f0a14122701051501080a0605010206070311090d2103020901080a 78
    0xa2540f0f0034040d00d08184d200e540c0c1c0b01e40b650310f8180f491191000e07018541c82815141802c000b442d0b00d5103c00d40d99024038a40d2a400e1409020209490500c54220450201400d00c845031081c03000540003442c07214440d02c0b5030312740901980400022942d13108051400d680204e4901c9040e800c00903041b140581c00744088da407500f20120320701c3c401c0d0340c0d40e540098040b40c41c0300010000300c1e1091003101d00a08080c00c0c00d0080c0303c030000004101c52414081c26208607500c454507002d02080b104584050301010008540d28002007240250a8024100c0340000541410b03c03a4029030b403c80c207079058413408103420045600c0c1c0b40c50a1290104c0c80041026140300401034400403031003401018020005801d09168210484c80010304480700207109413406408c0c90b03010801641d00284003940403900b45000100c200c81210440345901c201a03440e6401a0340c80001814032258868207a2020742c0f4030f10a01c04408103107070980c1070b13010380c81d503460208581d0000a01c004195401c2400d0400d030082d031 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 253788228 1250 253786978 253786993
    0x20d020304060302092220070804091d06040b1005031207020f010c06061211040231080f0304060201230c16080c060a061a040b1e0703180e04030e0d0302 67
    0xd00c10101b4212203524202a2200300e00b80d00114000300c1700c5081c0d40f044020750300e40304994840c01c1662182d4418444c003190f407000380030f04004441c42c00315200e42403e4282d4015003024104055030f00d070f080d101212005501100050b0518002824004034035502c4400343c10301d4070036001c0100700d003124070515050200a0582c400010220b102d0440030300404103030340c02c2c0c1c04a28202803440310201c00b03005018601c10805180003001840d0310b008002038000f55041d84c140707904403000b400fa40c030380d00070802841004d881e03424085c00130001e03000382c4d0b40950081000b61300000b403002000d900d004501185031a900c01003520032480c14003d00062159242c100c105181c10354815031342c5c0c0d120010000341d07a08410288100c4c00c0704c5000d01d00040c0f00d1180d02c0000d130505032841c00c0302441030348252400450002140c111005050419801c5241c0190a864441c04603080c00b0f44081800303500c0007112203408801142400c001c011890096400d9602c01e1100c8654101b404444603880d0010350943c8159034 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 253789478 1250 253788228 253788259
    0xe0c10020109030221031b0903010c0c0b0c03041a0a0612030513240302180a0b0a020616050a0c02040b0604060c0203010e010207050c100c0c0f0e0601020d02030406030209 75
    0x19190402015940009402d1100703080c002d0800000c0064040915020030764020291210000e0303d80002c09081d00c12000304590383c0713100789480303a511400d41550074050b01c0090140c11220b40103d0600841c50780140d552241107030320440c03104a8008059801140070080501c0c2032100c0c407603121002d51400944146c441011400c07007600510102d00003400060072402881d9199580c0000308070804005941c0700810f12507040d1404242400f0b020076601040c182d915000d200642e8000d0b0700090b0134010001d441d04900f5145070f1100c2243e0300544030742c45c0410300e4002c03841c0c0e080300c501d1203540c0d5042c10800030320821070303c5074030a103070a0b030740141c50b41c2900c1c04580d030303031002040140103a032110400342d007052052600307452003080c290000d82d206110341c00c00f003040490690566802180d0b046000d850000c4143c442420900e03000d4801016284081907000d46402c0e0407080c2c1e1b802c1c0c40e52518990b00d12004903596601e94240b5030043c0c0080c8000c109050103a00588071062000701520080003454 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 253790728 1250 253789478 253789489
    0x313030b1005090a06090e011b0f140a020a0506150f01050d0207060509010f11120117030c060a050a06091b030f0b1e041524050904020c010605010f0e130e0c 69
    0x281d500340d92041d07032803004000440c05403080407d541e00c007000a200030a00e15502010403540b4541d9502485400003034801410702c5a100c1d15070200d0840c0301c280e155008510025a81c0594400466480c81841c010608011789040e550f019403030300030030420b040200c0000464280e00500880d91000e5000c6c04a200054214007031244100c40000000440c00005250f900a6070340409030042051020000503800c02402e440c140d0548081030185101600411021861032194021a030302c00c0c0540d4003404100800d503000b003809000e514034184402912969510b045034201990081c2c5599100680609280240c00c80300d505d8622920004010903440702045803140028840c01015000b10b582c02218907081c23082d16048c2c483e01e0940c09889080c00e0309030401843c5500c9d18500c12100f46181180c3c6440741d8115550000b016100b9526055148042c03806049640940341c08a001e4034030b07800280d48144035203e460700c0f0040000c02846410007002004040690f00c20f03503907005819007414551550b = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 253791978 1250 253790728 253790731
    0x10221030402011407140f0c0d0308060d080403080f07021e0108060405180a0c15030b030a06021e121009020a05180a0b040b040f0603051b09010201060504060902090a080313030b100509 81
    0x1400040c2403520030303444000c0c0c2808c0c14400c5c1d5901c1032000c01032100c003103039005440782d612500940d001804001c0c42e042210031406640c0c8002c0001100150380e09801200c6000303441e4040c4207035851603020144070003c40d2116500002c203030000d546080002d00300d140a401a0340c102155200500c00410204689424520912030548079210014020801149050300300d903ca064585000c00074070000500007500d843cad07030302c03009800e0300c0e00480c80021b51031541c24400c03a003000100030951790709500030001240c1e82007111100c440040001c0002038503c40d44c0210f40d80e1201503038519140c02c41c110700340b00e001c103203443d255a040304001c1c03004602d8104850060000e40022144d441d1501d02d4140c00910314a010340003402058103090a00003054203581288101500c1500c4903521601d903040105d0061034144e1000c1e03409400c2810003d00885d0701d900800c1c81500c1503030214445612100c1c02d07690303446481d2604040c00e102443c1040820307410742c21590400c0200041c40310295480b030008440950 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 253793228 1250 253791978 253792013
    0x509241504030b0603160b1e042601090b01120609020301050a0b0306011401020d080a0b04060b0c071220061605162108130302060c0705010221030402011407 69
    0x30300003014400e11a640714040d44c8960118024084903442e01280d00c2071901520640030070080108a1000c603000c4c00c401300c07150069541c0401c1d1a5a0381d096032858991110401c00c110701500c9e070440e00c000744180103940312640c00c2044160780c2e03442c0c400c0308040c6240d012010755285540d02d1800c80103903002c0c02132500650003000c2c0814008806c40c01c1606100042e40b1001c00c2e19003031141a80d0750f1341c011814001d0a206818122465a601514207014044c02007100fa03106150040220720110450b0103045910044400c440c0d8450b10703400c9050506904a0020380011301c418500c00c980c46008008401d000406010a0b0901c5140d450711004407150460884840d0031041f0b00818a0701c5a094540082c82c9582c51000c00404071361082c0c9224803e4040586200000a400c01c1010100f801643c02140e0107403031296101085041e0b1070322202140180342c01402807e00e5000210f28104034108070403102001c0f14995180d50340107640c001100c1c98030811641d41031103024003040000442800d5001c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 253794478 1250 253793228 253793269
    0x150f0301050a2705060a020a0509040518010c05090102031c150b031f0e0a09020109080a0b0f09060601140a120e010e0705010305090d030b03150408040f050406050924 73
    0x1402c01d04002c02080300f148070f9103e10300f886064001141000039295000607988000603a9505205d008039a948103200044d038000e8206000c3c4500c00a0303140708030401c210094000c109000d42450229081e12038402d54600681c0140500d9070906030032400c400300b803c0d411000107204039400362100c032409034a0b407141d49455404401c1080d100320380e101804040d10b51412104005051201e00186c4070300103406070012039540d007440d100b10f901600001e4050005141110180d02452600801008044948031350251034000440d600842c0080c4550080b00f050310783c0400b0b0344480c0000d5105420a510040030004c0b0b032a100142d401e500d1040002d580711003800030502c034140192013441c0265640c401810540f410b0204040e174080403407080382030021443c0c0403c0c1000d4810000703141030705030a5842400e004000038801044400c1c4000c108942443c100001d00d03541e110104812500d5500c40c1d6500201000b0024400c010500d10101581680c110004003441d8a00c0c04100d1800c0319060741d40b80a03 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 253795728 1250 253794478 253794491
    0xf0136080616091d04050f0615040b0f0105042706031505060a0f15140d0c0801080f060106031d0111090a050405091b01050d090302010c090b070308150f0301050a 71
    0xc0b80140481103040c00541070040c00b0382d00d000201c44085904040400c4140d0010012904025040c801400070b09806400c584035405e100081d032586120004119214a203001400021030801c0503000500c56030586420381050701c0c024045100d080c1031500c650f05118503201500e03061602e842581c02031805182131060506080c040d900c121003002e008180b00d001314201c20000c180482602c0c105594441c1010482203401c0601a01e06e030007079858041d480f00c0003140c00320300ba002c180d000c05a41c50441d9150241a40d880c41c40d2900c60113001d182c0406500100c3c010700065000f5040024014001c1024010031000909080d0845001d04914081500000350302c05082c0ba014100030040c020454040115060001c0d1103503840d41501c2d00c1000c6840c10074000c036140d0b030040e01a81d081c1c0c100c248090105e0600781c68006d000f4002e11048402240045c1404035400179000c040d9000140e02d91034039a841d0f1074207220b00d4249100c00c00c14503804075050300d01c50200e44007070080b1401480003c0000c00ca0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 253796978 1250 253795728 253795741
    0x90403111603060e0f0d050a0201060305030315181603020a0e09130606080d020a0b0702191a01060804022107080a0c0806090a02010206040f0f02040c08040b060f01360806 75
    0x35101d41040e240020b0344020b081c1041c581012420301c907901400e080c062355a000031072043e0b001d88000d41c1f01410303d000100400030700d404080d0040161050480e4a01c9207003100c0400d410f40d2201c01d5449469001540c20341a101c18042d40c01400f0002d41da00741505180702031400281c4400702199035068850782090700700c0c10400d40b4028000a465000d0281c070341040301c881c1c005d596415030000a06400c648001040c0d10a0080c02100c8000e10403541c08401403106083c00130b4130b020112501e1410b00061400018841e201d9076000b8000e40d4010120201d904100c03000c42d07100300040c80714101c46e0040d0361000440c0c030010001140310f580308140481e14039292040f11800c040d0300604654868000004810060b0303400700c0c0300d541c8140d02c84103001c0c01d490700e03042c1844030a00c4080000e4210f031510030540e400c20707002031505200b640b1a2018a401d039440c074007840034511045005d540881c1c00303c03841141003180c4094994031041c03911504060404605150408140a83d00c480d00b6a0040c5082c0b200 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 253798228 1250 253796978 253796981
    0xb0903060708010510120b060f121b16140d0c1106030601140309010b0319020306240609060d020409060e0702010501030506180102071a150312070209040311160306 72
    0x18049a01e042c19003040d0f01d000c0106003400c0b00e401d000405c0140300414203210f104c0310b070b100441d69a0007502c4252a0014196049100c0d444a402500418990360000320342d2102e28000381c01007a41c40d4100d90401e140341c0d58a6071455294581242d8917102200080f1000c0e05c1000345800c0c10110791340d03416084a0340c0c00c00841d143c44c60010280584400c00400c08903980021500c2044a4008041642d9584941d6518014241c102010313505005a4501d810851000305000d059540200c0a9840d6901c5004c0c08510b0090751110421624952400005c07147c40c00310003030000700c00c0c09082d907450844070311080780c101d0b442070308507000583d580c003000c0c4421503591020030f40c0071042e0f0000b000f0700d5056403601c594407000101000c90700c40743c0c503008510070039080d0140c82d055980126001c140342046202c1e20041581114619801d600d6051148041e02c3c00040d00d61004c03001d0140a85045802e400744203400300e0062055081c404500b41c5d0b4446c100c02000040201301c070003011110406d0840c40c1260 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 253799478 1250 253798228 253798231
    0xb10050d06050d0807081605030403030c060f0203091c0513150e060c061b0409050403090509070c0f08130b12041a01140f0109091104180504080703081504060b090306 73
    0x10301403c0c43c0620038000406081c00c9624140d089040310352110212030303041c0c0385804c100342c004040d4003011900004041d080628046c4461088138140003102c6c9420410003240021200043c0030341c801312084500c04d64000100b5040c402602d412842c00c45036224418109446502001000558040c007025266020180aa4074103080350404c0c03900001c2240c1d1a5a283c0150005c0310440c10034004185030140c0a00700c5005103003c0c081480306182c9802c010b4407007643d500c5040d00a25402e80060b42080c0309000c2d0000c1076910001c18009885036407905c48141d000300c0d01116442c80c8800020544201c00c80240c00c1c1200e080074841e507035113450301d400884424a06026100c03601c207440103101c2040c2000d0440c140e47c00544d0320b505c2d420000b00040341d243c41650300541c030103417078640824401101ca000420540710b9411030303041c0b204001141c2a04640080314041d041840a101d04c00009106100c001d8200040d0079804600d48030000c0020100d40140d4000c940010340020032600c141070600c81076 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 253800728 1250 253799478 253799489
    0x40e030711030706050d0e1504030e010807090f03030e030a06020403081e040f03140a0b0106020f0c03031e1305041401061107180902040608010c080402031b13090203010b10050d06 79
    0x80c411a880c0c03e102400078000c006c1c82d2180161609400e00f81540e08000302020001c00121294107414941000b9102c044006039031800200c81c24009031589009010350403c40341014680c902d2286503032070072160703040e66a9039039516025481e80c0354085450790020300003440c066034200340d8403070300540054148800014542840700c0280000c000070031801c0e8002c01100c3e08041d1854641e02c8103182281450055280200304200000c00442cad5107500041c11003440c1840e00403142485107a104065907070249240c144500c50035900c80034500d00800018001320707075100700a000f41e151140002825240e44881c854541c0c80c03202c00401c40b40f41d104102d03821101031341c4081c06030541031040c036045c4401a80c80c0c502d0111b80b1201c12108548450b4003400041800500030403615107543c0c00100210720a4605912a1040c244c0c1200300d0000407101001d5013000030f04040490305071082c208050109910203a074076541c1c410300070034035032148075075241c540030283d035441e503100342000510080720b010760010f = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 253801978 1250 253800728 253800733
    0x120c070f030c140303160602031608040803041e0f03030507120c170612030316030c091512020f0c0705010f03020702061b0a020d060f061706070c05030405040e03071103 74
    0xc0002c00e00c8800100c050b1003007105580203040012001c03c1ca148500100c102680100c000b444040c00901d602641c0181016540c5904018040300200c0b80107070103079800343c10341c4010400300340040c00f00c200343d120703628502c8850341c6903000d662a00501e0741c0710500181c0200b5207030b10130807201690003024481b018080200030050a0b0b0141c1004006e24000320400102c18007100c0803030b441d40d41d42c4105502c0307188840704682d0f0b2860008040680345205035600c0d00400d0514040064550003003a0f03078020b0702c10280b00d602c0340407400001103032001503808803504101d07400c00800c03018220790300c01044080c06034802820b0035031074000010038012050340c03081c00300b510505c40702e00142d940c881201c98241e805100a200d0f41300002c5054109512050000e42c172120030b03080902000712542240041c546140c2c0e007040303107507a500e840b0000c0c100075100002285c1c00010000d014580101e03203014101c0e0203007003202c3c2010b485002142c00c85028804019503035101003211001c0242c00494000c2c00380c1c00307401 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 253803228 1250 253801978 253802009
    0x101e0e01080c070b0f090f010e0124180b010c0c06030504050c04050709090b0604090608060a1109090c0c0c100e0a1a0405060a11060c1c0504050d120e120c07 69
    0xf204d0002080c050002c110b600383c5200403d03003903841000210250221100204016920349200030b00034844d80c46081410040030007050321046101000c00220b5071010130f5a00100c0441001c00001c0c5907079104203051000b01d000800c0851080c0070a00e001d000280c800203aa0305103406c01925200d000083e00c0d201c0c3e0b007000e0400c8402ca030700c410300f90100e69040501161211586002036142d010b1030b000310700c000d45044000100403c00042a501800002504111190b2600c810050510401c03440b20782110080000c100e0440411004100d2855100245c8000d0b00307000300001d070081c80141c100c000142c110029560700c2d20389800d05100400c0c204c08900c0b001c025140e01c5100e02c1c00b0318810180b0844000c108548102e0241456540000204c0180c502e03601e001141003419400000f00340000d201140b000c07481c014010722440d8016034101004009001c0d4508040381d0400340c0380c0500c11629101d1540c60060710003046020412410304500a4aa00000401600e4070340c0503072000301d0094000e00c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 253804478 1250 253803228 253803233
    0x90b041110021c050705060705131a180d1a061003050103020a030b04020105070c06020a030e030d1211070c0801050601170712050406060b0a030903140711101e0e01080c07 75
    0x390340c443c400306101e03a103092800009003500c443c0214200a8240d0180504101c96541c0c4180144400f24400001ca9030031030f2216aa41807802d04900c488262081c10010382c0d284220f44107112105400c000c2c030a01d003590151340c1d0b2001e1407403140e05c0320741e00584842c140806480e20007a114000c551500d420000d640c95500080c0d482d80191002811586c1d0702000f05080d0b9200308200c48a90b0382040c01c2030072141d0f840340b0003540c402a40900394002042181c250001d413602003007080341e42c0082d0341c5080c62a282070b4051401880d2615076820f02c0e0fa008c1211a0001d801e0310210401003c0b49000010207207005000548a4096003210b101d503510300701704110100350821a482c4480022510005090340e580c03500c5001041d040e00454214a0302056181c5402d030300d034109440643c031a603a21040c5c09004000c680050050140c0100355903074904c03095106091107003140d0031440340c40c503020b031200300609032440a10360088941070000b004800000b0301960003183c6243c00004000c2250f1038400320341c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 253805728 1250 253804478 253804483
    0x90703140402090c09030a0b01141017150406060201060e010b0307051c0f06080a060f050903070f0c1a031b03010302091f03050313090501050901030f1410090b04111002 74
    0x108003d118100070000306002040349020741d07522131406801c45025013041c1c207040c91520b100744103104a20100f200c4900719400c2c51b00ca203508291460b140c0c9074840c2c0b40030315818001c1c10300420101280c005403a02c2c1a940d0f469000310002840180c00000c0d546007494290a040c110581010410010070421300c07040c030b43c2c070004580704a00300c1c040c08485101144068809401c120030ba1016460038104040741c01d080115585040718030900d0201300f900c824901c44010b40d60111105031043c0c000380108408180700c840c0c88011075106000700700c2402e4403410b0101c0b80c111040320503106500c2c040b0130050041c020b1094880c01f0006401c0c3c85080d50300d503a0004100345401000b08e24611621020b9001441d003d1a086e8043c40d8041e09981c1c44415010a0408000542c0b0070b16180c2400c10b0300001e114244840e0b0107050360380000391910f0030300050711000350306074000068803100c1c8540080361901d1111442100e007424409e000c000440d0501d0f0914080c107183d0400100d00c6801d00316040d0100a400 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 253806978 1250 253805728 253805731
    0x6050a0f050108040804080601031202061003031d0117070207050a1406072411190c0b0406110c0a030e040509010209090a05060301020405090a0b03011d1002030606160303090209070314 81
    0x7480c201ca9a03613100d1800d101d1601031a44480319030b21901002000b00304052070060002c60303d950895180d50f680001d14403217038102740b00160100d04614030034080300c0031404615001035410305048810920009901d01500707000c5400c0c42c01070300850b1083c040f034a01000c40034018200320418244800c2c40400050103032064400041102c0c485181c2070140400800f150f0318016900d9008000400004541c0140c2d035209020507541007400040d813014032030103400250303002d54000803101c10365039a50713071104014040c1403014202d020302840040c4a01100b00304e000c0001d03109540e0f01e0850f203414003d00094039005803a00c000c60740184000c11a80c0c0b118090a41c0c40803045c1c1001c0741980b00d520102e8024811034000e15002035916041040070a5560051209c60400b50000c204a0040d015100f442c05240b10144840e0b80003400055030940700c40e005581c10580052506e807900d110030000c044003030303100e581c1140482e840ea400c0c1403d40c0341161082c1e45c4070360b0a00341030204000480d08012100300 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 253808228 1250 253806978 253806989
    0x60115051303140d030b030304030503040b0703050c07170d1407170d0921020309060a050903070b0a0c0b06040b0307030b0c13030f05010c0302070b0a1e0f06080106050a0f 75
    0x400c01802100740a40a0350046402c00000690412281400380c0c484d0081c1103120040303400c2000e0804036060010456040740e400101440c1001e08155140e032141e40214825005c1001c2030017005596a0244403405c000c00d121f821113240c181e44150254100102119032a007488014640324440d11406812103010607407020003103464081c1d001c801d1209004080c41820410314140112040140490420003418502696246210400c4c0350490b628484c4605076500b2400501c80307121054020809440e007001c00500b07441105482e043c81d01c0352034200c0e8101c5000142902490024440c3d003100b403a400c120295010300455058101083c1d45408600c002425041130000090841c01d01c2401d80e40c4400d00c20424103030190f540d040c0480c5241c1039100560b801e510789010025018000e10071a0105070740000103141c0350792102c044400500d20420300d55000c0b2800c0582030300400c400d214200240c00545070000f2000d05188100382156002e4104a00422074420244803e034026400d4508681 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 253809478 1250 253808228 253808237
    0x6090118023c01090f0303090e09010e0607121808090d08090a060e1302120f04030c06050f2403030d02092220180108220c080708060115 60
    0x801c4410749000c0308201000481404044915000070802c0d0400d040b08a1030300340d907228400c0b903e07116803403111103152000034081100307001c0c2044207961400740707d81e1101c0e90f0303c00051000c039900541810000c04441d040002405e6101c4a850100300c1d218500303201114840e9010352094507a1401418403418251030f00c500c410a54038410403042c0004c40c0d010b070801403e0450b10030b42d00c1c0000760450340c141805920030341d03011032041c2240f01d085c400d5413000100701d01408100d0316070b5050468400c40207007081c0c5c1080159001c1d40c0200f9100d01619010b01c000041310489481e00309200d1141340400780281d010100032540000041d40c0020580d110085021350040c0d50348100f000180c0d00071000300310394120010300740350007c0030340481e409a409020364482d9102d40c00140d8204203401d1081d0040e00b0680190b958603841c0551150045640c0f09818008801407541180d20300086410b0301312003100d0a1515240601039018248941c000500201005100340d50414416802d0355015041040800 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 253810728 1250 253809478 253809499
    0x1805061b0702180106030516050418060803031302040501080d020615010c0f0501090b100b070318050d050604020f0d08030a090510050a0e010509030f0703030213260609011802 77
    0x900d8404100c403075055004000000c809001c00c03501e04100b00911407200400d14220001d8034142d80f41a185210342e00b15607070a842c10342400000340540034070201d0034800c90341c0d40c1000320300d81104000950144540c41d040d85e03d20602481000142c0700c050f000071b00b00e174009103410b411290f000220103400c09100c3d04031981801d01480100c81c0900200c80140003419048900c405000e01036000300e103083d009034a01d012a0341c0d05003181c0d0950031584586001510b00b00104008248100e11a25036041c2c0903540241459881000400f1000a0841031b581034105506110451410241d04a0000d00544940d81e40318116103414080d40002804007580c65102c5040d0002c00c0024450490390900ca02020405820074a50b07e1005141036001c20b1401e62810000c500218000010f4900a4a654800c1450220303da1780c1100a50040071040344918020304000c613140d191205080704179080c442c482801001d411400618200b03000d8100b00c0c0592503c401c1e1080c40280c0d502004415030160f0306400203 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 253811978 1250 253810728 253810771
    0x504060b04050c12070e010503072003030a15080601060507020d050106091103010305011401272003090706110601090b010509040627020c190f0b07090603180506 71
    0x24100450003554442e24100070401a034000c00081e0240b40c0403001031142c00c1d0b035042425150744030042c107003c1c04990140005040c6a00c1031100b40c001c40000201214500d88070454030b803440e04160356a911045d1210004034000c000c0c0c0e11a80000c0203030000401055141800140041c85800001703030183c4001c0c0c2c0c8a0040c00300075000070004105490040051080342c041401c43c903002030204982035400c0ca0f00e040032121f02c403603549058890f0902d804000595030a4400c61460a0003c00c910a607211264034096044180c00181c2c03125032059095601d00e869410a070600342c2940101c0140551409007100124000580c40e054421007800010392150a030011780346405444400380e41300d82030440100703072200d03035a040b510010980e0400000000c1128000c1c0d0590042103c2071480c2d502c14441740c4031083c0c010b0750340211a4040d03070304c401c0000510f450300800ca201c12200d40000c503107101010440643d2500c103d000c5c0c40162901010307400e201c0c0d6036031074441401031f24113030240e00441d410826 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 253813228 1250 253811978 253811981
    0x5040528050132040f150e04021e03010308191809020901140d0e01061508040f1b09050702060c04060203090f040f0c0e040b090112080a0311030f160f090504050406 72
    0x12041c99205151078040ea4075600d03c00a500c140152942c3c62950140042c140b1110841140001c48a0715114071101c9690706100083d00200c03036000008480c140c00d99480c00700e82000f14003031401410b041c2e60315828010700c2d40d2050400001401007082d030b12a60680110400d85800543d42c1d9000c000d0380d100207640c0101c2e06031003041d130003801c040d00001c1e11140802e015407056401c540c00c14024801e455440c0220665440600b0103074011a000200043c0000c0b00301e1101217030107214510348079107111400040c0b0300f08003981c1c01000d036079507444081c001e48075010412950b22060701c03620b0f81d04c1e16061030f0b0020344030f010b050302d880e008581460154003140d4450300140b90724500c2d12000c000522058a00400240c6a000d150f800703140761544078016410300f4611117046c2e40c04514a200341040945e00c0d0300f40307644040c91000c10036940e2505100f050901c10000c60003000c0c0e010400e152802c01480d481031422803064160244121391130482c0c20103801c5403006080b01c0d012540020280c1e00da090000 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 253814478 1250 253813228 253813277
    0x20f0a050108010909030315060e0f01030b0607060b0d050307030c0c0b1315121a010305131e06020c0105040308091c0e0f010c0203160f0b040b04120f0210050405280501 74
    0x231024050440132884030b51080d20303966862030442e104668169050f00540803610200724054000c2410005140440c900345c0000755400ca002d0b010420582040d03c80c030381103411002c82200042c6003800054184001c03070504501030419000f0103032910002800d8080f010a4a10038440402e0b021000c400020b80250802502c1500041003404429014a0011b1f516030401030128082450003002c00c1d405051041c20000392688100700400340c420400081d0242544180c0441c0c4a507001c008800b00c45400380640e60081d41300b901d0f20319803410120000c50520000c0c0d140070712800741d6038035003c00345980b041d10440340c40400d0303440142e140110401260000740000000e50144200b40011494001c0005010101c0e9078201d501d00f0180d881d01d066100500c540d210380317444c09400b0f10042c048101e550829820380d520580b40506107080036400305a500b4440c0d41c460340032441c0400c1c1000076090010051500000794a907a00d106111513450710281461801410304001564256208240c8064400d0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 253815728 1250 253814478 253814501
    0x903060a0f0e15070f020115120c030807051b010c02180910020403080327030702041e140a1d06041118100812030105031005090c060703020307020f0a0501080109090303 74
    0x12040d80e41d40c2d140e50400705030f00740c40d02c0d07000078009403100c001144188a03200e01c544000b440b8620322894552151070340d0205000580710316004801c0000001c4140c002446940d00c00e10142c05d8444800c105100c0604201a03080d040c805440c04500050b60355840d034012902c25010140c03c5a1170f09107443d4940520000d00305002d520004000c014080c031500558402e0811145c103c000c02e000e00128081e480c28840800e01c3c583c818065803006142c035410915944800e070044550644804210038180e402c500d00c0d80c010304c105542409001083c80c0259440d1140d040c03034011000085081c9030750341d604010009407902e00440c08010761903543c8252590610711070321421082d8102a1000b207445403103071052903810300c20311160604c0c13240f00c141540d04842d002400b0304421000c480b00500500b0008050001d113000d182c200405a0b0390342c0e0064501076003e94002d6858071141e2040c02401d1802000080c45104901003c000a03a0300c00380003815128044000701c0c02c0241844c0507405070010032a0b0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 253816978 1250 253815728 253815733
    0x1c111905120a060c090b041406070c090f0501170c04020c01110c1e2a03010b04020324090105030a02010f09080105040b07120b090619052e050903060a0f0e 68
    0x8611646500040000342c00c0c1c0030f06010441044000340903900d5030003620030484402000d11080102d1103c0040c1c4804032031004c0c2445180466035907504080c0c41082d007000064540d9041c0301805404a4480c090140c80d1161071044007007542d02a55580390b8451148511594001035140d603d41c000390042080c00c080100c00b1921030300072007541500e43d100d400e111603007070464042e0746a40a500041488069070424151f452100803084007016a10805403410f40640d2940c900301c000e030311a440110f104014407a000c22000301c0400c0d0035082104846012403041c800030006000c580d4000c10401c1283d642400c0c114160084107000362144041544020003d519010402044c4092400300303c1c171940307240c0da0b43c0e40e501459503000b10494044d0f10119030010320120005510341000040040c80b055102581100140d840300060712400314400040b0742c007200c842c0284070084401d00300003018045824014204103000340400d5943e4001040a007401d074461038008018500781d8054805105520305 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 253818228 1250 253816978 253816999
    0x30f0a090b1303030221191803050f0706030e030306060a09030506010e0a0b040c0c0b0a0e1e0c030307050c21030a02010b0108011a0717130909021c111905 68
    0x404488540d0344002d0340540900403101b8406501429070100b41c2c0c2d0103002a50400ca00e0b81d0300c0340304054a00400905220002d04550b080e0000b0000d103800035413058005004200101c035031641082c6040d4040814541015909404004040240d0b64001d500307a40c0c0380c0d1105c5201c10111070417000c42d4400b0307010340200720021400d07100403500c0520550701108144092907080c030a000c2140d55410082c4c0000324400186400254144500b0760051015400800c0c000d0007590698104030750a000c0d03941d1383d410035980302d41000080c003d0320b0300c42008030050f6040c00156224592030342c0b1a0501c2e41c0c401e075103d500c0d1500380150700c0100501a00940c00f143e071183c0c00123401038024035551504070701240005000017041c5509825032840b420500201c03a00b05021070b0303606101000411074450b039242050000c8002070700c1f11905080102801c140100b030035200c078010312503000100204104040c10f90420a800f0520700d091220380140150b50b005513031954124180115080398200d654005030564 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 253819478 1250 253818228 253818247
    0x10201200c010b0105040302131d0d020f0c030105040c1205031608090a0f080d0813021801060311120c130306050703060e0901050105030a020d061404080409050f09030f0a090b 77
    0x1001e4864a003080000308010800c680043d1000c0c06540b200a62004111410780e1154400c0d0300140141007606145141240341c00c5111400d141c00705d081000141e002c108441e40c103040402c02e02d11201070641c0204482d09107601d03204400c00e1540245848040e0500001c01085010000c071030380160805510b4185540714030303184140c0c1e442400118802e0664400c00f0a078541c1c066442812282c00340000d00843c43d00d0382040d541410003c100200010300101c40802503114140146050720500d2490b40c0e4030360500d207002d401c994981c0011400500d051210315100d40d26012141c0d0814408408030380c442181950009400c0b401d44c20040080d401c100a000000d501908003109507000101c0082d01e41c0d4581c21a0341c00c0700c03402d21405a142d070000e140f007405400d107370300d111400c82c0c010710000c84e0001c00242028125442901d0840703022000103400c010801c1075100385a00b006030150005042d05051440603940d0250701d45c0d00030042c400140007402d407802441d01000034a50105070a440b441c900 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 253820728 1250 253819478 253819541
    0x12030c150606030e011e0c05160b071b0f0b040819020304090b030c060d0b1807021515030a020402030c0405030619140f190906151a0a02070b09010201 66
    0x24410380c00403e042803422800503406000c1c2070401c00706d03d8040302083c28546190000b0702031800c030103014800100084842c1007240c0b191f0164140c01032030b802030103040096009001c158102c40d40e00c42c070b44903620218006059101c84140054100e406507040e510fc50800720300600c289001501c5802400302c40c040040d8000c00138208603042c8110030428484a90241601d492040201035807182c8200005c9044c00351552000c07042500150816094450240d00304c0c462400917148900964846192841c4031b8620090700d6034810650320b04c1c401845038900c04a540d540c0043d000030300c540c0d004800606c000c2030610988006104c0241141c0b11800c0080c0c030700140b05101c04140403041c3c03c0005100400071880003090181b58199803d612699410750046c11044240d030b00408c040b92900d1162002c03441380e010f4010440111141a0401e6141c110140c0b020005510b00c1a05030390140003037417440e600826044200e40c100c0c0721040d600d00314540100e00400282241040b802c03045041c40a039150403 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 253821978 1250 253820728 253820741
    0xf030e01180323030105040207080909010914010b0910200d08060916020d030209360106020c130e0c0307080303041703040c050d030c0b0a0207050105010506031012030c15 75
    0x90b15502000000f0402140100801ca541c824100c3d508000400c031038201a4024003883c0c1c000d00b88282000e01090000314040000c1e80249030080c0c84404059500c1c41205415004242ea00400b1b0704d008909000300f502c81015030007040501c04100b007091250700c0c1800d405003900300540705581308801483d4010705583c0c81a1030b0350b806108054001222204842c0c0f08880041c0c0f03a0300104200380c50314008034040e501c03840c581500028090031001000c00c0241c5920401c141d243c00585400f64181c03082c0140c00383c1603202c0001c42d03000510181440c0c44000342004049884580414803103861941540b80c0030003580100e41512070002c000440d0040400514000c0784541070284203600c4888003c20076020031b503005480485c071900b041042d4900b40850b040e00e80e100e03040c84030030b56020380c40b4000c002c102224810501074000031103c0400c0428440c1c00e015050071501d642c15801c002c0c1c040c10072503d6a0003018000c03845030442c4020715004040030081c4551260240342d4002c1c0c0003441d01c01500b42d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 253823228 1250 253821978 253821983
    0x140a09091d0105090f06010e04050703060606270e0a1a09010e070f020105090d030203070e0901290301210201090e040c050a05030f100b0103060810020406090605040b0a0f030e0118 79
    0x10f000c0100e801940301003002a5030708650001440241d00b802001050400c01a0049a807813095210000020310f06010310b100416103034594410411480d48106401d4402008a511440c1e40c0701b420701c01021002d07602c1d07410100c1c01c0f400003014505141c0c502c0f4680d5203000690360080100d0000036507410705c03103a01803054109640c6c2c0748140c2802c0303805900b62441a04c01a403607410640c0040150b41c07081d405141d00c01c00c40d15216001440c10b1700070862143c42078005860048089100e903010840704204c2000c04a04135a242c0c1c5503615001130b40c0c0c1c901602014004105142c00262030035a072061b03940d070019003001d0a082645003001d24165225a49a22805000305540c0c3c0d0001803d10740402c0c45020501040050299003c41d01d031040002c00e14070320003e052550760384020078910300800c000c0d10031110794100166941d042050140000d200359104608001c4104000c0c040c07403450000f03813442100b0304e090000ca00c0c414ad54040e001340c6066440c3e10102d6180404011001c0d1030040f8400c402da0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 253824478 1250 253823228 253823231
    0x140408010501050a0f0f0501050702011b150509030f0d0b2d0907030905030a230c01020423030703260d02093604050a0b09070e1303140a09091d01 64
    0x2079542c074001210318050310590302d001b846c0c00300801241d4040c1c0c000342510780c8140f400000c3c20070380b0440c3d011b12508040d0107452091400010490a104c00c1c817940350080c0c120801542043c0c5640117401d210301c5071139000d1003030b107864a081d542c254803607a681001c42c6140091130000d55000a035004003a48c80384c1085480742c080100402d88650080c860096016040300c080e40ca00582c091051368080130100550746408080085c04245003940742c0940115020340c0d002507a590b150811a00070000083c0c4808000b15520700050b101350340000304d0740216580103007008024070700480358038104511492029000b180c0000c609040c24038990040041c46012200005800b104100440c180c140c4583c0c0c18020a03050340b0b4440406041d15080c0d81d00512407001c030381c040e05060f9921001c298040d103140101d40c0c80380b030341482101110b4441640c0a003c1403510600747c00315171402021650344070a4000f0307840001401c40522032092450314094030704168103002d814a042c0318140d880c01d50120a40070395 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 253825728 1250 253824478 253824499
    0x109060507020d020111090d030c231605090903160602090a03060c180608240d030206041e12050f090a060e03010b0f03070905060111010501060c11030f060a02090114040801050105 79
    0x4a2000d01f07950000c1c8010f0540b2071282c425950031346107000c103020706507400045040c0c840280101c4181030701121142201a140c90100700c00104c2070400242c00c2507128007074500410116078070000540c0c240e943c0043d070b52810f040450074050024482e0009141d0440c00f6510084144203640d0010140d444043c3d4803040840308401c015124400140181000140c41002051001078084131001c581c2c03000d210850110501140054040100002d084000d60809010401071012051895000f4908200301500c000f8150380c0754450b200e42c1143d24410701001140200d6039a83e004150340c00c0610281411440340d840d102c0103049411022440e07446582030050058643c144a80800114100030340140401820551584003600008003580d0401040070054485c103002402054020000340e211070032000d06c103040000002e282041900c0c007030f910009141e100024001000d5038000809200180c5a440c0900100e6000c2c0c60444600d640c00c0b804100402c0e03004065000e9412690308813503407040c0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 253826978 1250 253825728 253825751
    0xd0807050d02070f0e060102071503110d0b03010e070605070308070c02090f0406060504020a0e040b24070201020c0603040b1b041e0807081507052d0d0b0109050f010c050109060507020d0201 83
    0x121101120418010380040404009003070200c0d1140349555102e0030033140041d0201e642e00d03401d400003e151a08141c80b04102d0643d42020300c100d6138500800b2001c1c2202c1814140041c0c824030507910014104200a80003509280c03145800300c80e5103038000e02040c0c441c10a600e010120440070758003074500e50702c1c3c1000000c4c50715040c42220100e03038031600c559142079112070410004200300850560400d208800b107103070078881840116000c01070303c4156500ca1a260000920704092101d92a02410381003003801b0101d90300350746c02a8083c200ca81400e0015600111808180c055a44180361501c1d484c06902140b42561511505880349902150f6240b96100da800c0c0d03469041020700e002d00c14a000204504610800060140500d07070064000c14100701450210105010202c0c41c0c030114021803100701407181ba0003103414034034091801600d11420400010403104004120303605024102d4521010800290415010b054010004002c01e140c080f9001e900c411031900218015440c0c145420034 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 253828228 1250 253826978 253826999
    0x303090609070f06030f1103010f030b090606090105090a0b030d05070308090d0c0308070c12030f14010803030105040905010f0203090106050a1e06050a02100509070f120f020d0807050d02070f 84
    0x803540307203d500111103850a0340541c0106240c504c4441c0041e115507020320740303841d0000158001c200704130000780320030701d90300300300c95410809011038000f40c020b1020700000d691084d00890544500b100c90303040300e8031148035440007822102c401641600039258403e2290360440c01424496000c2d440380010365840b000d03040d44448003404028045858a040e06c1c01191080034002e6120401e1304140d01403100540300c9800380302c441c1d5441000070703032561569120b694003401044140c9280030840240c0e94188801070f616070105014890040e50750f020442c0900000f500f1070403203008501003c42d030b01d080500000e8003803e2a406918040c0c0c1105c40009a807500900540c1070b5007250b500584903003030801c9000c4401ea4400b80040045100348a1a481d18150074440c41e4040c00c4808000c001d1640340400c01c00311a08035030302030922500e03100340c1d504c003140400080c02840c0f641110780f406c0070092171420f81100c3c0681030024195200d41070420901c10b40010b481e000b910150318003941c0442d522000d80d0b9 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 253829478 1250 253828228 253828243
    0x10510050f0a030b1203030109020a030c0c05100e0c060c06061017010e13050f15010f270e100603031d010e0f030102190309060b0402310f080303090609 67
    0x25466103040180b0300c0d255100703601125035008020946504c1001449501c0c4c510b030402e070401c00803a50700164020041d40c0521900c64086454100700c070b04100640c9549440342e0016601c0c401080d2035040d80c8413540d1081c4200301076541c00030202074072011040d200030381e614800c03104c41c0e006150000b84a18041e02802e1031102000720700410386000c0e800e10740c441e1924900a0030702d244652040079400002281800030092124030b07070000301040d02c40260b00020a25044c4d0041d03e420154410a000200c0d000c408034852a02141c103a154400504050100034a5201003855440c002e15080b50b41c64101ca402c0203003128001d81c1d540e11540004600c00c7c8080b8103448515000c5805400000528140410b261460140040005042244607190690020310701e8a06500090740d5280030410000244076050b1000b2044d6811418400c18210000010805078402041c19070424030401040d0603109920000c0e1026110007100980d803840400d0784da810035500340078180200c500042c0d110000180b5803 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 253830728 1250 253829478 253829497
    0x3051008010c092102090a0e070306090605040b060f0a060302181908060c0f07020f0d05100914010603030509060310080714040f14190605090f07020f0c09060f0402070204110301051005 81
    0x101d038291203e46450004000c01d50b03a41c1c40c40c4c0941040000458501d200d0300cc880b9000307070008500d0746080c1c6013501040c0e50007400315101d048020144412901d45e04000c400381c0d1498200183d85506031002080500ca100c201c3c16031010700130340e81c8171a480703c10002c003080702c01c400200c0e40c150300c80c41c6101d000350280800100c1e030001d05002c00005031914000394241c101c0060300d034240740712150b11910304000d60303000645545501c50021b4801c00c40742c4449510102940310003082901c0c03c554008105100c0d0140707040c4074600c0403010500d400a204600c070024030300302040303c002c02ea40d00c403054021580100128480c1d490074140250b00d01070360083d100040031809050105541e981d41190032074024010240c1500d956400224481e165292018080c10000e0010100b619085000034a0b12848038080c0303259400c1060b40c0d9443d51601c08140c0d8011000301ca4a039140b02401c40814000c3c060740b80080d60040c10824450400c211620040d41030361000d8491003169036800c1030a4581d0710484200 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 253831978 1250 253830728 253830739
    0x403050307081c050108160e040209060909030d0c020c1e0a051c02040914010507051602060703050705150402030c1c0b0606070c03200f0108060103051008010c092102 73
    0x41d40040c003440c00900c04a400038007002240e1401111440465000343c112468a03804041006645158400c03c07000070442080300100a1409a001c40c003803050282020b07028140c00170114120860500c103031344c05980540402c02101300f460b20000d5941110b51070182c0a025044800950201114104800d0740b60190481175007504e00400d1011411300515002c05128850740b15000603070300d0303015607041c00e40143d804880b5481038040140c01c48030302a00d8101071110400191090521581c5031003941501155500c0d10b8400707500b000c0c0d0361485482c400030114016255605568107500c1c0ba01d0380214001e50407100710280160900a100503428620110f0f4003020304500c00040c9018406940520302800441c01e0007642e541e1100071844a4008407080e90305d00d141c0d0200d0550500405a512004031154042c42c01c1d001c0c00a000803001604450401d0345403000592070800340e440c40001004000e00030000c884810b80c0003400c0707100c580200540c0d000742600b01184102011003034481c25400406 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 253833228 1250 253831978 253831987
    0x609080d0e030309060d090606140a0909051501080a050c03010204230f09270a020d060c170709080111040609151b0c0503061303050906090f10210204030503 69
    0x30141d86100c84008226414802000703049160f4445801030500311459140202c0c0c0c11806150003400c1e54096008101c00307104091030041c4990f1000c40560841e545d03c0000508500d0714141981040d4003440384208551038800005000e03000091006010b500030020b440d914a10a800c05090b03115a10400f88c0d00d14050a058502c55540c0c107142440e41c50007800c203000500100007050030510100c448511000c01c1c00d02280c005601c06141205000c404006000202020750014442502c61203020b0181c0e640d840400a11078000d269490840c80100800741051030445401044802c2c1409218440d5092400003107601f49200c0030b0f0740c240c8035107446801d401070070104060b6003c04d40c0300300b03281005000304828015422081c1c01c8a0704d0b034016541541c40a00380020702d0319201d0041d01c0c00044e1419001660082544801074034480c5104441096a0391011800100500455000350754007101110354648103d40264000c49545003541d003580006007094104002c034051440040c00306d030020031 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 253834478 1250 253833228 253833253
    0x30318080a0f05041a0310060c0201080a0902040f0929060904020d020303041e06030606230c0a020a1410090311092205010b0102190314030903040803070318060908 72
    0x4882c9809050a14105050503510404032480c1506084c0b0035000c010b0010a10101c5014180001d0242c4514100324410350030503030008003201001801907204030f036106091411543e031a00041203603100100184070700d0500e03003040d040c4030703e800035045003c1500c01c100c5507914a10906e20341c4034101c000c008551943c1c41d41c0038003024058041040b603160104000200704881c200195103a4220000e18500c0c20390f0038440301030220394850708400180306c4d00b08090f10100900b0b2010021a00310382d00402c2d00e5142503410b0760700d04000e4010080d03002d0054000443c0b0303050805030540c42c00308110340c00d00c051500c2c1001035032040010f00010b8202405030b403501170203003000ea8140790010414401c02420015010b0304d415821035100d002c0301d0070394581c0c940c8181c540e410019a00c190300500b5504e00b81c0c0d0916035001c1c1c0b1411140704503e56101001c03000600e512000e0003950000c14040c000e4070f98542080ca801010700d0030302068105a602e0310000401c03010b224444d900c00351a4190002d10800c101030 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 253835728 1250 253834478 253834487
    0x101d0108011d0c100c0209010f14040218010e04060503030d0504110604151b060908030a060f060c060e01060f0b040801050a1a1e130606020105060301020c03070b040f0b0103080304030318080a 84
    0x4c036035080c10b022025800c01c0058542800c90b85c02002d40301d100321740071400d2000701d4002103190480346100704c0c01442076040701041000711407102c6070b0074200346040340c0b044400702e8003401182c2e100c9079150001081c0d0f1240608503411052080380314030b031080010090507041101d0350080d80190020150290b2401c4086802280780c1c49076a0518a01c0c8102140f650f070310340e019180090412207440c0700200c1884111b04150149038081e002202041440c40e00700040105106003e0101030505912800317105035070642076100002134100414020300c0345440e1501c40041741d1051055040541c0b91000090302e030a41d40c0304681986800124049903007e000b004c00c118041c100700f0010070040c105490b07800603501c5002c409810880d1803801b0030b9103440e00c8406030071101c000380300e0750007a4010047c0e000c110b1001b1080b603c40540c0082004107944660030110722048100301c0c02450074840c0c800120922500c0c10181d84600c2c1b10b03560070b000349600c7c80034102c0b60200c0302d0070003040b4040c244600b50049008 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 253836978 1250 253835728 253835749
    0x1090f240c05070303050c0609010b1f0c050102040e04021002060c0904021809071e140a180e13020f040b0d12030e0319030507050f04030605101d0108011d0c 69
    0x1d28284540042586902d4141810b40e4411030100d0000a143d07850b1003014010b095000c0108002001110352803000725010340040403854040084903a40e1400180c05641d0b2450700c2c0350088c2c000c541f500c0c0c860390f81d1078811100b036505910a4040711800f0b0302c0c1c0c500c0001c903e07200c0c80407801d51a00740340507202400065000340d10f802c041c84070200e088181b291509180e151040f2043d940b401c2c028045c000d140c0318a04541c2c0d20800401c000001a00e500390129806c840030f01c0e04914062444800b204010380d00910303030790000003160720401c0a00c60303020020b40314400501d000321403030051030540008000c100daa500c601c013900301d260b5100c505e02091003c0c0003140441c415080100d50303030354104011405d5901c86810780d0005c45004050201c1e66505210760b9911003c58102140f41492000602500340224840203003032944450020304c008030001041001418484904e1407002c00200e8580a2030500340180c4085600e40104100e000900840c42d62070407202c403000c1c01c000721480051081c43e026 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 253838228 1250 253836978 253837049
    0x3030e15042d050d0e1507032001060506090f041d070305061608150102190f060f02030408120405070e0106030e10060b040b070606030209160206011a18010c05030d0b01090f 76
    0x403403481c1801b040d030001001118400e81d18100000000300380f040060202e4a00701c002c7d603141c454240000e803102422201e51710002c540c0daa020207117100002d0003600d040003008412503a6040903030500c01c00000d0810590380301d0810b8607107660f511020300c0c4101f14107462460002c1d40140204044080b8980e651405040602c1540c0595031025862580b1000c0048210703030801207503888105000d0b05204103400c0c0346041c0c0c420740c41d60401d51034440e4140510071101801400341d0000c202004400c20640d0010704020181642542e901c03400900146011049401d40b4018041652816005840340b10207440d1001c41d61410305007081100d0010303800c082e0044820702c0c0d50310400f001582e24103d19a12441c680c02c400030f000407040000034245001039110f88403030240f003850204c108464205807110303441040321003d01c204a40004907255034180034050880d000c0080c425403900c0c0725810101e60b10ba002c2e01c8174000c26030b49001c050314101c6c5e2482400301c01030340301d49210b4032400c0300d08012074000c0e03 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 253839478 1250 253838228 253838239
    0x1103060a0308070f0503180f10020303010b030a23090c01020a0201200c0303040306150e070905060d0207021005030106180302060a180b040608010f09051303030e15042d050d0e 77
    0x101175440c0c2d4550f80c41008008050a070014034600305103440ca4a0740f2551000351210300c8000c0034030782c01960300e01060003001d00c0e5150200004030345210550040c5105d14088240007444150741a02c00407840082d95880241d020392032040203654000200e40e04030a5040e91114443c1305046124180700850710287c3c507060060303070b43c04000360341d040002d04091801000d000440ca6a1445d0015240a480d84408400c860303120803c0304864021400400b252402c2c0c80e503d90700c40719500303584000c0c807035090003d41c000d0813020a045450340c000c02035416182d081e01d40c0c014020a1607004041c0c03904600c0300079400202009102840f0f803062010f004500c02c6903410040f015119241c410300c5400a40254001841c0740004000340242c54011303c3c01010018070400c8181411148400f0101d87d8501c094281500c03244a40e04243c401c20240d40100052403080c4000d060619111980340703d58000140e40304c1000d8814138041c4d2400080002d40c980c054000d0410b01c0c4140d0090f650752040c0c210f81a48003 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 253840728 1250 253839478 253839503
    0x30c0702090108060907081c030c03020d1503050d05040e180106080303042108060f150421060f0507080403080702070909030302031605090d02130902120307061103060a030807 77
    0x1a201e812009018040c0c3c500507058914290031020700d001d41c150b0040030b10b42d10252003140058140c130140445110716241c0443e6102848100ba400792203a1911003007464a000d0013001e00d00c1c50100d08405480c841c900f500c40024502404841500681c0200304d80300c2e50310300c003081d600c3c1c850440310220b4005580010460725900c65003541143c20031201560000389198100505c1d210712104140d150034030342480c489508011020800c17102c0340c0c480c2e071030241112042908291541c1005d071f80050040c1c002c0101188009042090708580c00402100c01c070781000d1401815044602030b8074440c2540303039101411540c4a85041350110000341011042d4000e1002c0032400d580e0602414002c14001d80780561340b400d15481044846000301c9250003040740034844045107540b01108205050740480300ca10150764120031070002044403081c000d600802c0400b07200744c0d0713080110180c011240100360401a0071014894800e480c402101c0d02039110082c81020b10014040e040901031203400b1b4480c91844 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 253841978 1250 253840728 253840733
    0x90613051f03050702011e0e0c100302070c090903050702100522050108130b0a1512050a120903021f0548062205070303030902010e061e030c07 63
    0x1540000d00154880c1c0700300803150820503054010a600308010340f0007000000d003103d11040c0c8094804603428805038952400301c28039802000700210200b0010301c0706c5000d0250315806002507001e0b060842e0780001c10840000d007242c4c0e03846400f03506a05500c409142c0050343c0d0800c070300900c1456090080c80340910407010150030981d04818900c2d01202c08809150400c400500380100c02480401580e4800480e540080d0400e1006504041d075948041448000c0540816038203444d03411408070b035690444400140000002c0382c80105008240b02e0b6000c0c0d409803011150440c1500002e90401c0da00300840c3c0c02006107012801c0c1d101554500035083c404d8400b40c4451064010641c40700203000b4031500864071000980c21b801c3c8500c0302e80c1c8411614284e09142da21150003d000441107944880c2d0814042003074800d0f9015141d10000f0780700119124a00034000b03140c011404e81c001018583c05081c2802e10604035a480620050101c0c034080c0400403000c0542e1008200507103440701485035100 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 253843228 1250 253841978 253841989
    0xe061c05010603230607020a060506030a052b0c0f08030601052a07050102010b0307030b0c09030d020601140d0f0f080d0207030e030c030610060c0606030c0b19080c09061305 76
    0x550f00c136010040c1c2003203094a05442c408542104030b07640f9004001441103640d000200da150096010301d01240640d01c000000341800c038000005030150082a541944210314035805c0c0c0c5c0b41024800e508101c1c0e006803401200c01a1703405000824061280581e5004200c501014580c06041494241e02d05141b8251080c1c4200b081100b10001c1150100302a080300014000031020b0708003072008021400c9440002541d5210510015100022850104800112140407110b032000094111908900041c400941d00d14007407241520580038084080814603045038802d1003241c00984004644003e070b00c42c51b11048842c0c0c07040320a40020400e0014080160000c0c00115000f07032501c4010041c03036805d150902003801c0e400e500c070342c21107000c00c8200c8100c219103405843d0b4518040446031414501140205419003000d01081c00002c6c4c0052024016001812660f00c812070f424203840c1c2248050714243c0056400050041e0144491078090801802400301d0044906800700d056556501050 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 253844478 1250 253843228 253843241
    0x130c090c050a08070f051e070204090506010f0b0a050a08070216060e03010513020d030f0c0b13030f14040612061721090307050913051b04060603060e061c0501 70
    0x7184000c10100a216040410103900c03a01d0780c208445131040d41c810040051040c0c800c3d0701a500300740303180106540d0030a4241c503200d581c007400401442d0031038101076684610074866000035402c07840c404074111071140107a49001d880d0780c40c0c560a202e500441625801c0d40241280214030032214108414050700d80000300900d002d0700c1d054688078143d4189401c0d10002030000480d80c1d0451a10001a160311160050060b0546880d0b007180c42d5654088955440311752016010018000a10404122445200c0d9403103101351221141e560550b142030390100c07402c2091596120081c0700400846019100103810348000c03c500107603098480810210011207074010351110341c86610900803402d040a80e02250081704000c1c1401d180143e0002551543c040c02a82d014000e50380101300c540c2013500901180f9a030000640d07455540102a054416456044461269040003400a003141c000d00c504c2094952200d0318003401c0c1e0720101800a485100d8000000980700b031061400440c10078811003 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 253845728 1250 253844478 253844501
    0xc0c0c06080709050a0f090b0a03060656040b030c0901030c09080703150e030c0a03080711061b04180b03010c141218010c080604060905070503130c09 66
    0x10a40e8100b80718020305090840c1c0006014020320714051102e80c190b024900704544010002045502121000c5500700700740340d0004103040d04107980070410041d1104180da9880d100305000781510016440c65150100d0f00501c4c0310100518003602401d0114010941078000c103001c80c2c5c0b880e0a90720398188099500c1110310255519001c55030209540c0e25001c0d03000c1c441041d20701901c0090500c51805c3d10b0b11503500c0000e008203051031620b018034000390400d1408231019000d0301e8940c04d041e220740c0c0d11500403d100710000f543c003070005818980140c000c028200034410040003266036001000c80c500031344140780b90049200380400031340e29018070b1008022a01c0b5040100d0380301304007402d25003541c0b4812040c1301440b43c0110440d0010f80d01c1805e9500403405210820215140e44422440754001d000012546508054100b00110780019041e4004c40d01a0340400102e0307560440b9608441c0207560620006401300081003401d23590b00301c0c801000c0e01640050390540e07503800d020f40464180c048170 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 253846978 1250 253845728 253845737
    0x6060315120f011b1110050912040b1e19030504020d140d1209110d06060503010f02090112020702030a0b04080d0501030f140601270e0307060608060c0a120c0c0c06 72
    0x1c60b8050070108216003a401828104003a40c04900c017446034881c1045880b1710070f101e40d25000107610b290304200c0d2031072000c1c0603090039548030f4941482d4070305d640c02260b840e00c074401c0c40c401c9200905071080c210781c40c409440509200c1034102a400b1030241c000640141e911128241608021802c071149880350102890020070003044180d102614400f14080c002049614240384e4001250840c0b040400802c42114040d0303045005142c0640206142d41106405610301144448552240d9004003010035090300c1d11101c00780d480b024207059100c0d51a00a4054020442d554001526840100d40140c0318115050800754042c0300e18048800c243e1094411403282c4007100b0601c14080f044d41421f1102e1009805158102a1160005042c202c07000e0208400123840402e030305015407201e092344641c03a054968881160070304402804482c060400c80c4d0007a41d011604180000c1c0442c0d880041070744808605001c4a0440c2008084802c0366400344009558000001040390030003e002e40f085849 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 253848228 1250 253846978 253846991
    0xf01090e09064212060411010201150513090c0b0d020318030702030606010516060203150a0b03070c080d0e0613030810030309050d03090b0c03070605070806060315120f01 75
    0x25480c103c084039000d000c64540c03503222500ca0522070424060052004442d42c00103540d0440f01180d070b14002842001c415009180034802009070643c001003480300240d000b40003c44002c1c1d145034848461b48155a80700e40c404c1544440400190000007a090081c0016058540e54001941d0241d100c0520606a031b07900004001920041041100e98810f0042c01503040022641c042a034543d00640400d050007004601d28105000c80c440d0800301325400b0310b0944d12800d224500300800d1100410341032240b980307440d000c100402c40c01e084e00e1198030240c0c0c80c0268031083d500c030514070b40d01c000d0b04101210346442c1d00061280040041c0da0081000048030b010b0381040d03050082001d41e010b007c2c151fa00e2100c550400100c0c0d44000b900095880c1200c004280300014074080c1c0d654007040c0c0c0501491400404d483c501030002001424010b401010701b0311a540d03c00038201c40d03805040b14029840001032002c24110160040e0341c003020800034051098500710000f00a18120072a025104030303a45039030 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 253849478 1250 253848228 253848241
    0x60f020f04120b010906030206030a092d020f040507020615030a21080604020c120d1803080f0106090e0103080c01060806010f170a03020d110c1009030b13050c0f01090e0906 76
    0x22076801445e0b19035007009401c1c11a40003030464880980aa100243c690301d50105200b8600c039090340080320010358501d02c00d0501d55408025143c0c00701a1320600c4a840c1000441c00d00c0e004241c81a03640e540130346138640c0c1d65421400c00a0060450580601c18107803c10000f40c0d00301c100d11440102e144a2400b02d9520301c00003007400f071006000a01450062080c0301c14050001681041100c01d0200962110025102c0350020010030254801d44e180c103800e001c06060701321480500604640303418262036a202c0d541554005c0c02c40c882c0f00001071105d0300400c080b40d8550040c2c42c00140c444004100daa0f0380d501042e10307041080c0c0112091400308442000841d22207107140c00e1341120700c40070f00311050040d02c02a41781e00442c4008001d10407601c240c43c0c11040c0074448040352039002801c500141c0740e4400000c0c100c403400c1c0011209401c4903000f064121205005140c500e5034401d00401e43c20780300c1414411880b40102c01a814003081000128541a50030f5425208080301c000420340c628044 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 253850728 1250 253849478 253849493
    0x903070510050f1c15030201020628050720010207050c0d03050c0f0f070602010e0601061b0503040306090b01081603080a0e0607060b0907140409110c060a0b030115050904060f020f0412 81
    0x2171420f200500451081006036004035906a000342c010568082c242c01070f0b5a0b488107407580e4100c64a020b440c2108200d8802e422444590a00603a401c1c116060303a07016049d0b500302c0c0714028010b800c40c2d000c03115a0a15140c014114601d1921038901207040450402803589451150700c500e049075048a066020b0f82041041000010302061000f0f00030481a05c8034242c48501c10700900082181441803006d41400002208581320741c000c0440c0d5a80d40e6a0400800a000e002d508948044921000040c5200c1c0080e0120b601c0b031201d0381008480e4038603646c0300000d5011403102414010811003a4211356a000040d19125000d0302c8046610014a001c00c1000e850013441d08052107070051034885602c1d2810161010b03110102c500049415024032070300750b5800381520802c12803050a041220a00d0542c10108a050301980280041c40c07985c0703442c0c04085441d00600b50031402e04030010f0b010801d50303007001d0504181c084d80146020400c02500425a0182c1c20901864902c140d41800300001c1 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 253851978 1250 253850728 253850741
    0x103020310060b040b0c0a14071d01030b0f1807080a140706080118110313050705060f0a081e07020a11061c020703200c0108010504020903070510050f1c 67
    0x85000400c80c050900c10b481400e07000d6800381d1740d0441c01c04150020000c104100110080340c004070b521482104900596681e003034540140e0036907020790411980820420f42c100c5040e2a0700000c07000c0c07240e40b4110b844151000080034242c030407090340c005150401c82481150042c201d02c0000d00940d0000d82042c440e5642c03064a05501684805c1007040030541c07080c1c00c0c50541c3d240d10900702e503542110090602800c0c0241e103001c0600e1000040c0b20b66170f984600000d540307031703c00c41c1505d0b40c043c0e8400802c100e6000e8000c010005440803c100319843e84651407855000200e40f0004554079141e44541c1d0702c02c902180d103540541c2c040d46503079042c1303d0f890015811882003100d401d032401c542420151140e04a020700352024a8012032030b00c0030075006410101c41c01c4100d1104401d00110040135a0fa908440b0f1140c1d0b01007204040042107038103290088400141c0050024640c40b440c00e03041c428801d84004254080100c140282800030481100500c1c0008288001010040e40907500000300ca80 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 253853228 1250 253851978 253852003
    0x22209140303070c0209190c05030106030e0a240603080f0307022803110c040f0209130515120a1703010e01080d020d11190501060f0f1202041805010f0501030203 71
    0x10b02c100000c0c0c5621240d045416030b41916404481e8940049a03202c11503400140303c0c0c80ca00741107540201560000203141210226a41405241c03040b507540da858140001000d040540d40c004518108043c1c510380201e09812104001111541c0f82c41d806c0300390300202e03200d040030200001800503041e81082605030400e6004002d03100358a40460700c0306042ca054000800340f2040d4000494500b00500041c2400e00e400781c410711244610403040382c000e40c018940f0912401c00e50814804400007841054411072502a840001340340380c5041041c00080c114460402d4815913010b080001c1e803514040800780301d401c0700240c0b0303035050030000711038060144c11084556000815450352594002104003030318100d070030071030b00c0400d00c46410b5060007025141c2c0003ca850502d00c0d8000c00005500140031903000b400c102e5000c40e190ba80c0543d000c2c0b40361040101e62281c112040c0d025207001e500c400142e00486070344403880c09141e99500d09441c2c0a24440d0b6906689000400550809010000b0640e1 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 253854478 1250 253853228 253853233
    0x8120424050a030b042a080a1806090804080a08120c0c0303060103090201030b031f0e0c0a0605130e0406050604050601050306100c051005010b04060e0105070c030305030402220914 79
    0x100e409030014502d00600803908101a2104040e441c4c540312584444100a18800c100b10040340221407900e05d0ba22074658a00090715100018100200794860442201c003c8824283c120304c850f216600580142d81d01668001300822000550440c10843c03691201d10600719030b41c607140c1c001c0580500c1907009058014200c410400c0341d0300800080103ca80c00b1800f400d0001c0c401006000403801000c0015010781c040c803482050314031201000303c0c1042c2c003d1400d4030a000e084a0b0b04001d40e150040017240c1d0b60084245a4240100e40c0964007402110106c24008240c1340c1d603d10a80110000582e000d4442950340c2062015506280c000c0c00e078071042c01c1c05d15900c0e40c24009c011601c400c02600c503503810060b42ca0a03c008116052003400940da02868041c0100d5031074420402d055406480707039501040300b1120ba0250b55000354140e61120340c010309100411440d544082c1c40648c0000d20890b806142c021451041d0094500d014000c142c4042c2c00207005101d41c600441c4c000011341c50072401d907 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 253855728 1250 253854478 253854539
    0x7031a0103021315050307181d0c010c0302100504030905090a0c050405220504080a0f0216030602031f0e0a1a0a0b0a0c051c0e060a0215060109081204 66
    0x140c0b1880010f4400c21000580000c0e01c1080700a560006191a0005c40e4540988240040c0300062503006401b0301e95082800c100440d0301c0750800c0881b4080c11400b4a0907080240d4654841d03004048a19005010340181c82c00383c1d80380725440c01246c200700e0f0304801060064405000314180015003562001402074104610f41c8401d501030451f0040d4490507200c0d4440c40c609481140b0b40c003074138002400c0c0d100c20038412404c2c01d01c1c1000490300880d0343c0800180035000c10008152000441080c00c441c1001c850422a045803540000f951005000c02c0160074514684088509000141c2c4004d00030000e1562050904c03032044025182d21400d181c040044020707001005958543c00c1c00100d8503108000c0344d455034402000c0d03803001c403a03500c050024011000c910070200341c140580f401814041d6107075803004001d04100506802004c0351200181d1141d112403044409882c1c5940e00400141012031382159211002d600e0039110804012031524049000c100c010010100c88451282c541c00d4102038 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 253856978 1250 253855728 253855733
    0x50307020c060d0b19050301380117070207080106121a1314030301090606170411030f0d1101050703061d061c060c080c0c210f04060207031a0103 64
    0x7500c50894045204480001e90032038221110303440240000000707000c14030038500e54900c2c522040114419a4040d50a01c04115910f030040d40e2014010301d4002c0c440e51503130446c04020503008045035031a90520034100c180c3c0c0c448a40701c40040744111801d41c01001517a01b00300325242990186d1740025036a0400307224010004800c03205080c05031031808090030391741e83c0300010401c0d02011000043c140f02d91040c0c1c031240c440d00100003581a140503180c2485400c4d51034104803021b4a45044c070030400001000418001419030192441440e402800c407507103610b001800c24102426000c1c0c600c0854440020111180d500780038841e84481c242c01d080005a00e0715018818801805049410098000c070000c0c076540c1e1130060003800c00307540071460464940310b8a07103000101001c26100e408120690001036510613a40100c0384184082d002910241e90401c8140c0707107005241080c00076459080c003081c1451075980c0007400041100d68020010745141d402c00c44028444074136000d0b4101282c0005002 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 253858228 1250 253856978 253856983
    0xa060605090705070602030c041a0703030c1b020d0609021309051207050601062a06020705010f05040c060f02030d0203150108070816110a020307350606010309080d05040b0109050705030702 83
    0xf0313015048031004d42d0f01c1c0d03101d005400e0588102d41190b40140c0c60180312494641340341c030181c1181c5120303480030007914507502c6041e035280440018414a01c840809558010308000c40c40307550f120f00c03460000c51a640745600040d182ea41c2c42036007001280d03841c643c01c0306220040101030079032507420f0107036858002c06440c2e6a403190414025101440700c1c010604060f102030f04041003406401c0760302d442040080b031030f021000e5805413009032010b600780022040000300c1880750601841cbd105000f84121454900243d41d41c2c0c03d100707807400650100303224030100d074480d82c0000c6104a81c00c000f0a09901a400b00141c4400b0307000c0c09000070080b00030108841200c0d0f2405455412445090444000000b540b2584c0f0703004140f40000d40500030b10f00f00144c40c0e1100203d64081780021004000b0340030201126410f01040c14135180100d510441c08103030554002d42c00a884140207036405450084c0c602080b1013940c03403c2e10201e82041008004002c95040c5106540c2c000c00700c0e180103072460620000096 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 253859478 1250 253858228 253858237
    0x4050c0910030b150a0219080315010e0d06050901020d05010e010f0e0c090915061801120e0a02090a09081801020c040c17180f0a021801050312130b03090a060605090705 74
    0x40c84640000305d04007418002c04c450f070138458000341680c2410038070f4a05400b01c0d400550341185407884444205040e580115a59440f001014000c14410071701500d4010141001925402155500300075044ea0442d050161030b000e011904200e0340310b03514020304200944416444814000245001d1041c5500088111922401c00b00e4200c040d0b502d4041300744944180d205101d503407105000800354100c500c00c1030402d007003040c00d0700c07040b80b001c042111000980b06d071715181c128140c00401000c1e0061514204480d0040980c110002d86400b00c0e60b100c0d5001c0c2d02607524680480b4a83d08120754641e41000190751103041500c003409940c900c1d940184c104107084002d0454002d0980004048003660f88061003456008011a0195150403108644400c41a10283d010b622100908001403001c0c0324028104d400141c010700078500f0b5840395100d03a810202d103000300c85c4005600060240030040180d40100403d1001d4039602560b8503050b011030b145030348510301070080001000010703600039007030342c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 253860728 1250 253859478 253859509
    0xb060706020c030f030f0702010c0906020d121b12050601090f062601090b030705030106060f050a110d0e0405060d15020c0f0d02070e090712020114070204050c0910030b 74
    0x150301d07800c00c0b12809045000b01d81200d1345003a4044204a8200750a0034020b01503038130b0360020003c02d1036640b4200c03104042c034051100541e10000150801511800030501008100003001468801e220b002010f648664034140c2c0002e003155062440310030840c452640c0081c030034240401160704e031400686400c4160301c200014001091043d080720040c0c0c40940314a1100703c80e0380701056864080c0c4000501d0300b1405207029200d041c0d00803845007014810b42c1c040c1e445644400000c032061300000c9400d5400050800304002074041030760840002000b07141039400b555251400c0c5880d81405010444100820030b07803040c007201d1203440115020b1060011035180c801d5000d07036925101012545002520189140c0b10711600c5000c1d46c40a502055020542e03140201d0109507880e105c403078507a42d60044c0540e4095200b40038512005601620b50030000060380e51b1250f0074512a500014100ca0701202c0740d01544200141d56001440c007140c154541760b0706802c01700f01080301a000f00f002040d5100a2 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 253861978 1250 253860728 253860731
    0x4050705100201090c0f0906090902130e07090f0b120109020a0b0904020405060301170d0504150e0d080307030b0f040e0601030204090503070803010303170a05060102030a12110a020f0c040b060706 86
    0x56401e80d4400c0d00300700c40103900040a0070545070303607000070301078030b2014891040fa8034900003000c40c00301400c0c0107000016400403c0c04160b1000294881d0052071040c5010b46c49100e902c0d03001401d00c00e28000d51012001151f400038103081c5040500c052a00c1d11702c210301e0540d162414600041ea2a0030100056442c81003070a0745505080340490024462604902e9120f900030000203801c0e4075078070307101c010404041c0941d24802c0c41e10000391468040c502800002e11240000b000d440c0340b0407140704c002410018080341c05440141c0b0780c3c40701540191040800652074400f22803007400e01c50310f001a04e00081d1030070406020505605612920113010091040342c0321101c0d44140601001070301e01168011103c5542e95a60b171401415045101e01454880d05440c80060340c0a115441114440d08044c1c02840c685001032400f00c5042d607441450340e00d0a641d030301140d40c0070031800016014099080e00181450060001d600345840025030b50b00d841b035030030403d40440c591103490580d00b01e03d900090 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 253863228 1250 253861978 253861999
    0x305030711032505030c0a03020307090f090f0b06031c0212030903091005040920040b0901020a060509100608210a030b10030515010f211803051c0504050705 69
    0x40d003080c5080d103020780141c1a10031040243c01d00c0c0b14412044400c102c0c1207510350114082482400c1610340b00c007070751603044010200109007094103c2d80e0036404007180000c901d2901d83c0c69400360b000e00042503404500f030104114080c00d0070802480c1701c41f50107404c03920705080000002e581d132a5600c1d844080c14004404103a843d1001c0050311020303400104085050700050b14000d1a6801512074104c1d03103420005010200350380c0700030811303800301c9a600c42c5142509100740b88415520104800c1d045114698a01002c240b007841038501950008002d84a20b54041e0403500c29100d45800c015400e802c961a4001c82c4540c0750300901c0c0b020381d0303000c0c07050311585082e100343d006160062001e50403125070300c3c0560100e58143c2c0140c0c450404460980c0003203000e90f0044551107611000f00d0045140944810b550b11030146074030581ca00c440101282d11200c0c560452403c2d484803404402040c0c001c04d11200c11f0100040301003188816400c10806440e00d911007035aa00c44a10843d40070f0042d549 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 253864478 1250 253863228 253863263
    0x1150f02012c150f070210020f04050603060d0510060528030201210c09240f0e1201020c0f0601080a0b040204110408010e1608071a31030302010b0a03050307 69
    0x1211240704200560f80c64180351041c1149142d0108440c490300500420341e203075006454520070382c0c2601c0100f1700014149400c0006001040d80080c048680c401d64000008000030410041d208a41040100200d00f5601d8107041c0000507032010041d900d0406144507071564000c050700c0c2e5408813502443c040440c24031909000900f0100300c07450310900ca040c2207504042c2504025190121030444410b4845000b1f0404d50181820540d805003000640c007500c03050722644200c1c4111034036100101a07031030180d00140d844c1d08a074000c40d4900c5258121590f22043e10005110190041402e0400f402ea034015540d01c086400c400204001d00c62070742d881c0d56111210702601600c3c003504002c0002c020b046c54080201c0d0f580c42120090400d200c01044010070111000b01e4030600315600c0e070200b00041d6030b105802c1c40064005400325004440304d001c0c04c0104012904800c0380d142e102400e03c0302c000317003141402400c0d03071100751865000c0da03072440040000400000489031a15044402c100001c01c0b4803 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 253865728 1250 253864478 253864483
    0x914041107020a12030905010503250302040f1214010203070f260103051e03091c0609020a06080f07050a050901030e1c0203040608060d0c050904031701150f02012c 72
    0x310700103074021950100101c1c020004000c600384c014000e4071410340031640c42c07004480314401100c011401c4d0b407194190361021100403205150900150801606103511030301d050b05900026444184c40c021084419414002c070805100045034401c00258070f9464010030241c400c100465201080026055000412000c9403141e0146042509624901035a4030f082ca660b50395000444003240c500301020311803d03800000101e4081c000b02a000c0086d0056401d1000310a0660940c242c94650319074520000503512512160098599034a50b420b05003031100c840040160020031030b00521104001c0000c820350400240c0b10080c409207804202c940d403000c500e0703041405035450840140c45800500e02c0098000c8013800540d5500d50fa907d145d5075551040141780904068040c0c81407404000078441da061aa00740c0e6802400383c2060408010001041c0c180312100340c0c001c0b180c40d5000e44800205503488080d80c0403400841c4001c3c400d050b44601c00d8601458000d10154042d4002030340c502150b68103 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 253866978 1250 253865728 253865737
    0xb03010e0c07051b0f0d03020705010c060603080f07050f070506071e0b0a0506011101110406052b020717073210020408070608090307030e0a0302030109050c03010c09140411 76
    0x43c043c0c401c0982410100c80e03114155500091061091240c440c1e41800c002e400001e0050b0583e0081c00388920302001560450141030047d034095496000210100b0110002044102262890315030741c0d0340541007580c180725070700d03828882c5504031000403c00d5036168029074450b55002803410058142d403045607111845490740003820401010108a010b04035903004521404080e01c1d20785201c0314400c08a400c850340400c203504210000c3c0028026980b0802c0503001018030400e44090a031011005001c846118030340b0b4610f03442d0002002c01c1003105000582d0305141d0725040142c2442c1c0795581c2c0d0351010f40301d003012451101180031051038510020491040414440064030740700350107000f02030080d62140c001c040043c860101e00140151046198921902e0b4240196003421078a640450302c0381411206a5070000c0341c8440070000d03079000e10402d0035240c85640244010311f002e0003072600796030b800c06410301880045c80080040030300032184158425012200003480440c4c2180f6601c09008 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 253868228 1250 253866978 253866983
    0x90705040314010603060b0a0b0f0c0c1f0f08070f0311092206050303070210030c0e090108030a0e0102030a0f0e031510031e0804030f0201112a0a0b03010e0c07 70
    0x203030440140b041901940140b0a90780148810f002445d1001c040c0440000c51b4450a40139172070400564500b680b50101400130b01a203401603541c036000140c000740f40308510282600000311180f006100c180d401070f02c59016038815040410003464003c4014045220590901c0305050300c0c0c000c001d05000d513810844050f0440186100500c0e0201841c1c241c440c80320303107211106075181c2580414240f0b40001510070081c0d000740041104103203803a08402400001c440d85080c00b800d0400400e140d5188650a0301070002d0300021611031204130001401c41c03c10310728a606540041041c400c0c2594889004452495141040b4400a2111001c2454916101d4071011390800400034050743c0c49100143d4000ca80c00f402c100907901d18841001c3d6016082443d00402e508410881040020059818118040d005041002445c442c80c4c090710b00b49428070382c0111b544040070880b050444080c041811502809480754001a4213081c0c40c0c0e02a07102c103021301c054050200000503030280ca40340446a8655 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 253869478 1250 253868228 253868243
    0x230030414031602011403040206041a04050a03120f03140109091a041a010b090d330501090c02030c0a080c0a080c06160e0d02040c05070609050c09100f050907050403 73
    0xb1030005600f203c000d02c00400728009111000d150302144500d800f070b030b40031b2900203000364a01403400400d0b140e24010031907065240d0350148030004460b030f40e0b5500c00300254000c1c07406000c4d808c4441030003004503001d401014141440e2100840c1c0b41c804032000c050540e40685400640d45107141040343c0c2400100310000c8510048208100401c5100d604804403074103c3d16080c502a6243c03900100140604007849401010510400300480d5000c800e035000b43d650242800c2c0f40030765042100080982a0703070000022520b910041055401c180300c0d264000e856840550b00b44540710103100e88500d0f101402400c1d80ca000315a00a665038140400715800d60f00c101801d5407a401c0c1918540c40701c0c41100c040c0200503a03110001c030b0301805000b40c4d89941c20002d2030522416550380c20080209200ea061703000300003086c000e1a000510a1140c004481e0007100101a100c02c81c0b030030030010f071100800354601503001c003d0800200050f028580207071041280c48601e1a0b986640884180c062540040d2041 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 253870728 1250 253869478 253869487
    0xc0c04090c03020103060b040e04031d04050709051f020a0204020c0c0d0605010609051c02190b07050c030613051b131409120406050405150702030715023003041403 72
    0x20a019074041164401e89082c803c4503550003a031041030140d07118403003001200d4400280060700c245840c110720580d00060500045a50b000b2032b003111422100c50f0081081350109000d146843c4041c0210401c13405960031b4910760940303000b034aa085080c4002d02881e00410401c2c4014410702c07110044801c054129403c203265170a041010740b0742807040c030002c1540780f400464181800c000002c0290406c20003803c2041c0260b0a00401104104508940603011a8041445030a140041c40c1481c0104000c00c5004c0b00300d010142007807406000b01c00d0354840381c01c000d00040d501264801702d900300001c41d12103440095020881c9a10000b001c2d294080c94010700d81403021806644501550458044902d45140c481e49112188a05d0241501092085c4410040c0c3d00d070043c0060110028032a0244c2860610fa000c60b107480701c0e039000b48240d100d25010400030240d04100560300210103500107451048001148640640303211100020746000000080078441d5000348480c1d54500c06d0f0440c0d998 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 253871978 1250 253870728 253870733
    0x60e0f09040b1503070f18200705070b030f16090b0a0804060c08090718060503030a03020319051302150c0a11190305072601090503090108160c080c0c0409 68
    0x50012100f18015442c0d803c0540701500300010000180c03000c4245120381c550402081445100c080361a0b00c075590b440301c0c2024207900095440300d000440342c030585a1145500d1904604184080d00400c01c6080d0600030044052900c4038002c1d0407102038104840300000c0791710201c51005098101055440c07001030700061460f0721100c1c1c00e100700d00a207801c002c2009030b80800c8070822021307203540c041d135400014180107206c03801c8000240d01c0c0b403601c030004400c7d6644002c2819a0032176060341000c25404020480326407441c103180b002c02040e5003800c00046c82c0c245820b4080d003268640103802102c80c3c008003066040600308844030360040c80201c40e1440c0652401424940c0b56120340390080d10b03005903140405080880c0041983d607c00060540182040c40c440042c0c91508007031803210404030220000c0510a1099a003c0c40c001c2e03016590300e80c10100007404540c40a441d940c1a503091016480381554002220103009500803001c95a0340d1400b40710f18504564821a50b2b17200345440951800c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 253873228 1250 253871978 253871993
    0xe0307060e03070b07052a0405070503060108042003100f0b0102030313080a0c020d230a02060415090308030f010f0609060203120604061805190920010315060302030901060e0709060e0f0904 83
    0x8001030225001c9c00359680b00314003180e80d40016650307107000c210300303001080018460000e00d903a0210b80381c50800c4420642000a40b50280f28241011150f955107900d01448149009421707182000780020f51441c10152015091f01c041244003424540002c02d030703211028411883d820060350024160781200702207003440e000c2c49401c0e09400310020108040c401c0303206000725004614507001050b40b824140b41030800c81000f05016001c078100081c015022000442180103180603401c8083d03045242c0d03041c001004007800880d00b1000500000c80700070802c0c3c650000456680d640c5c550550a8661078200110300a4045504141140c0343d0129103801d0f80b03c050343c05288280c11083c5e29810019001c00c6071003c980d488840131307020b103200707103419594010081c486002c0070406140000300e03078a007101805810380341c5810500020703400009000010109014050217005000340c0310030300d818001d07800390489049200d0030741409401513000d1400da80c1e2507200c45040e4000741002e0b4480c0741901e041039 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 253874478 1250 253873228 253873303
    0x170f030115120507140d230f01050312070602130807120203060c09090609040515130b090115181806050609010f030209010b070813060e0307060e03070b0705 69
    0x2034160452920748811802254080c0c1c2c12910b172070304206031150800a0551080c100040d001c2d032140c40707046801600d006031041c101c1e4103107000c04041c2082c0201d10400c0c28103034401c61003940241050144100351004a44240b40d0201006990b0301c0b016401c56100d03100f540c060006409000000100300200901c0010a103200710180c418595407034032342050314010705840740c0d00300c0c00c501d00003121402c0074044d071a0020f005100719950942c1d143d41c0300018500031204c64102c0304105440b01c0070450b81e40046900f01c84004000e2102e40e00c001c5681000d1800f83c4204268501e1511050b4000360242c3c0c48100d000c5082c00e982c10383c2910904206014120640d40580108d118400014034024508598800d699000b8034400c600d13481c1007002c500c19000081305030380d581800c00081c42c0540c0d1403040c000041c041d0342c89610b41c2001013000c01d0304040e00c592286050118115203101c4668001c144502914403444010351240b0300c5041c440d15024407800340c04401d110030404004195071031030449 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 253875728 1250 253874478 253874519
    0xf19060f0207080712060b0d06090602040f08011404020405130209090708120a020a0f021c0507080606060c06040803090102130b0d0605010504080a1709060f030a0c020d0c170f0301 79
    0x4401455a0f06645582c13000b40c0d120705205000d140f4848000240c1a802c0201c0c100002414440b6208040d12004101ca0600004807112071340043c040098010a005180c000c00202008002c80c0040c082554400c03c0014002442b07682c2d120005559160f0102c1d00c1c5120b5500a028284640303400e20445985415070302801e4014418000084814521344046910703079a81d55004d0b2501e8007081d55004103d04410310100c2e4000c009090220607100082c5039041c0c2c040c000c1004080003464000705c01d003811070103400c0c2400b40301e00b00705044290000142c034a800c0303948040c01c15601d40d0f940004900900605031070000e448d03d101d600150083e1008080c0002005048080020542c0c810042d03403240b1407440303050380c42c1d00321042080204004003d0702c841c030014a00f01a2078900d40303000203466a4024032850001d80710210038008032171120310401c0780240040c0020701c00000314400181042c0f01856004107000c100000305d03421005010155941001a04003482d100e5071100140300541051184c60b = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 253876978 1250 253875728 253875733
    0x14040903112a15040b0a020a140102030a052203080405010f050106020a1101080403080609070c060608100f0e1c0201200403020315070509040b040b09040f0219060e0f19060f02 77
    0x4a02c003490300c00c0b958001203400030000e5180134942186040c0310f4203d084c2c2c0d2020743c0100821880171540c0d0200552030441c00307030700040c0e6919100c04800112400a0a88a41000900c100462041842072490412034050800001590b198a8181d0141c00034440701d29241d42840000510107400080a00640d8402c90000c100203e90000440701c000007120040d00103040140401c8c0c040c10314000f641d4000015107001c14240009841d05820f5402c940c0c00440554440305c9410405462403081d100c410312090700610494014207012507a07128421842d45401c80c410b40981c49090007548101d003044484031141d60055040e41c004011034225120a9009020301480c0100c00a50460b03d540b04507407a854441c207081241062000900b0565401038000c2e075242c01700c0c0265520300c00c0031442240b144403811000c101074410b02020741240100543c10040c211400d20103590046881c490b030840545540406002e80000204004880700c00940d40c2580c825000c610a070f0b02100002a40d0b40d503408 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 253878228 1250 253876978 253877053
    0x7050f0f0c030d0e0111010501030507060201150f0303030216051209280e072f120a05030c0d0b04020a020607081003020607080c030f03070207050f09011404090311 72
    0x200291641d541e600d01560540160b1a0421403500801c92140140c20602d0501201d074440507103507084400a070803d4074507910040003080b10503424012130b000103035080000701c8054a031220510300001c2502000b41456004190051007503070080c08605101e4100c0d0480d0440a02d01941003180e40c44160050b00502090349a006440c40711030046004103000803da0386214603140d050401c4000280c0120104031030a8504090801011005005d8144041d240308400720290b44107441c2502a011640d1043da040c07181c803200baa0402e007a6507100250031021076130fa142c10244040184500c0c4601741e440f600c0807903411101907001030018864021606c0e07161807600c031154003140daa0568070000b903200000704080c8000401c810040d1080071160011a0700700024000a400c0c960004c45d40440180d01070b810070840ca242002015903480400d41e50b1080303d50400781c0543c4090544103441d805580c5032031002013010f2040110340320b50f072081c0c1c0548540ba00d0080b4540d0416000790348070500e5042c40403 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 253879478 1250 253878228 253878253
    0x150903030c1f0b120a12031b0201060806060a1805040218070206040317010f09150537120f020f060d0b1509016b0c010507060204090207050f 62
    0x31310401c00e0300603a0b005003c60a50341c0e55150024489000e00c00c20076484a807a081c0100f03e003203259522840d0340d00045503c42c02e040300d1f18076156004101c14814001d004007088039404400405209a12000303000c2560f036183e001103007941030b5044070303610094406410405060303404186103001758444e940d00c082d0740301103c1440b0840f030028050b05441455001d000c00c1144001c2d802580c00000307080d4865800350b500c100187d941202e108844891101d501d1039102e100d04d485d4100ca07000d04118049a802d41c0c18095510200916001c00070f00c14960034009005541c0d40c4044000e0240c001000720340e6601c500f220002c00343c08a1542c440c010200d04031102e0024602405a84c2c1c48441a950400325a0f83c00c088229a0b04030414800031803030481c1123818181005061002001d86c4441305858041c001d0304140004008411a1010004000350340b400c0e01c500105c0d02100034402480c145d43c81d0310300c9090010007031003158030211200b44009903520400801017245d00201001c0b40079200c13400713a8032 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 253880728 1250 253879478 253879489
    0xc04080f0a050303070302070f020316081005070e06070203030d0e010606230306061c0204061701140102070b1b06180c0a06050904020d0912022505150903030c1f0b 72
    0x2507400405030f40080c000660450300c29806003801501a0210456001954020a0402880c1503609a6000d2415000e0094001c1080110320009a000781080f5500d84284028550010502e00a101e908002000c50035994200705075808803000120420801030010050b43c0201000c0c85401d011595010031001c0070800e00502607203a80440c00220b1948d613690b4108080c5a1103c070700c400d51b4406a240800d020425880a0005094a134890000c0500181c11507418510164011101c10903d00340e100040c0e40d0101c2c0841c101c0c1d40c2000c0d00c5072a180c03421082021a070160704082c03a40d02c108410840c003a01252421015855400283c1d2004100c4a0a102c1d0104441c05200f022450400c66900d9504040e40148045c10041d240011f1003c502e544102c40a55845002e10069100303040c840c0c002030b42c200c201d01c215000d2291013480c4600d0003006c5410741c1d2542821580440c0085440a05a01c050003200e4003c444042a10500009000910800058426260080791900390320300400d0400 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 253881978 1250 253880728 253880743
    0x90203060f09070e15180402070602040b040e041e1a0702010e0a050307021305101701090204060b0318030408190c0806090a0501050f010f091a0604090204140f010c1b030503030c04080f 81
    0xb0300c0303141c03040710300d8606c14000650b208500c1190040d03030030000040d0940014010b40050300b002821002d44d41424107003001441940420303440140f26103455400003401c00c2c0300076801002d504404040c00d030341e1950103030f00424280410f2200340c040c510300c1e17004011000c07004200c85031080b1000c200b03108c4185045411142c1c101c8a40752101003040040c015811000d03600075600e40d2510000c12080c0c00c5d9400314040d20b11030317849010f0f851000f1091040c526101060381d500008880000c7d03060030324100c451903480d1407010407040400c01400303643d001e000c1402e02450203005810700b02c40003400c022504660b5566004015281c552a14012907456032b005842d0303a040300c081c1081d90543e542003966540c001c0141c5100029901d0b0101e4008070180c8502700035100400d132201c1c0058485243c25005442e80911492461103004046d8400700c0b26078000b1903280100f0f0700304074481238062401c06143d8041d8110f80018186100c007208000351111038000030f20507a504403041e2000c10b0190400c40313965059 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 253883228 1250 253881978 253881997
    0x5040f02040e0f1207020907120f060e01031a0c090402090d1406091b01080109050c1e0c0c220c0c0501020d090201031a1e0a120507091113090203060f09070e15 70
    0x40c0d002301d241d1510a254070b801c102d401c1900014140303002e00c0d001c01140c1503039209540810b0288010018070000f420404030800c1c1a0141d11403e1605400c00744140c414120800d20031507001c141c1002603126041401040ca600c000c04010300000702842a64615045480820138810502e21a5458840340340201c0c5910060310b4a480c05c0e4280410103014000007800d0100d00c079003e1080c49003102942c0b814100380b0b080594242c4e81d40312454006410714180c9021035000301030744107580c801d05150f40428900c40c100e5500c0040c10b54205034049400c055004009402503002103130f0700c0442c03000c55002001c140c0c800d032010005034a54800c0d0010021049144d16880050840280ca46407106d00c1c0c10842c210700142100c02140d00c8010030099444c03e01d100399001c1d40314090500c0500d074544130323500c203c9018817241801c189003503400900d01c880c240286000035401002041080d2100001200300c0d44000b080e4aa0900e8442001010a036504a5580c4192a5442400d044502c0341003190707014030 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 253884478 1250 253883228 253883239
    0x160605060d0b0a0b04181a1803070f030314010303031505011b0b06041107051c0804051b01090302091801050601080727170318060906090405040f02040e0f120702 71
    0x1561081030f080205040c81ca00341c1c016448445020400c9440c01c00030350014452042c0000741d04080f4214130503100b00610a81d030001841281101494001090742c100340c1e1300840007840e11404e403404501a091507003500c25900d4200c00003104040d00754000c0301000401d848a50701041e03840c80110303003c0043c3c2c49100300c2501c0c2c0300c101d040426045500103034000e001034004110503100030341800103a0b1000c0e40954442d004502c1c5a50f017040401101d088106152a00d10000d040680303809807100c000002c0c2516001c8401d0403039003540d000b203070103c0046400402034415480d090705d030005542d0b03040e01c5d009038039460305d40000c1166021340b10490041e0300c541e8400300240b8904034080700044113950324000c9856210720015039490004206400e003858000603540300c0340145141e0100c1c0b607540f00e80d00c3c40f41c002440345000d0354032004c0c241d0748203420485d0302113401e0320f450034203000581d58040080e4000d4200100101d8404000a078107800c0200c502c100c0d11035040c160075000e458055160002c2d4001c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 253885728 1250 253884478 253884481
    0x1b180c0f0f110f0601140102151b030709090204030f030e0102061909052a031615031a030d020105070e0414060103240f03020f010203030906010b0c12160605060d0b 72
    0x303510454041035900c031000103e8070101c00755103420740381100c26400b8038071b114011000100c070b42d40d05114604404a001300361007850304108610342a0341342d2101207096500c10100001d12054440c404110050007200303c215901c5480c1d00300000309090400b0b0640c017007408100120172075440003c10500c500101612081c84036900e041180281050b14400c3c1c0d141c0c8941000c0640e506520100b81c0343d000c50100700e01e12640158001d05041c1000300c2c4241c8058001840c0801c802c0e00314001c141d00298607840d002440c4406603514401c0c8481d00741780c40d9054403926949040c1c040d01503000300d002780080c0e00c9081c0e58501d0300c1c00300800d590300d80340388460141c417540c007103080d5500a80109101d03044042c20809416500300740b15240f18080d5011481e03080303a02c101003065050024009140710000e10146240d4030706042156900d15040c480c10007400400a14035402e000c007809006103100014052640d00c00081040302c22214903e0026a0518504000b040c502e01c0d101c1c40c231611041e40032a11055a = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 253886978 1250 253885728 253885757
    0x30f110a0b0307080a0f061a03010f050105070f020603040c0803070b180703030c0f032102030a0f0911010f0509061c0606030905060c0706060513090605070504120f1b180c0f 76
    0x6041c4e8041000c443c9600c0e40b0300818824100c0c40721106a541030342c0e0748e40d00d80d803414810a00c800010f6200c603050240400c5180041a66084001c481ea07405581807692a100d5150421a00000d6800b440181c00301180c40c02c1041003814041c1e000f41645065034204042100c0c406844000301c0c4001004107100500301d070b0010718184074500907107003c0d007007040c1220034203180000c040302c052800087d80b5500104003ca031082034862a45243c00c040c104000d04861030342d49500c940303100c0f4151ba040c40340740c00c1010201071084003125026040502090b444580c000c00e43c1001d461703000703108812641400340100c0d50922030311540c03594a401c0801000e1a44035200d1400d01350b4800c12058a8664482d4070100703544c0c03100c044414020340c0d40c00c00040e4200a40c1000000c90f500602520f04101c0b08010420403949160100b89079240c00100c802d512803498640f41c2004032503139035030880c0c24609150005188100c40548402c00d4560340051101c1c00d5030107821902060143c9050000c41c0409440c65070 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 253888228 1250 253886978 253886981
    0x1050702280503040b04030c0801051b1206030f0f0c18091f0b0301091a0714040501030c03020c0a0605071815120b030129040204030822030f110a0b0307080a 69
    0x720140100142c92400b52501410326036a07125400640721044110300810004c81c0c244185c0354011941018485164117428100109208811006a401b2800c00c007060240d5802d01084003100000c8049810b04500c00c0400c40e150700102d8601842003501e0740020a0503904041d004d40708032081c0d40901400a0354950031240c941c2d0349003900c40b44541e02c13600c050345a01e0910070118054001c0c4e030600c501074110002d0101000d40106403108011400020788500c90705602540d058030001d0902048903038440503310700034002c0b04405101c61050700119401d0058603401075004508550762607840b2201c407100381c180300b5150f11480030f800c03103c00c0301962840c0c801c41c2c2c5480001200d4401080216808001900f5107400340e0050082c2809802103000000110100781c402440989080d801c05195841d402e100f8050703c0041c00403200e68410400300001d2002d201c2c0081c44e0b10500404e80821a82812181c151064010034002c602d41030000c100182041e055038412080d40d5109003031940d52166140 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 253889478 1250 253888228 253888303
    0x605030111031f0e0108070f080a110f03031c0603030f081302041a03030c0d0315060210050705121612092301060f0803091009150c1a0405010c0201050702 68
    0x140f01400e5071408030342483c2184020b0700070803060004140050400d03092050441195105202c207a100c044400c0c0024070b80741c42c0070030020f000c84200e184040c041c1302003403c5215001180d00501c0240c0c503040761301d03031240d03008034192070181d500c1012100402200f03036403115041e03680b229180404003d01c2e0041c50190000105c2c2450502c00d4000c07181c004c0c000ca46180c04c0750501180640010700c0c0d058403943e00d1310401d1b181016054803060040d24044000c0d40310002011b951085648403000240c000340076500f2114450348a83d40300e02c40c0d02d41460b90720308206180d034440001840e0111004909103150041c816666000420101c0519024801c004840668281300c8441d54032800300003840504004220000c21001e0301031a42d882c0301c0020800401007501c0d030388050040e518401d00060041c40e041d5100c81c80c0904204102c5081c2c0c0c1008400000009800e0004101c00c10400040040640040300705140c01c2d00203008a0326145016038a400d503100303042004403240c2000c010110104035420 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 253890728 1250 253889478 253889521
    0xe04020406120311012d0509030702030a0b0108101b0e03100e0d1b0b06190302090c04231c0201050408060405060709060509030601091e050712060503011103 69
    0x41c1c05540c840703103846020807422040d80420b1280d0350380b012400e802e004140c20066102030040d114018003640d20456809407a10807500c81d0f8410000d94107075030030000c860b4516002030454810030003030301d81024482000d010f4100180140c10302c5a480c000c2a00404882c41003a04903941031852001e0f0843c0c5544202401c90390500c662071036008200c01600c602c002c000b0710600540a07040c60b01c0030141140750f130f03801e049510f414642c11a201081403014096040401110402c1080d44044034480c800c0c22250006540b0070040c10a000d0200c1c403000041c400c803030480224800c0c000362021284c4810485104e0a60002c105900e4003a45113042002203183e1441414050304140d1500c1c00d01703241141c202c42c100c45540c040400c3c0100c072131b081859500141382c2440d200346060941404691a0401032040000ca90780f00c13600c19071140c00755400050208030700d0108000510b4940c0c002000e00c034426096186e00c2c1c0c82c0160106050406004a0054468a05d101455900e5240c2c4030b0070f540201d0f14a1 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 253891978 1250 253890728 253890731
    0x10203070c0e0a140903030f060a090228020d14160b010902030601020c030d0c08090a170105011503090302120702180103050f01050a0501050f210a03021c080106090e040204 76
    0x3000c002451101e8800041d1a0019114803903203004240041140e1400c920713078011500c01000c00041840010460740e015007003c4c1e803042680c5a07140441c0c034050385508510113079030004c9900e482004030412410074038081c2c150004100c1d100c446059894088038514500010b030059408810080804024051100c1d101005180d00c6220f456008058000f81c1180c60020303000410720005682c100b01c2c040c0c2a4404401034203a2201030180901500030032500107200d108082051201c41c0c0c0c032028510014124200c0318890b0b40b03c1003045500800c0e0034041c40350b8600c0200c40020b141d07486445841c0141f503150b0020a41a80c2042010181e0703001071104a030b000700c080d48030307040200080034081c3c02188160300034510000003c10a41c00d440009080d03468182c6040c004108a80d8de40341e0007420102c040e6089000f154424940500021040726190302d0340c490210340f0300c10103500040144a0030802004080e04581509048a09810a00c580c0c0005860f0395024081c40031144401904a44020700 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 253893228 1250 253891978 253891987
    0x2030a14071a040e0601090503030a0311070f060c17090706050c0304050d150609090c120201090510020c030f0f0607050a050d050103060e06090d080c090d02031207330b010203 77
    0x404806030201038002e0b5180da140400c0401000300d9030407243d900000b090800e40d152030308020110b0b68078040c03c001c240030980c43c0c034003502007035203e80104d0b882184c001022850b414110304149015104510305c0400284124520080052840103058011a404409006454a03081d403c44031600800d50344c0f800d40c00301700000545e540d580b140050002c5c0c480c6801821a414000c1081c040342c0c0654800d240c540c1c1001001030010f01c0800754501541c8147c0403c1020200301d0004880d45043e82d044580c114030070710038540849800113061346900b003084049480c400e9000700407a840b0407018016006507030210002c1038543d4060400b50007861114a03055080c482d80c600d980042d00c01c2030b4000c1d503035140d591400c203546010502c105c80c0c1c811010381c010541c01f00341c1a40108015401401c40801400c0401c40f201130f581d0f210989403005400a0880b0802d02d055000580c1a40c054070049070303401d900c00380b40c00406c4404055540720346c1c40e460190802da51208d54110203081042c600a045000421 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 253894478 1250 253893228 253893239
    0x304060e03070b0301060201050f010f08210c120c0d021b10141909170606010516080304060f0b0a0f05010f090e09010f05010f03080301050d14030706151202030a1407 73
    0x6135008050039800410a410410100d000050040e0081c0808040c001020b100c112400556640749849aa000c541c8600d0111800c0285000b02d5400e200c4074024210035100c0b0340944400381c8030303401d0403800782c0344c03003548485040c1d0f92a90b14444a000c41118200242c18501e03142c00351844030503c1c1d0400c1e50703083c910040d4038a036907400b03801400440300400029690f884d521009100140201d5448061080020170780c8650305c1c44010019810007a0000e100803d5403c0c020070240519440b2011503140e05180c6480c0300541500c01020003003516000075503500d86490010b100c1110031072a000100f06040c0001180c01c400c0d8114081c050046c180400244072030b00c002e5191007822100000103000f500c0000480a8901c10703807010b04c4080700c4d0074050010070480300441e411203030201e906c038545018601d0310a615046150001c5d07514027021521005201040c1c2041d038100c180e01034100c032070a0305e4051048210a0410000e5019444010004002906001d1640310300c0710040807540a0390781c80 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 253895728 1250 253894478 253894499
    0x70e030a0302010e120703051603020309040903051c0605060403151803050a0801140a170106030602161a0114090603010b03160f09020316120b19050907020d020304060e0307 76
    0x38801100140c2d910345a151405005000c0d89010f110034201c99031a2000c1610000c255009100b500305002c6400c0c1d418200b054020401c4421010025105102c1d0313620505015100f83c0000440090080f90700b138520b12030b0402032181d207041e1440140304904003811500c48a01404150b6006450b259032411342d0b050100050003440200e0b0322907039038282d4035821174900910301e4406a1045c51403070200101c1000a650b07030003010f02915010240c10004400c083c0f2442d01406050b4400b038455480044d007081013900d018064802a4001c03540500d25a40300e2003d040280c609100f101d84000300c0c2d5044200d14900305600f5a040b110040c008551000e0301d000107414100140b200c4002e4104590007040441e00b014038010060140560450842c42e00310114090304c0340086918040000e0700f0000c8030f002500d82d111200e81d20018286031001c80003400440500c540300d0142d41e10a030b4030342c3d0000c0d01e400e10001e0302d100c0e03207221580a03604052800400f41e4a401154a29035418001e0000100706103590 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 253896978 1250 253895728 253895743
    0x12040608090f06220b130618021c08070c080a02150f030c0708090a061206080f0c0d05070b04030305090103050a0216020f040204080a0c150f0207060516050f15060607021305070e03 79
    0x34551b098081c3c4d02249040401c4800c0711404140c00c00c2501c5203980569a107450144c5101c0301c0983d43c500b155000c0c5441260780c4900b200c001c02030341080300d012940040000f0440c074628400d0320890f507220202e1800f18690700a0000766418000308000061080d0005001303000000d1058003e6410308090310b001a19000e56604564001a2052665003414441e4000c210023042410054040d08840820468440a10366451402918040043d004000c000c00800c03008049140c581038540e5100e190060103030340030240c0140040d08000216144031b02038800c884280322045211200c6a0725682404440310f6003100c6107502c150300b0301c40091001402e1140c034410a2027203c210b4411030a1007800e00d8070040904000d800c00135003180122000d500010b114080d5102400c03c503448010308040e41d40007200c10900241107014501700d070746450b800013403224401c0040140300c0803959030712824400c160042440c081c0d44201501c206946182c2a54422a0000d02919129002070749003000f00c1c0c40c2001 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 253898228 1250 253896978 253896991
    0x50303030702210a090302280602060702070b0c03090f19031407090b01080a1503120210062102040207050309040e06150f0d0201180812040608090f06220b 68
    0x85000340391018007000ea640550003011142d03070f40c1403074040c2c030f401051100e131404002c2c010042c1c404008640f03034120407000e00600b5002651900c2a0b10380c400203440311401e0750000d01502c96194040b030880010405d8407102d1501000031820720710700000300329806d400c808256405c80715260303c500c04c02d240c07147c1800c007442c01164115100703070148886500d89403466108c5080c2c00d00d402103080e601d0b0707800190240c0107501c40c0000325580301c2c2d44401034072030381d200d6000a018030304017441034405d142c001c5422110f00420000c00c004031503507480c0607000401024690302c074201105000500514040d8084c1c809103001e03030122030030000130401140441d41003007003e10541e070081e0108168001c2004040d9a242c20548098908817070910203d0346000b42d13114024180702100c01303440c0032a0800d150100061500004441099501e60500c2846902902403640050110800203051100c0041d98030389452100c0006d0403a03a07905100b400c60200c9550003011b41c40c0e44c00c4000c030003190500030032600644 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 253899478 1250 253898228 253898233
    0x403171315021b070506040320060703081501030501060203040603020a0917032203020904080c0a0210090611160b0309030d0908041d04020a0608071101060e011a0408030307030213050303030702 85
    0x1d0001e8903e809005080540249540544401e118985680d01540c0c00c8a0344141961601c07c0007801813103400581c3c200c901d410940105800341410b90101c103040c0514241d848a2200e88043c800450590b03009001d001c001d0392013044100403035840303039008001460703035840c0064201b6200c00048201d0000b040815809901c080390001420344002c0d00d04141030318402d0451400c0c2d00c2c60303002c0350f44500014805424502c01141c1e070084801d00344075400c44c1c507900400d03050644d9144000a0b140c20014000d100c00076000315000444c080b0000740480303000c0001c0e01c51480103464548064440c2d0301c010403060302070000380803001a41c50030b4000c01814911524800e03441c0c50402040c4684201c0c035000400080407071005002c00b50f1034400e880301c03d07546649000391103030303541c6501510036000465606841d9841d0031000515444900000341c1640e00820762261030b032225400032039442c01903000e201d0b5a60010008554494040d60040402640c0200c040381030f580d807440003a04542080741c2000c0541c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 253900728 1250 253899478 253899487
    0xe120705070f0e0105040b0109030203060711010627020a092601050703022109070b0c0105010911070503042709150b03011e020702041503080a030e0303040317131502 73
    0x103000c1c40240042c00041c00340c490302502c0c00203001d8440301c040c4282c50041b0795842444a20764481c01d90700c4080c40c0c000d4121001418101801040103041c400b0b40d0314254030f800804100d840310714010400040c5111513050b5005900c04260000358000e002c21010b01013000360020311059424a194500e00c0011125414500e80c2c000940c00d441000f05648201881002003075210b101d0219900c0d165001d10086812542d6004201c0c0e00d4600140c100c1062203c001c102030344500415081030703050300c80d000030511020403042944e050318003840800800b25042400203120703041084004644175442e521101d034010a04044640c2121004a81034450200cad00300c803852910100e02a800c1c0441c0e0540080101104c0b450864410510651960040c260000f40410a41da45c503084071204a000d0140e440b2522355900c1c044400394404544074022038180004001c0605000c002e0300e22494054071001d075012503035000520a180000d007447c074072680000b0108041041d42c09440c50242c5000001a5030b03 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 253901978 1250 253900728 253900733
    0x60f04051504020607080c100203090708071401051c090b0a0920090a0c030e030a020105160c080453071503090305120a05010e0c0901021f0e1207 64
    0x782000003614500c1c02000505000050300da1030112100c090700417506d540c0300c44401c1d40003402c1440c41c807003070f58545001001b800303550316001c1450002c0b600c9071001ca50740b1340e5a803034509180704080c282582c08640b0920501d1108a5080425003482c0f810710000641d549141e500d801e6034200a0721951495a507942829080003015486021400010003422020311940000548415401001450600d40740c80410100e94029040744010343c54040540b500c400d1503020090091400300c40105903111038640184440d8003e40e01c152040740c020101602c2c0c41c1c100265410594402c03034102c0c200089000000d40c09034419400030b0b80c0042144201c031600449500003101c1455400a03e42d015005010200309441c40b48110104030b89040c20003040032162802d054800b4011108008203001490b000c02804110540c4840c1c1620103880040d559521303504450541030040e11120b9001d079001700e202400c1c100107803800d10180782c00b5480210f02d0710107980800f41003a08502e2801000c00e004603400c000c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 253903228 1250 253901978 253901983
    0xb1b0318040b011d0103020c011503080711150702042c0106050901080313050910120309081902030d031a060403080c1c0206071206150e0a05010305060d08030c0903060f0405 76
    0x8860134604018404807106005032003c204c038024506142e4000b40324982c0450a4020151030091190207002c026502d06044255078032121080780e1a42520305414203900d420901d0816403000d40741d081c1c0c20020b1541c203000040031a0340403c0003d182020800c82d82c11842506141315110210010415600c2c1c042130103824401038211415540051000c0302008910308106811948221050445034444c0008004ca01c0c016422615405652400110034190801240c2e402c9400c40e00481d460725240f03c4208010002e44a4000d41c143c11144c002280188250425a5050309162031040101c6040c4005281c50780107074401c035046280800e40317001041d41030103842d02c4024010040c000842d00b40100075140d000007404c040c240303c507030040c036030070303d40039a1103a005852924250200da185009010708400c951502072803149180d000007107070135407280c060f03075000b0040039040c6004408541d61f00324154000401150b40c4c1d55003030083c0c14031540c0803c170b024040c140044980720a4241428810f0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 253904478 1250 253903228 253903241
    0x7030218130f151a0f0904020a080f060303070305040312090b0a020705130605102109140f07061d03190b0f010e09060109020708070501050403090501020d0e0a0b1b031804 75
    0xa10344000d0031410849000004c0441200c06034a881280c2d894143c03a800302000e00611454603001031010803096a420740204003030b805420141c41d48845980d5030743c00c0540e244110600200040c00a00c02040011000c684540c0e40010601305186032680b5188020340c00d800890032000168051041081241486055140300a0b40400180300b007074107280100707001c2803828000340c00300030416902880a442c0034882406031403446d4802d001c0300c0c000d41000d281d00c0d5140d8094002901400b00d004d14803120008940741120100d85480c80c40c0b12810410b542d040401e040b4050f01030140540b400324095100d201080054410200b60382981080d203412054018160000c014209414080c05240307080042d609046501e184000350351003265250031443c60046580041c01c035801e06040c40f080580041060040d1402a4200c5a11000d2070004642c00214004a5908550b000c0028404070032160020b00e01c03000c042e0035050b07000131418507131031556100c0310845e44c2c0300c0c03440a94046a440e29000701d1 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 253905728 1250 253904478 253904501
    0x1020a05120310060e1005070f0c1409010509060901031707020603010e0f0903041a1308030d0e0c010c020108010e0612060709030615030302060711011d030d0501170607030218130f 79
    0x1018019100e17000301e8a519a1880c1c40c41c140440810043c080001d823a0340088015440306805000c0e039601c00c0c400003c203200c240d0a902c2502032000100301d500b41004140e2041c0d000501d204801d0b4a50303180e40c01b1414103049880e0700c4034420800c20340581c54140c0210300a196440d5080c0d4185401c81140d022404050000c0c41c40e80c000700000c000c586480101e0380d0030005030700d02941d80c400702d0b01850302e40c81ca4103034006a160302002c81d1410540809070b1041301031450810035900e0b00c8050600458041b000054000d0100704000010300c150b4010b0707019a07138800800740c0704000342c80d010121240741100480f8408009140f458060080085a0217816150924442c1c066000c5040d954081c0d202c000061008081000e0910044c2d001c81c0b00350058041c02c000e08000703c01c6c05582148940d203940c020104142910704140c0001013520740c40480001801003000a0a8552500c41f002c07030103580700c07074000c50840c44061540071896035440021a60300414000001e02c1c80c11081c80700007901c81c240304d031 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 253906978 1250 253905728 253905737
    0x105010501020724030b0406060f02010b061e16060615020f0d1719020d270c03080a0908070e06240406032406200304031a0601020a0512031006 63
    0x100300508131603203401c1000001d0541103c07480c1e00301c5800c60081066200083c1e1241c14440e0000f80e082d0406200104240c0300e600a1200c4000003061184a1040b0514034004081d40d94840c840e99500308041e2071a04c50079200c125000f245a225102500d10581003180406180150000d203260100500c20719241e07103034080c00b4500d603018009400e0348401035030600980312405c00510f040c01d40211406100302048021901c2d80c04424496004100120300904148140013241880c05030507100c4190180c6d1003410580003c0c103590300c3c0b1480c1d4000d80107180c24071206080104480c801032000700d02501e103188415050785011001c2080401c030030401c407004151520500010b076800601113a0984106080c0425054842d101151070030028241d0015207881c1c030400440c04070f030702c449901380104036280d003880c80c800e000300b40320788074411071000038000d120300f0000d080c3d000050601c3c0380d88024140182c039070516258548a050048003450821164000020090680010b0404d030707020b028180f40 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 253908228 1250 253906978 253906993
    0x270408040510031109100507020a1e0503030408030906130806161209021e032803110f0d12020732010c050301030813080a060605180403050313060615090305010501050102 75
    0x804c1d41d05126007555035000c2d84000c041c06004501032005c56150a03800760229403000d540e00142c043c5045801480050410008400030b05c501e400015142a20140030107903181507a10020001d95900810036060110001180000c0300101407103003c1c0318041c00c40c4803207185111403100030550681100325400c0f040c03034140181c000da2500302080c0c0c1c0d0304200040d4003452803581e0000900c0e04020000050344040741103c2c503010075240c0c01c0c61030440d44c80703070300d079070403c0c0440c04200e58441e0b01031642c22203a68041142c04e01c4003071050b4810680700c80c410f84c005240c0710558503901c540e40703820141c0c4ac005000140701040914001c90801a8014580b0000c02c08046100f40042280c881072202a280c4400403440031000c034214090000201452421a0b20b00392052030060302500f038502c10241b007108000c5600340340c10604a041841203904d070703441e076107999203c00c088403c0080080e4103507a019907401011905004440340c4204206440e111303407840e94518940582551816005541150000035 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 253909478 1250 253908228 253908251
    0x3030c1409040e01020c0307050c030706020601031a04020406030c0603021822050402060903070303080106111c11120328020702030a120c15020d18030e27040804051003 74
    0x152011a0000c803000b250700c141201e1101e005e80036202ca00102030000254031001c02c40d0000b00d0810403402170301503030100c17940d50702c06a803100d02c00d200c0075104420b04600a075824400c02d0a0307641c0700e8402000003c0075a00c0e80c980010f40b800a401100c0800c1c1c1c0041c22091107500950b00d60003880c0100c42509118030401c0e403507100c811080d500480866100c20218045690303210948964503c09004c5400b00c2d6903d0500406840c4280300b12804505140c0c84007061000200e80d140c0c030101d841c05546118a90750340119940c1d00070300c00d0946640510b00d440090110fa54000f14010701c8491804183d6142d50007946060316020300102d208544104501001602d002c224a640180c101c1a1107854000700081958194050b0350001c1000c0340c01300040a20007441e9015064030404420100031070103410f052031203c64010800580812181c24151446141c0300300d5072118080d1000703d202021001d00100e10b9402c0041d6822201d003440824144003d0809503a2103140703400f00c1c81c1c10300c080c08904 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 253910728 1250 253909478 253909517
    0xb0913020a09020714030703200607020a0f050f01110901030e1504020d08130806071106041502030c1324091a0703050c060411040c051c0f15080a03030c 67
    0x610070007030351a4000c00c050040c0305d020001100a004d6903010340755900314619005146818010406016110320000300c0c800c200000790491040b821600107000c100441e48400c11056040c0350120b030036200d25030100000500a0207100300c008001e90350342c0d031601c540c0c0001409072101880c2c004d54079032102c401a0b5064088000c4127401c40c0e0161100c8642c2c0c201810f1129091151421403001c012300e507000013640d600700081d071502c11181c5a0710498028034500045440e85019a008bc2440c0c1e002d400c8840003400355801103070409041459030f49000004404410080b0a030342c0301d400383c00d200345d0004c0008455141030728151442d5103001c00344603041c8184042000e800c4020202c00304408a04841018091401c031080c4100b52002ca401d80c0c501032500b820640917914a40340500d04000d000c41c5200e005909503207042001d9094220325103c5c808000004142100d4000049510360a5131b1050160074080305c006030161002901040040e070802805581d400d0104078104410350103c0600c0c0b5052 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 253911978 1250 253910728 253910749
    0xc060a021002030c0909070c1e020906040c052506060e0105060711030a0804090e0c0306090312040c0b030405060108010b01090b09090a090c0f0302030c1002030712140703030b091302 80
    0xc541d0043c1c8036200d8202d8007040d405030141c1603030041c00210900c02d40035001820320460b10303c00c86180b01101d01004200d007070046500c1c4d0081d00702c01e041d00440e070145031075003200d041d221881c50024180400803212818220703002d00c4c00904441171301780380d106114030ba00a003c040d0a401176981c2c4554548030101e5494880c209000d081c001c616010b99040f60341c18081a4981504918031075252a2201100402800c7c0700e008040e8911900890100e0f030704000c59505e1241888002450911030303403584019824400620444a6603200040852248034001c0650b00a0703021381c009045640c181282d250031a12026a0f45042c803803a0f00302000000c28841c2280d680404c103641c000100d8070b82000010140c400da034001401507010100c0031450b070001049a6003100e000701d0441d03e201e540e04c000d124402c05245801c40061300704108100c0800c184c104014252421842c210354050300480407460690089201200069126010403c0741d19245130555084410b803680103501d42c0c820341c0001c660452 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 253913228 1250 253911978 253912003
    0x10b03040615090e0f0a02010504060e040e010c020a1b05030a06091a04210815040504050a1505160f0c030e0102010906060b120c03010803070f210306080c060a02 71
    0x301000000d03005501d40203400320031000c0c0702c0d440d907501001500c0b020044400502c2000300041c008100003902d0f4842030b406071143c52074141489030071079111820000d140e4215071106c401803102d840902c2240744608403580500a404150b01d800c80e84d08604003200c070404002800c00f0b00440d40c2c0803038040f0782c8a500c031000040c00011450030003141211078855168500c1100100310500078504000200c90002d00f09901440120400c15103401c401a511100ba148102044004504182d0311694000d4007900455402d40785d91341d0b44030300e117011624490788507540f9507090095944141e032820030b035000e007800d1401408040400090504103124005003c21580118418259000390b00014056030010300520040e6280ca480343e070340d40e010201c2c5e11040032410700010510015402030f00d05031000355010f0b6142002c5915a174210b4450f000b01a9440340d0020100401e1100f0800701d9a10740c941600d01013130303603071400c21803070304208100141038018001009644034859011038101c0d0301e40b4 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 253914478 1250 253913228 253913249
    0x108150109090218040f0204060915050f040e030409020706181a06040e03040803040f06050313080711090115120b06120907030c0e1012030e0103090212061005011805030601 76
    0x10b840f400096084034031194010300c441c07114004c2c8000c3c443c900c44d0005009001752400d018880d90f941100c1c007196a140090462061480c1c024000c0c0d14110360031560a100080000c1449035960848500315480b44e881480d18550001d928010088503001e44d40e102018410003869000c500d8036202d0150500c009690142520306000a4580d9650390013981505454011652240c0d100c3c61480e5484c3d009009545d880c011122001491501c0790302240c0c400e04158098010030a41903071100140d03082800221a15540081e441001d503c0d40c40b5074a00030711a10307000b41413087d000c1e00301410482070801c40820740c030b052826a1302c00791528801c50304142c5101c004140c170ba64407042080e0a00f00e080c1c0000740320844051000402900041049000d042090142010b007030340c44a07021086124008000c0204804801d5002c00d58040d034400d109150002c0c00348c01da640600c41120741014011100d46000710036840082c001564132034071850b000300c090764505280720708110020340d485405100b140802d4 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 253915728 1250 253914478 253914491
    0x1104140f0a0e03040909060e0705060f0d02040801020a050a0f0206010b032a0f03040309060906020a141e030406090605032710090c061205040b0c0f0c0703080901080108150109 77
    0x6081d0350700500116407244152900d464541d2101000342403d09010354526080040e0080c1c0c608001c1048421990010102450980440b00d0941140c100c000407800f8203909020010710002e0a000800c061205940e030300d59203100d1030304060301d041700840044045502507001030120503604800c1b260061410f800c944092011003c1c00000701e4440090000f84110105080002516460103540a03034443c0c1c880c0d08049403070309000c84652440703109040040e4401030554020961900e8042400c651714000c2d10041c8c8040580c5500705500402c1042c941c1d400058200451980a42ca06007c0c01e500d291a902c1c1d030078003080701007080302058072022003011206080e043e8801e040003602101d10703521106000fa40024104072960b0b4080d4480d61010136032071140030181c504280702d0644140d40c015070380050354503107a00d02c1d0219001480071040600040240d0300d03600700200309000042d0b1084514540c0c03058070030001044818181c1c05003205900400c01503245a04a141c42419604100320000b1b44 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 253916978 1250 253915728 253915741
    0x50703230d09231905040b01080c033103020d0e0604080a0209060307030b0a050402030c010309120e0f06070b011a040303090b0a090902030a0b0909160b0903010f020a020a1104140f 79
    0xf01d00209501c3d520800c40d0300d88620590081c2032450031200120303820843c0c3c13042c03d40103464040007140c02048280701000014240c104000c00004411005500c20505400342400034501d280c406c0c030b0075070140c0e00c8104002c03000755021001100c0050240d803500e04085c03070084002e5442da0300d820000c0c811620b80e4000707103981e02c0c2000038800035500000322141901300101c00000401c400d4030268024020101c2d490a00d500a0003244101d030b0b84850f040401d00d1807050111018454a00c115600c52002c142001c0c1c25900c00014204035405002c3c01c0070254540880001c0750240e4690341a46400280403c002103500907114000300d5050140355a9144000c0e4021518150a60840f41c411840070050001c030a000d035200300420001905c151035a41c45e402200e650b82c01e40d1081724880c40c88042e42c00d1108140520140c5108100500041404080c004500c0c05a8202c00004801a0302c121016424460704028a030050041520100100a0030440c0a404100c000b4544540c15034020003007006c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 253918228 1250 253916978 253917029
    0x1401050708090409141b0109032009090f1b0d03140723010f06051509010509030f0c09010b03071d0d0209090105150301060e04030813050703230d09 65
    0x2d1014014804c10614945141c0114036405484411949204811100880c008602c1006250400585590300240d01d540c0e55040380000713074080000c0707518440c481805036856001c6031502942500000c2e00c80040050780007464802804a900c45440104000e001c294540280800031182c252904101e0381403800500703007241c4103445008000381601c3c004d16603a6500d101011714580c40141c000d002c0004810102c006854440c000ca65000300406d4102c600020140300400c03100a041c1001c90500041c080002c0c03c0c10b200c4280407060f50001448800d003803074204082405007546009190035410a001c00805c5840c004801c00c200d0110fa00080b01280c0d10301c044440040c4d070003000048546803140d016400b03442e0585003101110100381200403140307010301400c0103448031000756100f59680d64404803100c10b0054510141070501c0b4202c0b402080040c0b0040e406180106a105113606100100800012040c200f0000e00d030481002c11503800d510030658800c444595100b60b640d183c04183c0846c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 253919478 1250 253918228 253918237
    0x2060a0c0507080304150f021f020a0306120809010905060f0901030c050403210801050103090209190e0a0803070e0a030506040f02280f06030204060c0f0c0e0c07020306010f1401050708 81
    0xc1d43ca100109000580c0c2c0312a00c080c0c8564403065481c0000d1034000c000690343c4403000c0c02c991552240d40d64410f050300d19180c0c090301e0038140d24a0301207a07581d540c100349110344418441c243c403d00c81c0040c40d1492541c0001d0780c07000604042d120545855105000d48903207000da8200e0f20b040540714850540400d11440c1a03030055600300c02e9505104040e0180c0c0080f213510040c0103404550300360f00000e40d6601900c14500c9068010b46a1000f69071001800001020301c0350321410101d65518084107070a000f000540300951140003a0340d5030b810405000f4000e43d01040c1080d00c80c0041c40c01c14000110302081403900b15a001600112041d03552001600c1d400d4040103101c001c0603c2951071445c1c41300009003004a0701f103a04003541842d1070b603a00b1003da1281340514404215070494003400250020110302010b8080c040e154001c40c0c9400c411341500109491000d803254000c21340d40190720341440a1401010511000541d440ca1300402000c9000009409411700c0408518002440440404c56 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 253920728 1250 253919478 253919489
    0x915150c010209060c01050a240e190c020601290703111509070f0b04080606010f030603050303070302040518010612020c010204150804120f080a090201050702040501030c15050702060a0c0507 84
    0x1525608805d000c240200400c60300a02d41a0901e1514601405000c0c101400e11500ca81d81c004414180031030140b07041400303894104000155076802d01d4524091090000d8a615a8050161545004520350039880005079a070300c03d0442c000800186009003080300c00b0903a05d07003848032040c4030b5240b4031404c10b1a20300c0e030181a00700d110104954800b011135104162483c00c0f02152082e510b0b01000c2e941401a40551015a4003000200d5090740c011003440089514600c0c1c00b042d80c0c1e4883e076510b0701710307002521444040380d00801c080c40366251000c0400044a03034032551204540c1b40a90007440c0c40780b52500036003003c1e07002407010f240c0403007034049a010303068115201b06400c81704c0200810000c1d0858007511840c5c4102c0c500310039a07102d02202842002107588000300e81c7c4640300d00c0f4000380740c1400c0490500c0800c100f00001625180910b6000b10302072441707404010316242e09101d456103400e82c00010003908001c51801030360382d803003139952182092406159801217807920a00d82105074106 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 253921978 1250 253920728 253920739
    0x927050903040f0602010e1b0d050f0c01110309100509040905060f04030206090d08040b0a0e0607031d010e10050c2503030b1002060a050a0b041a0915150c010209 71
    0x10008100c10010081c001c0302d40103ca454099035036008101c2c00c039a0708803050001a04018161808483c46c418004000d640c0105072071150740d081d41d01c103883c08032181b60b03a0920f80c0246002208668118014404010055024606c0d1559400026038860006400d0b0801c2c4038020440500030740b9160700c0044803d0b03000003101c0b8a0f080c140c401460314881101d01701c0051064030b002810714200441d9180050307110303407629120354907696100744000034010151440c903543c80040d0740311000204800c2d07004030031a807000200e0309582c1d40f0491440c007080a0301074007a81440301d01803040c840000c0740340e448030001e80001000c1c0c0325030b582c00d02c0d240302d0444002c80030104640245c020f45c5040700981d9138540710b904d080001d2298031050029000084a0b9607000d60428030009941401c2c80d0000ba60018030542c0c005440390299000600325030080c6440c01103800c00c05c21107005d600b001d4814503049007020b544642000702d2180040d10300a0441100150650f01240d2400c402000b501515a0140c000300b0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 253923228 1250 253921978 253921981
    0x20708030a02010506090a020c0a0f051606080403020d08150607060209030d05041d0103021302160c06050d051b031614030112020f0a03050c0d0507080d0302040e0a020a092705 77
    0x1c001e001e00400e4500c1486442084046042002c0c0380c800c64819100400180400c1c2d24991207028441190100640c0c030703401341e50f01490b4180701d48000c45001c1e05807910741070003c1c207103400c000349414a13880d407080c240f120031824030051000a40c008bd1211008480450396440e00340f600c0400390093303002c020380600c190f2007085041c0b600b24025006548840f0396070550075075040d00c5582200401c1c80040d4111112040c0c00c6d25404591700100754030622400421a45103140d0340e01c104169035640410f00281022409004a00a6010b000c0c0c11001c440031403040f061682070b0701e000510003c0c1400c0482000c070f00002c3c0780715005100c40d8034046082440d4036241d680d90100e00040f90f588400480c0720f000404442e000030f2130303e01110010b40350400e00402e540113100382800030803401441c1c107946d01d220345d41c000a0400300801c102072182855580141e1200c0c41e050300070000c00320141204440c1c5006011711400c4a40c055400070490341e1060380703005031810891035040311094060101069506000 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 253924478 1250 253923228 253923247
    0xe0a05030a110f1c030c0e0d15110c070b09030a0510050103022b200a12050c0d0f2d06060e07090b040306020706020c06040b04110109050303031602070803 68
    0x2d0102500240e0002a01c8995091807610b580b950388018001d04108100c40c0c2ca401928820b90042c0021002c60800e42d080590450000e4200e12250108441c3d02c20f0b00c62443c0c03140c0c02240281d00c21100014140d505040c1c1070600c0760b0f1205064000d416603000041a4081c10399820003a58100c0e9030403109603001c4040d00741c0c1302c001a017400d000680c01125958042d40000001c0800384000b8800b100d0106450f00e20741e5501c00201560080820104c00000700450480e40e44212000080c150000d88418401070b5217401802c107070b04e4000c00c9100700e0020200c0004149030401c484200e50740032005110060b0248004240000142d4602c140400540039400c1000402c0e03119900303640120340a0031090f40c90400840300b19132107018102c1340c40b2040c0410000524140c0181502c3da11980c5d001d414500e500300b41524001c8116815106017803041c0c240700a201e4000140d02900c0009e18280700f20504003008a40e49100260401401c0d052140c1250030b114405d0110030081c010400c182da660b0780014 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 253925728 1250 253924478 253924487
    0x317090a1521050411011416020f1305180a080d050601031b0e01080a050709030f0c08191103060403080f25030c0305090303070e06130b1b0d080f06040e0a05030a 71
    0x1301c404450b114203040540c50f8030341c0035200c00c841c2c1c2e0b006000d5551626445c00c8228202441c071190490300310400d140c0c0c90f4202e03607070454001c42860151500241368070b0b0401c0800c8411300300c1e008036103044c1c2120808038040b030050400c49050304103240000c9000d444120040b0028135584019500e170038089083c0c00d01003540300c080c1103128182683e860748a0344880f48644221a420b42d56000400c07981001040051166100c55640c68003c4180a04550351100c65a05050380080c2c6200180340d00849041000000105c41c07030000720079402043c2616241e0380280c02c040011b03000e00c12800c40d10001a4420711039440074072900b6030380d821401540b0000d0030040c01030584900e450000ca424003001409040c0004242c0b0700c01c0342c491383c805902001550034030006a009580091954849940118200e1561001045440140884190034400c01c031034440c02c0202c1c03401e800e4104071781001400701e21400042c1c03a6800c44011100002c84001022070f1a01e04664010001d04901012414000442d0072 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 253926978 1250 253925728 253925731
    0x601051303061a040b0405090c10090807080102030601090f050306010302010e030f070b0901020d0305100b07080c01050702100608010207261e0909010b0708030a020a0309080c070317090a152105 85
    0x83e04e06000505180d410001550b80071201225243d10203100c011040c5801341a1070594841414442c60450b10350043c203040001d1070300711b40d040d603400206100065070312419500007001110300c0034030303524245070000351144018070003e41004500104140640c3d403e20600c501207050001700c1b25010f0744c4000900c40e68104c0c0304900c1c003501030b04039440c41c001d0080c003803103210b070301d0010300803124508001549000d500854410784010109000c200d00f503150903c1850300500058005098400b04480140142c400c5134001d0307400d82e40184002d20006e01210b00d0204c403400b81c1490045c000e0300c000200221030140f05003800103007003001d00041900c0e01003c01041d4840703085c0c130021800d0f03072101030410080c4a5020001d000c2642080014500d82d107a50260003019180d24000c43c061030152a1002a508100c0d00c0315403e070400f0ba4100b080100480340d000500c04010142424800014000341c11000103200d84600080c03a4540107007107501c1112500700e502c02194040010030380c90307141503004080 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 253928228 1250 253926978 253927031
    0x11040e041a010816050d030215090a0b101412010e010603030e120f030d05040c0315050a0b030f0a02090c070209091c020313090e0708030a02030c190b060105130306 72
    0x1600700010822100100d060303095500c070042000065443c00b024011501030400c0180d04500500b2038210710511102c0070640100562002000644842d041080d020700b030180c10000c112a075550700f0003544a100080e0308410408032407800003115400e000b94090184001c421801e546481c00220070150020100034081e48291440c0c0c1080c40700d45485a505d2a0440c040401d5610501003056103003082d030405a4030034071803080440969581e40e1100120070617001070844007a2200204007014600744101141c4c0c240440041840b015100581521048a5130020380646102e40c00a03e803010344004a40e1042d5000e48409a24030700a810180c5540381c0340c9044011007080c0341c0300b0f104d240c800410303603501080f101007031820b251614841500400000305506427034001c00000040140007400503010341c0045401455488002c8242e290811180c0d144400d503142c3c1c1c1e9520400030441440d651584502d081c00c0040e0b07503244c503c40c40e031080807a80d1300003000d641c1404000c1c01c500f040e050382d02d4103054 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 253929478 1250 253928228 253928273
    0x321090b0c1305040207260904051305060f01050a060c06060b0c0d020d020102091c0f0b0405071e0b030f070c05030403030c0b1510080703020702040203130c05031b0411040e04 77
    0x10b48070301c20001640709400024150701c400d22150740404d41c0034148039034050003002d07c06240c00702d0800402c095a204a8803946403520341000c40c000c2c0041400030692100d81000202071030760402000a40781e42181c0140003c01a8801c00310003000b10980c44000034102c0031590355102c1c18200c10091b662894146160014000ca480c034080e0716005001f6190780340340c01451000c5030030710207105080c42d2005100a642c0540ca01d8207040100341c105480380e00883c050405000441c1c00d1000900c204082d041c0d088040140c0302000300f115403c030600f80d90300481044c4030301d20341d92600542180c0b241c0c0010809040d6010024001003015000658525114404c0546801d65070b600301414407005240000c2a030820208a680c1440e184a00304990b4004a9403c005007480c843d5000300b03049070411901000384110b05603e00c1c05104681514030300078001100142001260b0424900c1c0800404100034021a01d5000400c03250112074262005400211380c501040d26040c200360b582045200c014400d8203 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 253930728 1250 253929478 253929517
    0x1202030403053406120207080421061b0210020313140f06180d0e0102010f090807170c03300403081008011506051e2b0204030321090b0c 60
    0x3c12070004220122850f940311040c00c00111107124000c0d501410f002c4500341ea0400c0045400200f1007403402900c190141528000b1240d8900002241c4d03800c055807510160b07803c1d0a44886a00050340e1010402c105409a142d0711060840e107840084880300030f1000710001e00d410b04030324000480c400090f809104489c0e494a50b03007110080944124680ca81c1c980080c5221070006028009407c070703100f018400064000140c1e4410001c603400f8040072590340000040381d0051024070b0540c800d128041c4c0c10311038604040f20506980c1c91085244d0340321140c00a5144084160040381038484000343c41510380840c0c0b5241c500208544c000319099005030b40109408a01404140b10320100c3c80402042d0b6901c10341068005c0d10580c01030051003046680d031450002d0100c2411015041004100c3c00a008a080c1c030300900c0b40d556a0801506c003250b10610003013001ca07500010400e120207524484500c007a04200c4181c01520b21140d0142c0307404404010701c6203030f603003090041c107500126130080e8407071 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 253931978 1250 253930728 253930813
    0xf080c0d080408071202070b1b0c060406080402091302031212090a0206030126010c02011b031515020f010903020f0c0405010b12190c0504050109050f0904120203040305 74
    0x1ca000c00c2d0303006031541100b403084c0d4000038080f5203a4102c5030301500480721041d5036200070700321580c40741c9007140110900c2c40d80c1c10101881040307103051300b80d401c44126041a080450080c2007500007403000c0e20a41103413020560221502c560708142a4001d03091703480c034042d10740344007549500c000b100c0d0008100c031000081c60100c000c1044511326500a245a1559180c210241f11801c40e01e02d0407030f0307001003014891142c408248030f8481b9080140d0004181030110708100c0f10441d4000000c1c80c1454103020316003213643d02d14044007054924803a516502d021007a02c08074070701002003504500541c607146901080c0343e000501c004407100c215089800512000040c40305943c000e2283d00c0001d001809110501d8083d14150355002c1e626908918540c1c0c480380c640c000307031201300c0380d4030011801c001002d0040b541d0000100c070150009a40c020702d140710078408682c50f0318009002400886c560940039428900c01c2c4200c0300110f07080b008444a644400084000c80c2d411300c1410700d000c2e00c658020421 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 253933228 1250 253931978 253931987
    0x150f030105070f050309070b031003060c0c050c1005070206120406050106030b0109050d0311030a05030a050a0605060909070e041e05070206090a03080601090f09051005030303090a080d0204030f080c0d 88
    0x4107a00e69070310b03514a5443e458040c0e40300d420290418405001d142c20102d220680c1201651150f40401c0a4085080c550700b0070500b20f9005101620400c280c1c910000049100010070101e146030954100002641340072040b0303440d0003000c10080d440880011105445650102c8990241e4002c00d006c0046980c1c800007542201c02c07000c0b840d408a800c80500b00980d10f042304060135030740d01030704080e00c100d5a84484a811070348078142d1100480c4021080c440380c28254480c4540c0040b041c1820402d80e420b0000040c603d0281003c0070344110721000001e22420710601d0301c40305902000d801844540c0c0c26000c035141d0314035212a40f140f030a2801001410480c800218140601840800b030300820840b030301d040340d00702c2000701301ca41030040401c80054111a1850b4520040c2001c0d0700004103414501611130010180d5440301d4400d50040c4107100d550440424502c42c0c01d030788040389680c0d030410582040003134003035940f0182c1203950307000084c000d00503428002c0003c1e4001e107040d503098501c0c5141c01c0c0d8 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 253934478 1250 253933228 253933231
    0xd0519061104151e090b03090f0a08040305060f0f15120706030f0f110306090c07020a032307030309171f1d07060e0607080909091608010b15070804080303150f030105 73
    0x10001020343d40100058030a03000219000302d5483e0544113081203101049e4903004c404107086507a5040003408106000d03081c0320640e0040e00c0b41080114030705007068100c91201b0064078186a9840000451b1020380e2003c001e548104481415514000c0d565003000d0000c140030320210301e446041542503070031080b40c2d10502ca1002030425a950450f2201018004c491000900101416608101e46005a52581031480c0258420540d00c1c00c19806005c0c40d1030b0180c00c481ca04000d583c440d850900000344c00088880548403060f92083c4805403100c0c00314900a075805204880036403000c0030040071303185504211101030314824581420f043c480e09031030391910140300d0b9000040c1c444181d5062803a2501c003d00b1203601815299041424400014002c1c900139034100710300758400c840301e44018604004640c02004010000c1040100e210049081c17149c843c001c0d00c0d007603c00040d07520304010040302541c020b080c40b00c0c2127239103d180c40325100848084c80510144280d415601024403450140900c5 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 253935728 1250 253934478 253934537
    0xa0507020120071101090b2701020a11040e0304090911010201061d1501030f05070309021504030b160504080d02060406060b0a1706060c010c050d0b0d051906110415 72
    0x26140c00000e4841d43e134950264008070b4108500346000160704440600a460b003030704a800803e02041c0380c03007880c2d01442d21085d00c041c1590408401b5001240f01c0c402414400f10701510302154410381d403d0303c00c0c2981300d9900003034022854140203005110a42c5107806014100381c00800515488070700c2c014420841ca00082d06846003840000c1e0851110ec840c640c02d207106040c08031740c42d0400301d80b00050b200f00f180e28800181d6220032a909520b0300500f80c02e14098001c080c1c038640707411500c0d9000d2804000f40800240180440c003440418440c0d030464000304400e80a841c4100000d840082d1600e20986041e90300c12309208000c00d60340303484e81c120340400302c464031895410500c00c0c0807510140d00041451b640880d041c000301031810700c02c2c01002d060741810354445a0b42d07826050a802124141c00c2943d000e5400394564000149002820030012000e0441d0701c048042e15140000242100308a080d07282d180129001030300b0700161000340c03454451911915820268400b07002c1800c440710407407 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 253936978 1250 253935728 253935791
    0x30c05120408031b010902181009060b270a0816080312070e040b040e0a03030e010b01020307150204051519080906070c0c03060c091a0405061207170a05070201 70
    0x559900900300f8240130440c100c42000032855030f4843c1c0003d0007a103003c4160400c106840010440b040b440c1d800007402810070750741c08005160810143ca422030103550b2815126100d002001050b081181101220000700201008816600c5501c01d5031502c1a81c08c01181c1800c01c141d0114031840f0101c2920109090000c0d108400d540342401201d8100e10858055081962001c140b10903440764007032210040004401400101140c1c0b40080c120707004214014520703490700205440681e0302108541c0b8050b040804c034034400041e6022103000703200315844164009000d16540645401000c0548600301440e00c800380d807880301d07240554401c14101d440b0615a000000020300c000e00492114540350700801c003000d081912030b6211030441d201c00d1038030800306010b410204081c104904030059401c140350550b50405160101240a9008404c3e9000e40c9800240001d0826403140c0001038a48450780c076044081d0606035040380042c035003680d00f40700550805210f011815010b1220014210540b503a = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 253938228 1250 253936978 253936987
    0x14012c0325051e19020f0414060a060c0203030703081f06090513140f070203040f080309030d14030601032703030b040c0e1503090f100b03150112150e010207030c0512040803 76
    0x71325144520002c039080741d00c0140b140d404002600d4501c00da100c0c2c40c445124603c3d950502d441000b08070086a40160108524800400c0c01610302200b030354600d50f4141483c14458440a040031485680040d18000d41500084002a034580c00000c0350704450080c2d403d02ca03020042c0170344100742c3d0a219890351120f14124007060100c6140f02e14981d0100e420300c10340b81055222590407c4660860b4448000341e8070200f41032000b40b80501080440c4032541c00c00c0c145400c04540d443d0203038003000302014185903440a05000501175002c6020103620107031603480c00f044032490090004d25442a032640a9441c00d10b06480c56401903568030a820340007006c4492101603441c81400c0da034801028402d19000b9403042040250302008042c0309019840c90200d0a822010306241c82e100c002c250406a080a041c010080c2c404074924000141c0e40183c181c10701e170b22214014002501101d10804110340c8001060022305500046032421213201d902510021000920780c0c192354043d900845416400410 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 253939478 1250 253938228 253938253
    0xc18150806120703030306050a0b0c0d0c02040603020402070f110411090d020a17100c0504050a03020f040902030d051809010e070f0e100c14012c0325051e 68
    0x200c9a901607401011a400b05445505942c01c02d00300d68411404a61542c03000d011502e01110880c018026031408181072280e000c209503681c110043d09603050111030500c400954556821003800365401030419540d403207403461300450141140800f80d8101e40d4160b041c42c100e01d01401810b1000d4000701207141016940f02c1001940c04000b44100d9220300702d02030002d041d4000300c03908056101c00d02c000d0301801551501d44000d9420410904042200402040c48281e64085102d4140ca0b01940e02d82c18540940011400a1282c900c0180d41803060b1040c05a045a01600804c10b000604c0320820b400b01c140d0303003800945e0100f07015009291032544000380c1d2a6114030400c458241d014a007130440c4908407404500c820300210015000620b006805d4814019200d5030111080c050b04005c01030070300303045c401111342030750b02c805541c11845090904460042c1002a074130f03e403450558082c00c1200701c01440000072100c4100325418001c56000306020300b01d80c0322683c0390030940700240c048400c200 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 253940728 1250 253939478 253939487
    0x16090e010b0f04180c12060510050a260a0c0903020d080c0a0602040b190f08160e060c01230c0922020304050c04150f0e06030f100c1815 60
    0x2080302210000140000a03c0190a13903400d070307600818400000d41012100001025041c0502210000710b01b010b00130411a142c607413903800703c1d02c51761410396154030704500e040712080c12003458400c0140c3e009010b494402e01602040b40203002084003046640c1090b907080e0740012441c44041c0d4868140c460040c040742c1128020008281c0751019a84501c84541d940e0049800a42208091182c082108070b2440800d030b20808a04003241000351054481c400020214030000b0104890008208200c1c035403140620000041a540244416243d46061084034000d0079000b41c5102c3d59001c40c400840d888401500b0316018a20344001c2d02d150542400c02d21007069402121945042c05011030051940b102e4805140200e1041c1d01425000041504020075186000000021201c0e6201c040180d008200e4440046480794103000c6040c0c5c0e18040043c0c1400310f25905454240034007020180358551542c403d8481e00080c1d1140c2c0041145403140c01d8a502c001c1c01481a0f015184071300c5044117019 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 253941978 1250 253940728 253940737
    0x21b1f0e060a0b0d0b010602070e0a060e04150f110c10110307030c050d090b0f06030d0c1103120301030309030b0c0301030f06051b04170609030304020906120a0203060c0316090e010b 80
    0x1400c0654a04d0b0315984414002800342c1c04075005810501f401d2200e8441180c0180e00900c2c0c190042c8016418019808500030740603100a042140ca4000f0b144003425680041916041c522000c11407030715040800c01e245d0703000281045c118003540340181c0048050b4818500c0000b54100341c04d0855540303038030540040c80c81e45030301418024207011034552500030b80240543d10f403107100000303114181440201c2d1011809800541321741c1101010449441d0f00c0b0f4642d154290300581445140140d16010a00b0710080312214641c840300040003009254000100c03900f00d030b2150002d818036542e1454150060f02007800005c210705000e40242c004907406801c0313650402c40d0407819400c011104610302410b603000d54061841c001c40300014508801052000b141d1000c05217000e10310754074081d4001415100024039552080001410200340240c04101d558500b0740d0142c02c907030841c01c2c0451441d40c01e4204886222020031400c602c5000c81d4411081c0400b110704010b04a40503908000c0d446805401 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 253943228 1250 253941978 253942001
    0x120a02101101020f04030201030b010e1c080712021501090905060609091c0f110601180509190305070b061801170307061a030705060f03040f0204021b1f0e060a 70
    0x10003102096409420f2005098403203498040681e1180f551001600340d6080040300743c18028038034011a0a503c84103d01ca008184c0b07038010740c541000616260201d40188070020f030601e090f6000000e030440d000a404091a0b040780b6041c03505030380c0c400540b4150345540308000c0443d08968003041c1d035030800030200c07508910316109594400d028010216060002884000c000030003414210510b190813040e031180991004020f00303250f40c100040300701403807170b41244404403555800000700011014090700c00c0b1003020007044001003049050051075a046180156522600c510100303015150940c40110f200301281584400740e031a00142450012030059014640c0c082009010f0015500b44074260ac00c8103401000e20103046480d0a1524210b040d400c124003c040c10004805410216020b8990042e801101129110b0a62000c14003a000311002c54600d0040003021103140b06000c21a46102584211041d56448400c80c000702601c2024959102c503800550204180c00d8035504035440400 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 253944478 1250 253943228 253943237
    0xb04230a08011404030807030b01140702010903020d080d06050409052505030706051905030402010c0b0a0207080711040c0201020a0903020f030708070b03010905060a0612090309170c0f120a0210 85
    0x156101560741c251928501d0607107982d2450f0707007004201500325190940126103440c0400040c001031f4000707405802281d02000c2034101c0441d980086a104544142c0516030150a03035148a03103600d4440e206410005801100c182045004a02c90030079106090449801000501212900c3c1c181e404d1a04503200d200e04003d2495100451b20751010801003004100755a03401342d669040d242c032842c03540c11886d0790f00d0403c18100248070150f0791021910b80c0d41341d0400c0e82c004054031800c410700000d2107030001c001c150700b002103442020301195100031000940c00b61420721603180ca82c58203e00702d03c6130740c030200041200e105003880542022244241c4940c00501103548058031050242d103031040940c01090350960001c0144004841402503541010003628581d400c142801005045104000c50b0480226525008201814824560780004210500c0401964004400803d48624080e0900c7c0d005085010301a80c0e05d041042d510001044410094820310700940d08100d0030050042c0c0000030403 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 253945728 1250 253944478 253944499
    0x61406030601030e1218040b0a260c0409060c020606032d0c041401050102190807080903010213030516210f03020a0506010816120b0f0c0f030903130b0423 68
    0x5c0002c50061807010350350043c1e9031909401d101000142e440c00381409019080c40c403410031003c40d41801802c10211813100c59642818a00001c51030410794052480d441428040100c0600c6060b612201149225a098841641d1a042815a912415151511700015001e2101c90f0710b000007120840b07100d0240e00340d414401d230420000c6d069038200b519181c418032021004001c01d40e01003004142401d004d10200c030100601d6100c003809405114000b408030040000c04010955080d0304076480034500103040d0100a4403810516075950060000300d181041980c0007241110141e0407466001d443c0700c40c5071500300360583d01c91529482007801202035111724204034001a9041c0700d140e02034001d03100103094034a48074a08040c0450320b603200320306403800308482d240400c082c200307100d50105007004500301582355004000d01c240310f480041056400302206200c140440400284000c040300d44003000990744506505080340b08070b225800382142c0c00c5c103010002201c0c841009800401c003d14660f03c4 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 253946978 1250 253945728 253945753
    0x50d02031509100b030a02070309080a0317060a050a0b180612071d01050304060c022a030c060901050d0c050405120f01050711150c0708040b04030501061406030601030e 74
    0x99800a0381c0c40303114180391003440000c80c142580c1d1564071200011812000c40c0c0b0f8031104684c1484080d2521000c50b80000321407041c5400f03201c41c0c00c0108615000c565100c0454140248003240602c0454440c0c444103001c1071030341c03600c9540d02055075802440c6600340344c540191150a035102000c0b038403038a40b203849507601c1950707044050f06204803000c8039000305144c0408020b0402c01c807104d0000c00c2c800903800740003869902000340c0c0c4e0301950006002900c640c141c8410b03840c10383c024081c100006c0e0005e640b4510143c5120050751144000c0e801c84540805c0e6004000c614020001001e0000e003040c024482034140304d4124640400711410f1462074940c840d408940300c030359403082201c095886202c400d01046000d1090b41d51051403850000f0030580003200700c0d529240089605c0082c0c9801401180742c0342c103901c00b16040540d022140f244ea440d6130301115491500075220a9600354070304403002a03600d19a40180e4990305008107030070700d59501c0d000150700500c007100909410f88581040da011 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 253948228 1250 253946978 253946981
    0x31906060b04031401050f0c0301030f15020a0e090108060601020312151903120315060302070303140103051e0318011b0212160b090d080703020a0519031706091501050d 74
    0x1940c001c0500e0104000ca0310300403420740e200903147c4000790780207004200c002c8001005503815070307500202080c02174016003002c240d072004145034042c45520010f40043d0607034212040c5484120182d420403926a81c600c556522183c08446603409a001040010324070b00c900700c449980200f0300076600b11501e964402141880100c03071519820304150300801d20a1048140062040d480586418091803184440391500c00520744a0002815001300360842014020740040004030b00c1444c01e41c6007580d6038142156a510185030401d455130b0854144c440144000c000c868444900105040c20201c1b058011208080102c3c0075035244c800c00c4043c50700503512620070601d00c100a80003042601804e2489905c503100c960b200032010710013000601c00f50780760929440d940c2030b0840445520340c94242001e9040c14080000100035014240010b240200355a2144410300e009549050002c4580d10640500201c262282075111070900c0004000001603c7d03450580041803400c00d051050f4030080c0c10 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 253949478 1250 253948228 253948237
    0x516050a03020a0b06043c1a0a050d050c1e09040302100510060e0f040908040602060114010309030816050f0d02190e0d03030b0f0a17010b01030506031906060b 70
    0x500680141d07205030140803a40d030146802c031780d080307a003000070003070049281070140c4900310b44100c201d00000c5801c41c84030558003502c10f640a4100309020036034001c07001340340819545404a100b00b05541c4082024280b5200810b10540d100d001400071464520400c00264a00100483c1c0051007c4003940030703440760b0310380da0700a903c6a0018180f22010320908019a20020310442c003114061b03c00f00901684505a0102d0550a0b00c804517618040700100340a0012013502501c03010380081d000400b09d500181c0d060490703840c0440c0000c0c0102caa40114191107a881d00580056444004503201c000c440050030110441820003500d040300d1900c400440b0303000007900d0180940e01080105410004441c401404071881c604012002400000034002082d0b070100070301051b41c2ca0145d200356450304100b1001d036900040684441c0750f600d044040e80040c81c1c0040703201c1340d42401950102c55001e4054070f40188801000341c00860410b280c1000801030030001601c00c16150f40001030301500310030051 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 253950728 1250 253949478 253949483
    0x2090a0302060a051317070311030a2a0509011d062b031106010602210f040e071e05030610030603020901030b010501080c04061b0212010f021b0a11010516050a 70
    0x150316100914400f50b1950055400900c5ca00100f400c00c01c4003030000b1a50314160f81d4040155164414440042841c1201d82e400061544020f60b9030b8400101000640c41070700300415070332141d06501da9003030110b141c200784103020044001e860040c568030541a00160b0003800501000b44a11200c1410842581e2100c4440c490382243c114907006e1603407110401c404010902c0052115525025009546a01c43d0030941c10f0000d8610405541403a68001c651045174030805454031641c950300c0c201c134500c1041e14030348045880c0c40c06441005001d0001d40030f40604a85502c0e08541e100c805200b01c150000c0780c0c91041584e41d041c0800181d41d5502d150340694081c80307e0064541c10a400905090005001010b00c00d400340b00800000c0d82c00f9904141448414498455600451000c20481c65140c00a50f00a500b4011b64006800d9254042c00c07024a020075040011a20340b00d1964a0b41052a80030785030365804011400154016002041680c2c12092a4400e008403038440c18100103901504 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 253951978 1250 253950728 253950737
    0x10c210207170c0c040905030702120a050d0806040c0c020907180e0a05092a06070201090905070c150e06271207061a090a050901020c12120703020306010503040602090a0302060a 78
    0x70408a06003041300140751103007502c04008070041c0d6280c5076075a00901e80b0081c828554040380160030f010500c4003901003a80502100c42400c4000c5014048510844469000318134003030481004c030b8450001c19900e160060030500090325071381411913104401c80d1140d00350030040700000852038000c0c0201d501c2020b00c1e003000101030a001d00d1103400d184d11315041003680c6403250080c1619492462108403810012a401662080c5606c01680c0c4042c0c9644020350691074082041482e54124a919403070600c41c01d80d2084405000640804580e6412100c034a06c0e030002c8009000050340d064010001c82e400d0640c4060f44d4034180c400751070200103200030340c4c02c01c5020810008000703d0780500c12504014090f080450354205000c1020240e00030f051404003620b44e0081101d012081d030403981c010412809560881400c00407036402d680c01041060203814600c0d00044000303119100766809142c0596a5910716116038542001a4100e00301075030b4030441900c1e001006030b45000003000c9284172510b0703 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 253953228 1250 253951978 253951987
    0xf040603020301031a011a03090a12020c01110313050418140703030e0301050106080c0a0e09280510290301060908100b03031903060b040308031602010c21020717 71
    0x2410444117950352009801c4014580040c0003e83e9000042c40c01040d092a1080e00ca85e00e42183c54500400746034058071386e20103800c50b015441d90100701c00e14108000c1e00c0b0340519200e0f4854003540d0703100b03440c1c04106d4040b500c4000e10040c901900a1203000e8050390203c441c036105c5403600c12003054048400403440e03201105c10010550040503068130f03010110001c120a40c506440074229040061071015040c1000510088480c000c13000d01280c02c0c1d002d850520617150084c3c898030481c0d040c0b200724004020750700c000070040340c65024940c807944d5070740da01c4c03101da92414007034130b1214400d050390035070000a03480c81541401120001c1d60080c0100e50b03644646919011545091524030800050a1410011740c040c081d24000110f82c03400e4400c007256000070710030381421402003842d80c0029811900001d80001841102c01c05140100307038203020074a101ea83c03c6c1040e400c90305048042d00c08980240700050144020320340389048803240000146c0b800e86c403541c0704c4500d82c3c4004550b044240b80880c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 253954478 1250 253953228 253953233
    0x10f05070524090f0727060f06030b04060302031b21061b07020d08090a080a0501090203010e06010e0406051005060304050109030e030111190309020d0b07020d0e06070303050c0f04060302030103 85
    0xc405070030110820213003040e1401c00041d43e4036032101340500e11562400c03500403215400740f000e400e054840400002c02c9005d8807001c0c8100b201189100d50000a4242103071750203145802d00c03542c401c403a1300400504600f40c0d1920301c91800e88400c00941e91102025050885201e08040360b0f035641c0d91114003501d03880c03a000540046507404014810540c45061103c0001a1980c801d854001500180d505845040340e50014007142207603085408c103401f4801e1510704006054006040240c4210024081030410500a9540d15824400e00f0090360301100883c0110320207a000a800103124010342d080c054544000c00c1c1c01d80d0042d102140c1c9690342d1005e540c1410b1740508400e401c80700440083c40f042404031250a0f03a4011980c07682204024010402511402980814650b9a0181c484021100c060610030001c0740220f5034000540511443c04001038461441e03800600c4001b01a00d04200030780d24120300603c802005c050f2000001c100b42101465460040c00090004d50f40250b40e039070552 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 253955728 1250 253954478 253954543
    0xf18012601081c08060103090c1d100e0709030b07020705090c0a020d0905030c010518031f0f02031e130506010b04171212040602130f151706010f050705 67
    0x748845036502c00c80303200701c1c41c0300342e214264581200d02407070085511152800d182700002800d60010701801150798541c02805800c0d04140d00c203140c08036800c0c0c0301990f26004560003120403210480000c001010a10009041c0176040da0042d4051040354a010346a0700400c1c414002510300354070003240810b8a580c0c0d40e5041022400d59405490101c40c0589031402180d681c502202c102d905200b07002c50202c510b1802041c0718056503100800321400341c0340c08240720b05d501c00e10160601d41c0c14240706005141078094003c503401150842881c070701c00ea9101c0c45602d50044083e01c02001b102c0c000c0c0035007010030800c0141902910165600355501c03440c2c002071644000300510b000445411210788051800710610641d0f07811514200b2045140d60b031481d250000344214240c040f42020120300c0032034602c0014406606071140340480d101c40c800d0000b0b064586070b41076610144a90002e100240c2d05502c1110101c000d0340e118100581022480d9940d203081c071490a0b12540b0541c003640e012010044031 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 253956834 1106 253955728 253955743
    0xd03030f0f02040f14090a0e0a0b0906060112180201050a1e020304031203140619050904080a02120304082b0e01050108010f020f1801260108 62
    0x1001440c0d00941040c064034915040701c42010401c40814040910482c00041080e800387c0d640030075400142c00026000d15160080c0f413008000a480740d881103000d00d080601400c014503240000601850b5200755201c045406e01c4907050303100c0c1818103200d82c0c41b0707020318040d40e88080c0003c3c01c3d130790703a149000d036180c0c0d0310a810030424105030f0200107401520720585000c3e52000c2d03070442c2141034844890805032141d0030240072414524145140040d03080f8802d8603081b61558034400201c51403411102955a50700c0007415045869040c052001e1000e50760355003500f5400e1584410300d4502804d4001c0d040c00444092600b860460501d500b020500c0840f000e04c102c0c21212100760290000788102c4400e9804c1881003c200c405a00039107014081081c415428840c2204100c522500c4036040789050000c038070810242d0035801e03000d62136185060740b40c2085651610741c0c01413400c8203 = true := by decide +kernel

theorem cover : BRFrame.Cov 253776978 253956834 := by
  have h0 := BRFrame.cov_init 253776978
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253776978 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253776978 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253776978 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253776978 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253776978 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253776978 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253776978 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253776978 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253776978 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253776978 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253776978 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253776978 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253776978 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253776978 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253776978 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253776978 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253776978 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253776978 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253776978 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253776978 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253776978 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253776978 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253776978 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253776978 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253776978 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253776978 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253776978 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253776978 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253776978 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253776978 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253776978 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253776978 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253776978 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253776978 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253776978 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253776978 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253776978 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253776978 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253776978 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253776978 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253776978 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253776978 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253776978 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253776978 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253776978 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253776978 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253776978 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253776978 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253776978 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253776978 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253776978 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253776978 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253776978 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253776978 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253776978 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253776978 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253776978 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253776978 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253776978 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253776978 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253776978 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253776978 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253776978 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253776978 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253776978 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253776978 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253776978 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253776978 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253776978 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253776978 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253776978 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253776978 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253776978 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253776978 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253776978 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253776978 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253776978 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253776978 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253776978 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253776978 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253776978 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253776978 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253776978 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253776978 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253776978 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253776978 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253776978 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253776978 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253776978 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253776978 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253776978 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253776978 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253776978 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253776978 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253776978 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253776978 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253776978 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253776978 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253776978 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253776978 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253776978 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253776978 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253776978 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253776978 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253776978 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253776978 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253776978 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253776978 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253776978 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253776978 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253776978 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253776978 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253776978 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253776978 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253776978 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253776978 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253776978 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253776978 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253776978 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253776978 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253776978 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253776978 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253776978 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253776978 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253776978 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253776978 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253776978 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253776978 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253776978 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253776978 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253776978 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253776978 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253776978 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253776978 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253776978 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253776978 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253776978 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253776978 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253776978 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253776978 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253776978 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253776978 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253776978 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253776978 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 253776978 ≤ n) (h2 : n < 253956834) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
