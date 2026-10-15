-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5483
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T16:00:31.878532+00:00
-- url     : https://prove2.me/submissions/c52134be-ce80-4766-be32-d72d3342d531

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 985971223 ≤ n < 986151079 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 985972473 1250 985971223 985971229
    0x21b060403110c040911010c0f170a03050117070b090a03050f030436090201030e03030f0103060b0103060b0d0c02070f03050f0120191b0506060301060504180f111806 73
    0xc80019004580c01c01a5110961b1281c02410020b9103503810b00001d50306c50014410040009445164032442032031000104981070003080c0c103c03d0010001903d400004524950962144200c05160070010001035181941010441e40f01003201e642000c410040000012000c0004c1c0c10320010101c00303183c4803410200440c24a2101ca0003190032105178554500144c10715800e14080143c08900c081a105c04900068001e04400384011440380f10000402071100b8018104a050300e04c19002440046640c8004400fa5101e6000340d030002c11040003134594400d850351024070322480c18010388404580d100c0244c600010300e41d10a0760540c01c0403160400040081c812a07046062224a00045492122504a440c02030605926580d120808200c05060044400341544641002010101e4816140607a1201003c3e2101800f0350300709100415285000c0c014400c000480348205542e41003180c85405410441d01c82c241c404005074000b41042c0d842d03914100c0824482c142c0701000609214080c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 985973723 1250 985972473 985972483
    0x1a0405060429010228020325050d020d17030907060932040c090504181110090312030509061b03150f0d0c18051603021b06040311 57
    0x3440d1050385441c07454030b0002c00903201da00345855002081081003441800507454088203c0121251510000902010220400705901c80900c240c00740e0360000d600341e03107841c2d6000c80e481c41c1d000c20198040051140b42032124074a41c1140c0010000b41a40401c0d803201d04584403100c2a8030030302e0b0300000822003e40d00401800c00180607926140400c01e20b030445d0f84010440c0c1c01c03645039200d41155042361381c8003401d50007409100070040c0100042c441b4280c0c050016000c45c0b20300343c00f550a050751010b5103002c1d1070382d01101e65044030301c50350020001c40800c40c0741c041010402d0244a01400040007082c4c25a0907201c0c40c0321585c0f400034043c00d24900d141e1038241c0003408034003e0b150201014426010400960780c02540507050603070081501c0c80083d010075a150780c0c5a400540aa200c14280a0707412000800c03134a4a0710404640c00c001d4803c4c109644048425250700d00380746160210740ca100f50300170b00016001c81900403c02c0ca040c0121414102e0990707081c0e0004503c80507600e421502401 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 985974973 1250 985973723 985973731
    0x1d060708011508071b0204060b030a0e0c0d02060c0f032a0f0d050903010902120307030306050922030c210906390f05061f03020603040605191a0405 65
    0x18030b0041000b00788014080c482c002e00030400c0101150000300111840300d035003140554020001d1028a8039040403c020781c10403104000040d040514207149002d010800ca500c0c5500a03080346c7c00c0342e400360284000d40d401103440d04500c2c40340b6014a0018031302403024000c20b01060318040a1082000c8800886580110299080d900948400040500700080d01d01d01d9611304e04260703446000c0c0c9030003c0e00410440e40003940009010201c0303144210040001c05030b0f5803103900c0c10008640c44900b8891f11070ba04a50500650030302d182c2070104074245142648507144a8a000041140c50340e4488064130142d155991002c502c10fa000c01c40305410000e440007400a624102203178540c45245c256641000584d503240e140a880650407102d40f070b0a459039256a00038080c1c1780304103103619000e41e44110444944100c6440e04801c2008480010400070490f41c00600080c1140c4807034540314000c02001c0e0080f0302002c4c2002c840086d0841c60301502c100007124901d1050300020312002e0109030b0310010 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 985976223 1250 985974973 985974989
    0x5010b06090120030c03210a06050904080304050102041206021c0c120e0307080c0f0f060c0a0f122405060909131a0a0c110f1c031d06070801 62
    0x2000c10515640e00c11192002054149049110329410f500503a045104650f02d001c01c6000c000b400f807d1304601140107091034241e10b10a040c140d61040f24078400c0f00c4030790043c90350000462012402007088500a1504075006000041ca069a2840c090041e0038082200b11842034011035400130010403107031030780002030a2031001d0085034007000000f441c650401c005c10107469a54281200c101c0b8003001920304840e4000101c13035496040c4041d0076038a84d255001e0346031904c1440501040c0c8c0c040403542a020f00d000792921820140841015030383c0070008041c150030052000344c80d003888141402541212200c202d00c00c1d5142c05618440c1059a10582095009207420001c05455880300781a0760786c0100c415a100c8142011803030580c000c03c00480307402c003152400e2020300407041d1040d4001d0142c0c19040d1100c0e402940c510700c5140c0c40311109581e000142c0c22007052001c40b031154540301c0700300340c8451800080c005a908010b0003841c80041005000364810410003800903041461980501075031 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 985977473 1250 985976223 985976227
    0x1b07050316030e2d01270909170901170702010e101b2102070201020703080d05150f09060f0a05060706050106030e0304140d03030f090605060f0a050a3c0305010b06 72
    0x20151300c40649000b0a1150401001a988501c0c98612401d40ca295805900c451482c55079074440340c20141c8002003050303849841c0c40c1c40c0540c01e114076034212a908941a1103a9040c1c2d40507004141e0300a40003000d05003035540340c0100044000061158682c7c920312110700007007580b4400010b1518460f6401850180300340320300e0251a49550500c14420440301075000360ba52016480103c0c06d100e1940d000034182000403903210000300050b001284a980100440c3c030340c51400c8000c001013403144003400d0b900302c07084030b0102d078003814640c10349040200301602c0005182c0d520004288983c1c031000054800f1390740c9000510a07558180126000d11001c00001d60a05042000b60281001040006803180400402040400d80070360080c07049034034800c500308803010079401c2a0010b00300481c1c40e00c0c0310340c58000302d0035810301d455040c0e4000c0d0303000a80070341031003410907803102c2040075940352020340c24034003585070140e640e002000c080c1d101c01c60f5107142c40301e03510714903040d03003901c04a8000500c10101 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 985978723 1250 985977473 985977529
    0x2406041103040b041e060c08070c030c0b060f060d02180609060a0e0301150e0a0522020603041a04051e12030619030501020a02010c080109051b07050316030e 69
    0x40d060a0360740103038000b1240e80752620f903440c102922080c840520312076403519555040501006520620301c10550b0b80710608a13640c3c01104a0700302c408e40304003c0c08112400c800c85d011070080b40307550b80c0c8030f44040c01c02510f56404000003080d51300421a1146020b40024042d0f12001000021f20003404040d106141400c00802c0012071301d002d414080e0042254184070190355607003d40040d489075003040614042c09441e580040c1c400c29040b1482c410080c1400c001c54000c00c0c0d1200f00306003440c10000d40741249001035007042030550020340160780302c490340420481024040700110703014901c144000c0401150f031602081005010b0b03403032070003281c101c00c00028082c110401103070b900c6031003110901d0050184454902c0204040c1e003024055610100d0301e0105550150b02413280803115441d00d03544e0780c0e60340ba548400d581040300d413000005465220181080d24800180c01ea00c2c3c851001d50b4100f03d0240a075092600100600740e000a030000e5a6641e02d08110034100008140046003518400d0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 985979973 1250 985978723 985978751
    0xe1b03071715100b0d05071d030706180f0815010801020703020a060c1205040b01090e0a080f1c0e0114070c03021b0409140a0507051801050f0d05240604 67
    0x5046200d82d41d03038040c41c0340010b40d900400103984001e08401e4400548805540c04824014842103c08101280400c484070a180c4607a84640201d0700d00103006001c5141800d0084a800700522494090100e11940120300f480403a503441028004190081108052045100300d4505040c1d02c015907a034810401c801c0131030341c00308170204210380004010039000c41e080401c540140e1100c2940383d050340f402081c00100190642001d040303c18041043c050300c4405107102e5100c2c08815001844503404011401c1d004610030042d000c070341c0614161016601c0c0f0a0402401d9840e88092410305941d01d00c140d004640500041c15000940e038a4002c1d45182c0a07030340070356502600c0c2d41d418180740031054480d80550303072904007901e02e50744031808019601c00c4000b81980d5424040c812906800b520002007414101002c0001e0396203c0032180000a9280100784003000c1c0541001c01d030049203401c03220012030f008102410080030030411155859280041035101014054000d52180b4104002400713541 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 985981223 1250 985979973 985979983
    0x708120d240504050c04091409160e0109050604021303081246020a0206060a0603050c030c070515040503030406060e070c02041d060720010c05160201030e1b030717 72
    0x1001503400141310344842080300307124040e07503200006160400401e01d0103220307800340c2070f400303080040100d8454a1240703040600f44002d0b4090103a040d48440c00400422125401494004601400051030041c200144c038030354928503041550144000614200b000e805038500d030303078400ca08078540810180d090b00980401c00041c68200c074444441c00510349103420300c10300c444007400102030031959001400c0020b03459242c2107032072034413940c1c41c01c3d400a000c50007801280e00c00c100c001c88061841d9035550700d40e030640d0010003090b5008d100300e10b5050388005404503598040c600540c019912483c291a15100f0742d100e58110004c08003489092142aa80141450307240700d80c11100861902410344507180c07003042d8100c00c4a00b500c10b8030140200b00d608121510240d40031030149696001818400609035940007442900141d81006034031124002030304001d020610501d00415844e481e021414604560740c1e80c41c00701c1207020241868103150401c110002041585403100e214500f07003a6007900c130 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 985982473 1250 985981223 985981229
    0x305060d1103070504180203060603010c02190f0b0123100203030705070819080403080709050d110321131410111e06040308010801050f0c0c0708120d24 67
    0x1903407070340303040596014000c100c060b01001d031080141800910482d080101d0083e01640240108008111641418024000c820030260014585004411020040c00c51084c0080c0c072820700703842c080f0300000c01a00d120f40c02008400e03070b4800025003040c200c5400703201e410f0302c4910401d11149000c00c081d1300801500c1d444403640c00d01a0310313840c0c00d06000d0854820310003480c2c10341048a0300011419000300d05103024900940e20180c1070303610140c041d104001580947d40d0301942410b44040041c1d1000401d4003941030107400e0700d48129509002451035845c2c8070240034134030b00108101651030f5500d10524018101c0702e002c0901e9904c14404968035013044c440582c100058810618170340c08042080070808040c61181c0281015070340801074441c80147ca0403000103450344000a00c0010501840c1d000711440e11000545072140d81541d5003c0e07000ba01d08100900800c1c05c0044c000509200c45201302284e0f02c412035551103281000d400b02d0384503084030a4400b0f06c0320120340801c07038164412015 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 985983723 1250 985982473 985982483
    0x5070309030803100b070b040308011a0702040207080919030203121315090b040305030706050c04050102100515120304050907030c0203030109020f070b13050d03064b030b06010305060d 81
    0x580c0d211003c00c1c00031210617411000440c400040c086040040000006101d14000d0341d8848e0700b80d8070f4040500c43c640b036411582c3c025140c28055071002d841e02e40d00078500e0794800c0028030710786510400858500c42522880308010400c1540070020340c1400d2100d00d6146d03015204207031400762640100da1100c00280108a03143d6038040001d07549500032600d40e8041c2008824180d100c0b680c1e0b20f0459542d52000004885150511011036113007000d102c00d88080d2a016000b9110814202030442c0080600400e9488a207001c0703095608540c076a900b8003a9006105c1000d150303510704000501011010182022042619001004860a070b02200b0b0300d0550350384900150343c80613103924806540c0140c20002d40002d0382e50007030110b0090040140e50b442c80c440c10a403001da00c080307035044d811101300d48134100c5030504694221600648000320f0079114041050041d034480c881c02601b800003025800c2d480075290b000311092050010042000d540300b00701346000c1c8624175103c030105485020200300102 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 985984973 1250 985983723 985983727
    0x31413020f030105100e04230d030b0d03050a08041b18110406021203041502161110080a0e0304090509150f04030c021210090602041a030103020901261f0507050703090308 75
    0xb0801260000d023a15008002d02d010030902442c1190b4490b240c81d1000b8000c245003240c910520304192025004640d01626803038200620340a040c0c82800d8028003c5500c1002016954541940303c01080083d00703a2035202091589004100c100f291042460741d029034000348010001075070f0024095400c203441100d515180d456a180c4914203a000c620080f0509001080c00e600b10304018660a10b4103010b00b40300c0000031400c406011011901c08211000a0100c0e0300080c4240b103107030810340340880840100c0c1d00d8141d89051980444205540201d4140c005404400e101c1841140396500440c02c402d140b0030b10300302560040e200f40f149680081c017500000c424a80070142c00d2000600c05080107105011b24141803506500940c4035006a9880a15680300700340084201000d5a042c4c981c007418000030b0383d0030110003041c080c2c44824061040011201010001380c0244100c01442c407030f81d24201c0c01038000440e90410b580740103010301d007002010300503000400e80c415202021250050b54a40e = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 985986223 1250 985984973 985984981
    0x30b0d1214030f270c0120190201030b030f0a06092a091d0606040911130213060825141b060108030a02070e07031413020f030105100e 59
    0x1a07540308890701d0710705042501000f04221003141580c560b20030880280c0b0200d98004110510000911094003100141d005c09050305181d4040c40705420440386220000e4443c00019050340d1600400c0340c0800114082d4607121011540c041c0541c0502000c01c4000d8402c14044462403a9030f442203000c007801154031040200240720180011045020400c0e0420104520043ca0a100c0ca2000c0c410020b4442c81c241c440f99400611a80c1d0850401c01080a4a0103032034400421000c1e000c100019900b842ca01c0400304030741c0d6034550441c05000e0001102603100d82c50445020284c41e460740c0510184580c080030010114601d2030010b5405840014405076a44414412900054444c1c0c520079041800900307082ca0300891400d0750081d006040803119503a03210f4010944038068122030801580c060001403003100100340034550310508505e40018410300d0100c060b006a4810b0342c0e00e1440c014480800b8041d418200b02c1c4407aa13a105400a00c10703410320141d56001403169100d007a02070882e8401103 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 985987473 1250 985986223 985986227
    0x1d0607030f0b151209011802010e0a0902030910060909110d1106030901021b070311060c010e070b1b060705160201050d0f050609090705010503070324080f0c01030b0d12 74
    0x8060200c8041d2030743c1c80402d001c05401960340c0c045003801e04202e0341e10002401d0200140034003000114140400100c034013951b40117440b140000c207442e40d40020400c0020400c0082032000d14403c0d02100d004029400703000c00210304a4415403c2482407908011150340030410302c8203106a00e03001a034918484e100181000b050a104061030194040c1d0000240b01407030074150080c1000c40380c1058060611062401556070ba03a40c94400144146807a070010402450244060308040120384004100700051085d214101100d41d005010900c030049503030502100c0e10998801018a45e400504071030920b120040c0c86402064284c05c1c8580d5400703800400c40e40b00e10262030003c00f18000501c400422a040700c0083e040490340c0ca8012058040002c0d0a4100043e121040303c3c01a101c0501d2360704e61076012000307030042c81240c00485090b40a0352100d800641c0d116001000002c02400f131030b441c4c40741058105500181401e04140c00c0c10725201151b034880c4480c40034254080c1c41001100903d003c1 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 985988723 1250 985987473 985987481
    0x3030e10050c0a0303150f0f090b1c0308040312020c0c0f011b11030622020f1c03030621020f13090f080a02070603050702030a0e120f010b041d0607030f 67
    0x10101043c0610100c540401da050340000d100941c40c10460200582c40da42c0e880c0032412248554500c2c844410750400c42595103500142e0740303080282a069107240c04000d200c808000001045000422007000c000c10305600c0b80901e00c0340b940700e400070f40c50a01106111070b0b50701e0305c0051480c0f0a004041e00c90181d44c1c0103104001060010340c2482c01e218034541008a00c0e010104841e500038025040000c40782001003a5010008000340540c00402c401502441102800e800140303400440b21031488180e0140c0c400305001c0e5900c240d82c00305205007080309403080418031741000040449110320000041e83c0da0b807002c000701c1c1000c3d82e550305540303288003002028244501004d80300c41c030550415404d0100610051140ca034440c1c08881800340d48940403012201c0c12106240140c00500c02d11581c00e2090a414210550083c2240c02000780d0450841c1060b11200da103404070380d0f48058084060920340200c00700c42c095070b5200221300441c2403005460f4000286546d0415540350402d600c80310b16940 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 985989973 1250 985988723 985988737
    0x9060f04092a110735010908120423100b12031209160b0d0b010212040323060a0b1203090619030603081605160311060a020c04050703140106050403030e1005 69
    0x11017150100b540e62070098010621150614096a07400d0802400b03013414060b003004158000a010324101c1410301001d00d10b0800340c0300b1200c60450380c04940800c0c0c2003080d0078000407480c902408800094404523001c035510050010701880300c44408001941002c01500c05410340f010302c6010966500084500b400034000c2c11a1010111507004650b241512003d03000c030b50440304003003145000150041e03940e80300341e42d0344a036007036010401400007074200e6214113803804880c5000d0100304c0c4c4c0448298100202201e10007480f40d0354002a1003207141000518086890f1074014624107512000031400c1485002c2d25004403440302c040d800c25441c03190348040000e503000404181ca07102c1003160000c03103240d00b64090710f4620074506072022101202010100700c82d88103c014038900c101c14144103058100d40301e09030641c020708038001b85c40e440f0f038018644140195940000c244007000090110420181c100b4070402c601844140000380d001503101c43c1c4614210f030140d03c42940010120350900c10301b0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 985991223 1250 985989973 985989989
    0x6040207030314180706030b0a050d0f020306430f0c0525050102010c0909051306021602030708062a0403021002070602010507020f030304021509060f04092a1107 71
    0x40d00b040f41303052901d003a20404141c003405a610035991340100310291105c440c0e10035804002c41400f00290f141880003401c456100386110b5542c901c1c2a000282001000c440c2e0310710f410032882003110755008118010340805c03111100c40054050351070040505403120000c02c004d00a02403004070b0814083d407000340c00076600608036901103409406407200520318150000300f4840e01e0101041960060140d0b07000030509640300b1400340c2ca807414800c06040c005d8807120315650b94030b09410100b80d20380002c002e801900c5245031000c401920506190a0746076100d080603801240038080720411024100071a0f846079150395550140822000c4100e02c030360360000b54031101414100d50916000f1030510115001d0b9002080217a45981d01030361113619500f415802d030341040000070010703d80740340c5200601e8181c0420034100420b400c04942c3c16400210740c0c100c3c801d00420300700440e03501c0303018400c1911032000d01001c1c4040001182c8161032100388a820901c8214003e50f0b01c9003d0402012000782114 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 985992473 1250 985991223 985991261
    0xb0d0f06150512060a030b0712020f040305162c0405100e0d080c1306051b0d090e060a0e01120f0b0109060608011e1a120c12060301050708060402070303 67
    0xd201e01400b55070220162070890310b000b4000846610f004828207089030b800c840c0c0c0e03005595901c40100e442100325040e030400d81e5402d018019200c10707444080e00107140f1400050842101000440302d8071500350b48440c070126800c4130303180c5200006940b17140d42d0070102c98202c00300380c072140703002400d00305040105600d05140aa89020440d40041c10041c1c000709920b81c0f51090b115401e14012a1160366028980452680402c1100c0b6102e00018400c50401d88095005010030b4510981806104503203480040c64100d41882080c6004060580180c0308035811141c50345485800c0c480000305100302426001034840c80c0c0300b03005000c941c0c80382d4503a10480d032151170341e1141d03030000c01007040380241800250403034004502c075041005006c000740d0090650804507807400d28034610824180480e01d5074510103001c000010007504140ca4022a0501c1541e510f40c5007640c142c5140510041c0b60710303c241c0c1020103011104c0d804c00100ca40041045e0b9026030345000906054000c1c20005081007408660 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 985993723 1250 985992473 985992509
    0x70f0204020d02030f06042903121303030908010e0a110310051812130e1f03122601060f1403010e1e0f06010e0409060f090302070f0b0d0f06 62
    0x200343d00451188600b810030741e11a4482c40f007880211024280341c840070141d01b00807160302004041c501400040000d080320441c094442450b00c07907412079060340403510b2440034240101341e00722245601a20341c240081000c0080784010326600c2e81206e101030301c49d41000c038014009803010b201d1030130142c03001d22050000e410b0144503500b0a4441e40402c0c01035024100d0603252580d00002124580e03101c0300802c5402c1414500030882d400c1c0c001d49180440c04a2407003c101d0b44410120140045026100710354a400248001511600304500f54141007503041070609845101c050070745056654a00e050400e0702c020440554440c501d01403002e038048408400041c241392400c00c0944120031407100c1c2850580c5081201030003000075100002c0360745101c0000f481c40d500c40c41c01c6905001c1c0003070000c07030600b4070f40d107882c400c8500442c9140394190710761500b14203040c0c04000c1c04008000b400703044205031f03140103008503050098420398032115031101142d98102c90b0b5508048080c042051032510031021f = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 985994973 1250 985993723 985993747
    0x1e0109050c040b190206060118050603060111060f0402030705090105091512010f02091806101110020414122e090506070c0c08010516110f0d090f08030915070f020402 73
    0x130401d1403401407203140300003085540720b140c04d210003a180d0a03400c00c0850811080000c242c000409041c100f0903c2d03000111480d000304025070282400300c8508000d42014014113041401c03e4009038010448140100255100c0c200116442028800745a1441407288000350b4103150324180c1c24095820044420400d41c1564010030209104440312501140804040b404010b011240c49a0190740d03806046192030080c1591100d85c8081000e0329000410038012034126045034020748060380c8906a02c851074107206220100c0d109000c00141403803440c84510380c281840c0c03840705c04078012800d141c500d101d904540003204865840011b83d010381c506200020080c034a040c02c1a05c080c002d0160010f00c1c2c90b81071083c24003488542d185401c0703c82aa41065548080400c1420124440e0b5081001070b4003040c0041c0882d858695904160686424494031140b0b0f5183c000301c507942c00402940b80b9503642c0d58500141d010940036121703220501800c240303120342c02a06019420900000b50075070424 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 985996223 1250 985994973 985995007
    0x603051c030b090403090b0f04050619032a1103070b0c0c061513020a0e1207090e0724021c021e031303150923061e0109050c040b 57
    0x190180d90200b00a0581d9020082d80d80d030292406804158401424040c01507404020116104400ca070300c1e10301559a00855240c1c2c1c030542d41031800e96280c0c1c0e008498581e01d4068164612010190007003007860000080d000320020a2400043c0210010404024030090090700d4985800241d440c819280c480c800d4192a800381c282b0711028040d80c400100c43c0800d1290940c01d030000a0407440b04081802c011900039404540c880c001d0150301d003a01404daa42e103020302c92012714200c0141c100c0c64030b44202801900c1d80c1c954800c029800c090781c1071181c1c5140e50031141418590010091111071110801d909000a80c001040000e0364500031084668000500d4001010715880600008803070350302c02c039124040c094404181da400380d8020004030b0b80c0229003492641c0000000520b019413a95003162080b60340205808910b02d1010f0100540820300901c1d82c0150318010b1300000c0070714002070a0034008140039410300d0b140d540e03012961001041d130580c2c001c1c05290000664138940050865000 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 985997473 1250 985996223 985996273
    0x6010905010e0106020d080c070212010603170f09040c03271104050403020c040e03040503010e070317030c07080a0302070b0103081b0f030403060f0b06070c0e060103050c0306010f03060305 83
    0x21400c0a000141e902000c4852604a6241d50b02901d001c19692208039031003c400781c10b08200c00c0d028081c078005a40c5e90a4018903004403103000084980c03031031603c48521811105582c500300003c0c04580b003d01c05010071a610341c0c200711400103409002d6841900100096149504900d40d180c040000d0031004950550302280070300d0900391380e003604030100000c0e40c408440007001a0841c21a40700c190626804c41902007a81030160390401d5224400700c0d00316983d400a440659100d40b10420500201c1d84290610070b543c0081c00e440c515181000c2841441841070003880450006045130816100c1ea060307581444c0d103c1c480648c03659403410f0924a5801000300c0c0b103c041c450240f55038400f0b0000a0642140e41440040e60402c6d00d9a00c0b00030040411011400c01c9684420f40c0a0b555511035000b400703024401e01ba103400c41e030704104012450060082a40741414544000e00c542482d4010940741d0113442460548081110881c1c02c070050011544024280e1180188076440210002c4c402044 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 985998723 1250 985997473 985997489
    0x2030c16080325050d0e120f090a090605060307050d0608030301030606030506070f0206190f02040602071502030906070f141b040e1f0221010b040f330c0b04050601 72
    0x20031500304030100d40803414403c8003800314000f080040001d44d115040b810342d82401400b0b4a809120042961003070760b0014074203040c4150300281006240c64102524005400f83c9481007241c01d013840041041ea00c809403c402c244000440d204074020000d030880e0010300070803c2030740d80b00e5a49190900242c1064042150140907120009604034030174000811415010b60048c101c5444106d103608854442055424010751076401559190b4598001840103144543c02070440034580f4401d8614034248074101d00031904200700b1442d01c1d688201c10f0b145110703044140b10128440324940010321410f030310801c188034007070343c4225502d00c65801864455031506840034081804101d0304580c4071101c5d8001040a0f40014610381c440c080a0303400391071a4200d15806240c030500c1c4d00c00390340042c0d03000d90001041c00c030009401e00c41c20030f42c100410010038600c5c039201d008401c0d00b404000c08034149107040203600350050b05030464074480c0c0003602031030382c110400f8883c1e0304041c2480c42c3c65403824040d07410 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 985999973 1250 985998723 985998751
    0xc08070f060314070806060903070e060108010503030307091a0904050f071e0801120515010b0403020102070e0c090d02240403060e060403050f090d170c010b15090402030c160803 78
    0x407094081c1c003400d4050198030303140c00071642d1502c6042e1262a0b010745182e42003802800f070b5a656442c00c10001c0c000c0d080035204950240b800c04001085410140c001c140250018400e110361180c1184000040e11960b24110310130500e40c8100d16200d015440581d54001d0503c810f02140088209c100e038020344081da1b88403a015400c00401c00000d4143ca420000104a0801040361340c201c0c02d007256000e80305800ba1480c80885d525602c2296200381c00103070894a002400300210f680404c0200000d1001d140e01d0b0703078646000c10440b070b020301a100e001406102e40c28011000c40da44c40310b204800c416510400342207501090080304850700701e0701040703d4240c50315040d88042c0b000041c1152059604d56110351801050202403809a00f15249483d00078012404682c0020850002c400404102c0441c1070b4407485010782d11401e50301c007400b0031405000d40700034a0302664070210889040c0101500e004d0ba5030b03184c10408401c20f204489008168510210601b420040640019809050707000c1c82d1031 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 986001223 1250 985999973 985999979
    0x3040320040603061b090f0902030c040305070303080f07020c180414030c160b0301080c06070c0302041103070e0906010f18090c02070501122304030c12020309040e0f07090203060a030c08070f 84
    0x181c6d20f0381c11402440703920603091004020b03841060f0011030b0f0101480b980c0c5810203699554041c581803c9800031404110600108040c089002c401c00d1f80c1320070301d07100400d04030600b0360103e003e4164034060240440380301d00c0020180441038125015001780f039411280e460385a505042e80715490000c144c01945000070000600c14140026281030b00e250b81c020f465090840000c020450303000842c2200c12092141c4000050707944c1d449062045010506502c0d034134904200010700c50510342490380d100700210b60034400740384d0f4002094ad8055110341402c070218030152500e00080c0c0c645902c0701d170140d802c005099000e06e902242e21002c9903801e88034003090502c1070201b1003d0340c56480c4903a41c00010651904421400b40782520f8202d07000c3c0c2000d100c0700c1d4854540d125548850711500e8050303800064102001d040612500002c0c940e040040c002407034101c02d10342c3d01c41081c3d2040e90710480c2c010000c2030f03441d40c5070400c1303500031071307004840f540b18070380e00d0201a03110304840c4a08820464044400 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 986002473 1250 986001223 986001227
    0x1106250215061219081b030a0215130f050a020a170d1206150c020306010605120f040c1d0a0606090311010f030b0a0b1b0f03040320040603061b 63
    0x59544101640c03101d00c0d8540d00d03041800035201ca90200b100b101d02c2005864008001c0c102c0b20003809900811203070381d8901214007220b8002c007a00e4182c1c0e203150f00800195a030198045010300d4004840c40c80915282c6170410700d00e442003109800544602003010f03500b420090005140d51000b44241d40884000d603a07176482002d068041c002c3c2c482142c0001c1e2405910500c14004200b1100140d800040c00c217403280048280341c804420500d000c02c0b12552150150b01d800c1004500611113460028500a1204e0902e40003010190000300c51044502c040340c04c22000006200207000c01e181d083c1d5020040c40d02c1e9620310102a500780c83ca89141840106100c0d02c100a20801c8c1d0760050102c12008802070b004484c01c504041800d4105641c403800c0382a2556400384041c01415000e99036134960250f912500f601c0d0391544800d0080368008254000702200200544049030f410100618000f42a0b07030007c13100e00e502c0e0540c25440703864094040304001d0140c2c450001030500300c0b0b002a1007500e1041c1 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 986003723 1250 986002473 986002483
    0x301020d020d110322031e021b0301020f09121507050712020a02013f02070605090601030309150c05100621211b1103100501030c0b0a11062502 63
    0x40c078500c5c1c401c1e41010040c1c0380200308028080c0c803900d4144501141060403103c3d00c518044028010b13040f1450101c05c85038800e0031f1046126048008501c0e01100445041581c469184094011440503c00e8000c241e81401800395243c0341c41d14040b510300e000b140050003944a080100c40040103d08050724403440000e00c07190682d81078403041c004200f011205410ba84003101484c40f01e2054031a010b980c0c0c130300d41110320021540034002580340c2119140c00d03419514000c144080c680c0c410001040465403201c2c20380c04460b50420078611003107a030f150403140000e2000019081344124541c200c0300030102d60040d821242d180300004481c02071518840010f0301080b40107003080704400a80c088035080380150018071425801c0203c4038155a1010006e5444502e40c02e9070011908808442242014024000218614a07082007290b0545d600c4420301c4415019a650880020a0300070090f8020721fa04400c00442c1001c0343d90300d00e03201c282c0c00d01d680301410007410100c8152703042703111881c00010 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 986004973 1250 986003723 986003731
    0x60504060b0924060912150703110f0d09030203040803161406070e0906012a030813050a08490b030a060c2003030105090c0c0c010e0f0301020d020d1103 67
    0xa459203100c0c00b03c1d02004516040024000e51042c146d00310022008005c00440118002c50b109500840c68070300405001c948205417090101c0c1c0c0d0400001064032a4402101c4400402c039100050250850404900d140141c1e040048540700015184030400d0b0340320500c08811384600c0007a01ca440d0410049515504152a0100400c40d0700a01c01542d140038000305901c49810300d003e901440c40501385004564901503007031034200d4101001d006050b8800011350388803410020791003039070300295115540c0d0701865a0113801c1800207d42040c10000180d0303000540720b1005541190040c41c071075103c5003411300c0d1040f070324100003403283e0b5110b1074100d008113248000002c026005280050301c030140504034124844042105d242c401140081ea0b41480c07080c6440848025920f81d0704040138003805c0d0901500518142d402805038042c0050b00264064402c00d084c43d0040059810101140030702c5c804d0030550394035500100b10144414900d41c00380c076021384101014040c800480c00400c0d072900c0140d0f = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 986006223 1250 986004973 986005021
    0x3060510111005180109060203041a0405192f012c060903010608030a08100819060b01121d01050c030f0c181801171621060504060b09 59
    0xa03520b25030201c2503500c003d40c071040f603c1c038014103006803010356400c44050020445005601000780300520100a4540c020048111480c00103410640c880f181e4541219940d0302448040200100400003e07128603000c512a111501c101301c0c3c800744282803062070082103180043c00c4644690b02c400c4120005c02d098043c400c03412240391141c7c1c01804502d510a45c181a0550740391680010148002c100074214040b9550b1a8101410120002140b00c1d065511046203544009000c4a00051560402c00800d0740a0740001c1c46003030314001179800c40380103120040d50624008403e0056080c1c581c0c41200540500004c03c650f50b1078140c444060f00050b00c5d034011385a41200005d548400081c014003100c0c003440c10040b100c0c041c9100080ea00da60b08501000d01d40e41ca440100415403501000c4040e140000004c0c10151100c03c42c1d580344c034201d034800c900e401c0c214a110749220511b07800a01818039000a4144550302d800c1c02d055014040f88100180200344820004040075821140c002c800142c00c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 986007473 1250 986006223 986006233
    0x733060f140303040e041415060117071701091508010908180105070615030201030e3d060b09090709060c06020304031b050a021903111309120306051011 67
    0xc0110500c92103030900c140d82c0c251008000c041506400701a09920681c410a903905107100010702d05410700c4c501c3c1c86d251000202d814140301041c0e0300f000099400a541a1045003180c3e51094102c820707c1a000d2221a4a0309000c000f045456854100005000190214140c441d44e035511083c222a4040c1e805070041c50103000007508242e070320700c440752441c00516065043c0b60361600c0c0c02044955a040120b00c14074189010811560540144122151b600000d080005825500054600c0d40c003140d40103105044822500200c0803000940c002d400802401c10400388c5070b0101e104103604c40b28a0710310410542c000102e4040c41040001c060300e85941c0e80c03414206459590340c020b504060011018003001c8100407000780a1082181f010794003d2005003030801e2640141704003400142d0244005c07840c807076030500c089045d998100c0f000442c1607076074440707542141132000001c1142c0c2c90010401300620b81450501e90303040e0000d0041e00d030200c0c0d414100340c0c00d9001c16113594001d01721250713441e044 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 986008723 1250 986007473 986007479
    0x414160503150a0b03120c0d1d0904230a05160510080a0204091817031e150406030c0608100e192406090b0f070b04080733060f 56
    0xb10b0241d075400c00c900c140d002c40c10198101c0001d09113044403000c00340803174010651103450b12080154104007074003810009844803891518608035100c4400950144880d24041010040503014001600906c0e86d644042c0c6404100d9640e03d4098071031041d1958407401a00c8000c1d89810341418084940080000c0d2031603005040603150307240020840c14402d9802e1000140742c426601404107401c00741440040e16041501e0320140d44081e850b06010300c46020300401804d0205c40000c0d00e41d00d9404070070f6040a0780e07800a002e180768403000c0c44030382250801074008100300320080e00405030390701901c481c115681d90500c00da180c0303100391088020f11f00840d004a4540c422800c03c0894030745005001143d0b0030b03001d6003250710ba400c19005480104001400410800d81d02c102640060500c1c024903900c1c10b0784110110000380100c2c00301510b15130000011404100c1c41c041150119940a0b00f6441c15050f145501c940c0d01c520705074444541c90070035040c010381422622444050300c03084211010101c0c1 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 986009973 1250 986008723 986008753
    0xc080403080702071206061d010f0b0c0c0a08070e090a030c0303090812012301050c0a0b130606060302072010050a030905070f1406070803130602040b030414160503 72
    0x500a8a0b69003903006481000c651030310300072020907609006d503401040c86483d1040c03180507070306054100c00210034030b90018000a03440c84c102104464011311880c2d15101188116402d103280b00580304e901039116000042c800002289e00e204079016410804030b2569144c24864445a2524006001030001441400024043e80c400608a40203080c52030501c40c151050710a01d000070f130031401206e010821080800011040721903000d203003e03e4030a00b010020550790340d070b5402c3c10b01c0040a855445002035004100200091811600b140b0103000c0c5a94a0b0344c003600030b40c4152001e8031140c80c103040202c1094000740d2501c0c1b100a000d00038803406551000102e5560f000003031580308068070f03082c624012560400906001d0039010b1103040c42070749001103690302c40001d1060a400380109200503000328040c070083da0b0380240002101d0070424014038006000348107940060365001004014070060140b280f1078203604106070f404a8031840104200500f407150203124069041d44190141c02c403100c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 986011223 1250 986009973 986009987
    0xf15150f170a020903031602030f2e1512050714063a0b09060102060f07030209060d021603081008100906020d0606051332030a061a040501090c080403 66
    0xb641c40320006003070075014400a1708650002001090346450202d5541c1985400d004042d52105100010046203004200359801000310b40c06030041e00040c1e07070440c4919410f07500481c40403c03228588508058071220240784169a00c1000c0d04d580c0300d007000105134a00215403400c20540002d1809040005013090141c110a0b4031384210102d54005040d00c0c41c011107080d0f1907014800700100070411051100600a0342e190003800c85046501a0b0b05100d144101213080c41c0d006489443c000d131355080d07030070040750326441004500e14180d03100048180384203131080da14140242c8070b43d4030035100d900c1e9445400f480446d40e001c0c1c2c2010780c1003c0078011445600e80c0c0600b034064801c41015041c01d81c00c0c07000c0406c492a90f07100401007480046c050b15a40c40c3d050858001c0c103540c0340c0b1f201001c031010500f0030340c880d000034000030364040058000115940030803041142c1e95001d20240310641c0c4100341c0d101e401c5504696180560b0800d400801d01d81d54500401400c40d40c3c0d952040e00d96943e03600d0486440c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 986012473 1250 986011223 986011231
    0x80309010b090921030f060d050a0503040e071101140c0d0905010c1e020d140a022a1201060e04030e0a0801060b070c05180c0c010f15150f17 62
    0x96680340c41211058941d031022502c11043d0310003400d0b0307800c8030002d01e0308981d160120310412120b08008101500040501d4145c101000f5200c0240f01e02003131904910f0400d8501002d09144404100020305c24000900d42d8805c0f4580c1d50745a54100384aa80c881c2a11003d8440303030700202000d000078400400e41409044680c015080c00718142c0519241d0034210380d0960031b22070000f0100495203103984540018040c06405a1004000721801800018918a2194035a243e91040080d0960102c6d2003000703009409980721054500d180001805050128140207403030707009420307000744c804094078180304810442c2c64140d070300c503519915554125200d0080e2020103a1150040202140c0c840c0c09201c0d41b4043c05038200c40c66510a46410402c01001e20795000500c1144240c2c0c1ea4461740c070300c1001a50300001040c460756181c2c034545400d1405040340c5400b046405240403c42490341c8021001380703040b03404041c0c003900030122041c81102c1d18000d041c441d80104011020780403c0b4119200070541c0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 986013723 1250 986012473 986012491
    0x6190f0203071514061f1d040e0601060801080102040303141b06240d020102030706050a180506041b0b0307110115090212091b04021b0d0503041b05010c0803 69
    0x15060490b40c440c0d038400d4002c0318018078544e541004650607480c803441180c006030308440b02045403800c0d80c20f020301821620101c004200266009803400b00d15140c80002004000740240140b2203500c1e00295500f8003449140000b80031903000044005041c422601500d4040e5141c076174a8020808204103680802d41209078a204080c40d030f800c8640074000140520300c0300301144c00451110710136070015802202d00d02e20072a00441d0641c0141c0c4c002080340c4005074070000124040c0e540c480700c00b00800400580035502c1d140621844200000421090311032449000000180f0800c05660b6a03441d001c1d0240d080341040410109a401c0c1c044c0d0359020000079100004215100300c2e0000b6003030007001e0340c010603c02d03401150300c00520a47c0e58030558050031703450052800082c01c1c1c4080039a610309100950080e5030000b41c211301d1400f0107040c0144049190304491798880d151000078201d41c812201611401c0000c500a060368140d01900d00440307005a5640410340c020352549107051740040e00302d880f = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 986014973 1250 986013723 986013727
    0xc1303020d0f0228090204060801060f111c030f020301031e080c03190e040b10030213050913290402131404080d060504092109170303070e06190f0203 66
    0x8016900c0c484e401040e041091007000c0c0036003002c0241d51400c603203a042000841e0040c001400000e40c00000039046444a1801c59a0380c001c825094a201f241d4269a0000e8040c0d8040010b030b10610b0702858082152a03036003085480150b1020384102e010038040280408043c000d040c41092211000154a6005055051920802d01d100c145540d0240003404c18981d043c002c10f040ea550000500203180d8001d0f1800d0040308810400074a0101165071400d052680c04144450703441c042c101c4650107000080c040c001a401d00c900c0019030080000c0303040f201c0500f115001c0422680b000a0251300902280e8042500e49841d400c00000101c11140780a00b15652400360400f11102c041c1070340994010f00d105541c0f082e083e2801000c1d02c040d500700780e00560501508400242c02081410b40a80351054a00c056600c03c0d0000c031412200c81d8058500f80078424110f10000e0004002507000b08a1529030200300303601001400480d0041846010081c2001c09044a00c5800313800c0900281c078041c170680c1c1c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 986016223 1250 986014973 986015003
    0x110d050912040e0402150a020c1c0c0f0e01120302070b1b01090308040b070306231801060918060602030a2007180606110a0f030302130803030f0c1303020d 68
    0x3600164050681841a4410b204c250b060200481080400e0702c14100d01d80418580065590140234800300c3c052040e0905002004100d40c44405469030312180100b84140d48480d104d010010f20300500ca400c2d02e80c6000003804e1244840580743d02e69060300a00b900520308000020f41e0b8001449000310409082400c00300c03c0020722502c49c0082c406d1301c03407052030305042c00c00821202d0000d02c0c850904d86051307000c0c496009881c2030703181e00d90b1415501020358101100400d414042d0610031043c1902c409001080b20398014003038000b600d440d407100450b070300000500e0809031101c034420702015800410030401d0440c400c0080c0d905550320340030b0305040c164054030140c1c60519903521417082191071440480b110030050003400c0003401203140c40d01d5142d030b15100319034464120300b5004000ca035440c0c90030020140071b601520010300b10081624416a0794140c41516640115851040303842c980c0b0004014a4400b4184c1e100c0b41c0311007228803996421a0700b4011109117500041d103070346040711088 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 986017473 1250 986016223 986016253
    0x4052509060b09130c17071b0503070302010e0d02070311060d050f0405120406050906090d020604152c1e030105040602070308090619180822060908030a03020901031b050306030d03110d0509 83
    0x54114144184025551b5042f94203001382180e261000c0c20300d09070001c484001c820340d40001c0d01425170313410618808440ca034040015001d84074905141072420304020030800c207444865101d0348914040c8081e200340f25280040f100d1140300e24001c040210303070309010145040c10040e001d0700141c0c1c0003400320110300c0c04940000301c0036041988108000c0704121085440543c2c080d04000c01224688107041020040c540380700c0030400c02401d018002d46980c1c142000f10030450744252981d00b4042c00130403160501e42890b2020b580b01820071f0f00403500c0c03200824180301002689500c1108072038030150090644c4034014020300201e10b030a442080500c51018007041c031503001000c0031050301581011504000f403c00b101082203600000510940c1c100400c00c802c0080121442c6c0d075400e1400603528044100184c0003008060f142c40101c0c0c442641404940390000c2c0114001c02048003200c050301421041101960710480e4100c02e82ea07400d10143d088080181c01480c0c0000d071010a440a80801c4019 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 986018723 1250 986017473 986017517
    0x3020721020a0f061a030109080901260c0423010801060e0a0504020f0c0106060207080c210607020a03031b051603030209090a060e0105040504052509060b09130c1707 73
    0x1c2544c0c1d2039942d08a01c1000407259500d2002c0c002c00768001d00081c2296202c412590181101d81e5062080342d14402d000311070215841d4928050110f05900c090408601c50300c1150824050075200356210306400309000d03031480580004040c1603541d281640e0a0290442c0c562554441071500916100804100b0381d80b1360010301140c24000402c030b51108581866142524925844001950403d000078421044003060000308403a00b51407941c0d02030708141d5150340d142018100d0809501540051160700b43c0d011903400c6240f4000d5406000c3c0011107502220b412944049a03804194101b05da030340703c0b10201c00c0200e00700303029080050078101c6100103c0c10284046688003d00380d0f40d040306000828030b80c1d2015000d45419074003008a45060390307030aa03075840c0b41c490318000704000d0b42032080050070381444440980300f80ca80900900740d56001c0c01c00c06402c0040c0a030710030802c039031401d091038055104800039024156100e07044000742c0c0c0345500c1a40c2000d4000b90805c02c0703880c0089020316403511 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 986019973 1250 986018723 986018753
    0x302040f0b0919030308040305220605030402030c0a1805180f030a020120030c090a150c051c140d021303110117090309060d1d1c03020721020a 63
    0x30101d0b5201c00050810452042203c00c07180d5100d4002401e0010a920803480380d885a414149903986405002c00d00c3c1500401441e460035104540c9004110b880c2d0007006140030318401d90440701211444810082c0400c0c250080c61501d2450540300c4403030300b10301c2d0009604290420400d2104184041c9424100322240d4040c0300c20ba03000154545e492982445040e00d2400e500d905024103400081c2e90b50854070000d002c40c0c881d80030100e090b134030070759451440710001d11640562800c51074001c0c401034450420504283c03954061540c055a400104c000410b403443c400b40c0d1f90502130401c20110403450b400010002c0c1c880f42d0700b4071074013001000d40d8580e0340145003c1c0c40170001901001000603c00c004c0300358003190f6100040f0a0003803104001040d100b8000b000c54005456081501000d00100015400e1085400510310a881d010307801103a0302000c211203410f86800603005140540c240c0c0700b6a00e0080800300d001178441c890f1940c813128260700348242d2040c1c81c0480100e8481187d071000d502 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 986021223 1250 986019973 986019989
    0xf030803040b09060c0a050a03020c0d0801090b0909100c0c08070b250c0204020a120f06091b09150e040903030b1c050307110402070c0f05010e0414160302040f 70
    0x140814071151002c2298030020040003010380d898a1010411030780070300200348052040c04a014140c050203901521111082c030812a00e1a07001c10784001e00d814020721588a409240a60714200340c10301e5184541705030302440c0201914400400e28800400c210085142084030074099000041d00c0b01000342901402241d1080d15810441c1d141064004090504510341503919003000c005a044a0420780c1d490301140c0060302c2c3d202410050340e070201c41c504500c04103807a01e003907506011003a6020006545601e40201b020b10400f94142c4064504000510003041d00c0c042c04101c03100990303011205006003032a141e034a0549810216080d2410200b044010a0729948598241e0804030350140c24660102c841c1380303004e0102d0701c41c6078a9104a50018121903100c040c409011b854a8048170102544070f107220780c1c8a5580c018074910707480180182c40c00034075014802146840c007806011a00e0300c413410207500e99150381d54015061160301c014a018540c00707020005802c0c4480c031900004000da9 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 986022473 1250 986021223 986021227
    0x10080402010f030603121d060c010204030b090102030c07120201110a0f031104120618020612010f050919020705010b03060a14010e0702062d0a060509180d050a03060f0308 75
    0x25100241203061a00c00050405181482c10808034103103400c07080042c0381e1b505050040d9240101514102a80c0300e0125803ca0780024081c180c401c1d05600520480e030003100c1d81011501c0d9508514203078841695444c0f000700040c441c01d40400c002c4400726007205568000021440c0070400b20064640000c007030540419011f10101603c40c1c0c00d406a0550a46140c84252615081004620401000c520b024044a545001001218501c507009411943e002801c40351180314068102d00160707002d015401034040a010000390710700b008451103006104c101c292400c0c3c40c41400d108030080d000084290342541d21441d000c1c01c00e84003844282c0c0901c4511101044004540310342172014441a031001c5504a810420403a0a560214010340c000b50141e01500c00b5030008030170207022419050745c00306030030100000d014200e1159800303401200c0c004e4030301c0000340d611754192491001041403502440d070418070300b41010910401c0109644011400c002489540303030800c4402c007401940085882c3c0c940 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 986023723 1250 986022473 986022481
    0x40e0c0702030c01030c02060c1b030301030b010f1509061115040605151210050421050409050a020702010f0e012a030813170901030204080f1c0905010e1e1008 70
    0x20722043d03c19400a00f001d00c00844d40060007950703480300601d121088000802c3e26182d10465040c0c05a03141000c5084944035612824580c04441007031103500d1940e0210a40003c2c1400c910303e20700395041c00ea8031542ca20b5890844c0035507420f0351603d141130003802100400340403520064082c900aa00070306000a1a281c03140c420b143d050700c050659803145032000304094140000082010480750b940300e000c9280e0b01c0743c0c5400d44504800da03202e80100c003405500c2000495004c0e01920885060500034840c988030003005038202c0c424820045e000a42c11700301c42c00303068002c003e0300c000c3c5a4103151038142101614040d2181d00601407030440c80038030010f008030505a01030340035900041ca002010810482586d242c0400c041030f034400040404002c902c0a855a001c0c0c2d055500a0001d8420ba80608400070303211a1203150800c15400e6100070f1544002c01c0314031860f5001c05881d81230311901d04492200f406c0110b42007812031498100080d85866041c84c0d00e40704498000c070480e035203c503203503424 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 986024973 1250 986023723 986023729
    0x6030213331407080f0f03190c080408070b060a05060d1b170112060b0402031e1b090402030606040b07200d080d09050c1002070611060601020601030314040e0c0702 72
    0x40710407204100030031400300380310854a05044499480c0e105005540e10001c1103a594600d00500c08070000d441004410405081200480341000c00580502003040c4422a0000c1d500c4190903200505036075024005007002420701d2442c00e4026100a0886545643e80c01c0040c40c2c070381c050810054810381311032041d2880e4000b0f0400801e8420181059074100401c060b00d148071507030521408407641a035440c90000d100c405d5114002c0b4006c003801c10344d641c3c60b0070444000269039a100104251440038002818145c4000c001c9e0b2000e030500140307071b180038072000801010350406031056034000410040028540b100308014120684580b0412441040b0107070401d20305480004118000d52a03c00322000040c007400032540a42e100711400a8000c0c041d080482c0340007001071090307410401c103807a900c83c00c070340001ea00011110f0039503c040080c440691070341e4589000750398042c01343e44090010f01c0000e020f0034060035103048003040c50781440d1395006d4284041c00305480d2050468400159041942 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 986026223 1250 986024973 986025059
    0x30c07030306050a03120c080f03040b160c0206030714090306010323030c060610121104090f060518040f060f05011701151e081b0405010e090706030213 67
    0x20040380c40e0700c120f80c5144c441403d14442800b40700201b00e0b22200c00c10400c81c230101900d500194020482c0d88078a0030346498040c0c07040c10748581d4800501050140b0340c0307074413881d4110348035580a88a40e003140c403025070035107404518100c881e440c150280045c0909850800402d40203501441007480800d6619644c003100400b00740c4a00300b00d030001c0040c0704000070001400c90b08100b007138503d000c0c4950307619000c0306e040b44611540e2001d10300b40303040c80d10705041444c0500151020084200403051000b001a41200e003680700e41c50704050621b04a5050030324143e00554080c0c000c1d00d5420703c881696446408484681c1c4485a50315540e80040c0a110065610860440c04040c02040125000782d0f41041d82c0541c0c0c810040800014200c07403030100307038403108100200641d2040307803801c1e000d0f5091b054444245000079030040d4a880c00005903600000f81007130140b4221806001c3c0941442d1048000e94021030041e124203580b01000544d030300b491b41d8280359140a0200c0300a05075801d22401c0710007 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 986027473 1250 986026223 986026229
    0x509030a030b18071206051914180f0601110d020604030816120504080c030409020915092b170d0e0325060e011d0601050105120609060a0b030c07030306 67
    0x40070364030b4102e015111880362484d040640e90900c80c030000e060b803c100c406401d040e041507810404000c40361409440441c5c480342235503070403a168211003c01c1c00600c040485840c40100400a481010903000d9000740c0035580c20483c18034002081c17004100b401032910394100b0308840141c2c401420801495130205045820018815803010302001e2440d0041507140319242d801910769840b00441e0410003058102d4034015020019a0340f19030b0380c3c4902400a400200d200360298041107640c0c9114941541103900c000002880c4042c4081e10090100e0100040c0d42000035941082c035186d0007140d15800300020603401100516601d82084142d80d0640b1440e4461031250344c4203200031107280c140d03a40781c0d250300300c0c40c4900b0300c1c40c400d080c0c14400058003c61424048075480c000d1140810801104001c222286030000c40c3e9050740d0328001110079100c0c2074210500010700c00c02280745da01d482d40c0c115810500091100c42e84503110301c811107a60f40141e075111401d41c00007490804142d0580140002 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 986028723 1250 986027473 986027479
    0x703050f161715010603060f050f03030415030b0607080403020301240612060f080c010f020a1a25030509010e1609050414031602090a05040c0e06130509030a030b 71
    0x1012815001441400341640100701c042c100302005002c10035410000c2007204400001c4842d619651490040c000303045600403103900504000000c00c0d1402c00c94400410000301178002c51130b0524102c410f800c100d2403000e1100c101929900c1c1048076540c3d110150003194040c0c45469900c03440e6104140c211030681d0305000b49881e194000c00e4910420302c0299007111143c1c140b8041c42c01510000e0001801e054000669229041d5008550703a98000348940c041902a2039000b000858600160b0340c61100c10002444411030400c00b8010806e81c160b0310342c01444000d96a02445140344041d09c1c485060910303c400603554000b0000929000d01076140d41109440c081c00d5075144821510900c2501c03405103041c030303544a001080400400c288114840703440341c01074945618000044d03980c02d540c5004140d1240c480304022900250043c0f113980d000f1503028640c400018a130029003c0468801408945d122b42110050003107400c1a0092910651144000e1a0350300c9200c0b0028003190f601000c5540 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 986029973 1250 986028723 986028733
    0xc0501092108100e0c2203030e0d0816060e1507031a090c030903070b01030515010902040e13030e0a1d070905030d0e1f020a03021b180603010f0e0703050f 68
    0x140303c014461040040e145a0080502c81c1d603191610b5038118840d00c100c86203000c1c0e107100940300101c6404030b800d00b5244a80e680d5480302028801704441f410031583d02800d442800c00025a08480c005a19800144a00008282940140300443c117100035071000b568558036082c104451a42d041c8911114940ca501c0070003223513002400401c01015008040504407000000171820064040041e07500c2942c3c0034070b1002031980c407483d02540368018021400b428060b0040040f072182201e000340c5058503005a104200c3d6959148410724540d460b03141507050049040744009179403070f40c0c1111030103040060b9800d1840c220900e02134080c0b000c010040020428082414015590040317101c81c1d22405503c4c1010740c07441c000c400035044182c014440d00c0004810703221103e02c60b8011500f002c0c1c1d28000d80039900d039034241007203111300c491a4034103c503031210034007021400030129188007507001603020b00001280240404404126104c084000c00035610107082041080000c00c002e5035010040d43c0500 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 986031223 1250 986029973 986029981
    0xa0b060a020703020f06040302040e0d031116020d0c031506050f0f03060c030c1201030303291309080c0703260702090109020306030a051b03010c08040b04120c0501092108 75
    0x30b4558403140802407060b01080c002c403280c0c0d50b491042d01d01450300240200602c0f0345c04101555140c0140b0a400d011038207090004e14080d10314815241000480f45005104504590800841c1000070a04848900d9540404000f151072403e14100b0031983ca1800661741c2e00301410800040e0b000c0d150640328444072040d120241e10081905074000304404095034407a210032902c3c00d69070141080c10002484031034000400d01d540758016046058203e00b991981d46001d07034000c01e2820b58080001d4114410301e072000898612030380710314000d60040302028104800440f246040c2100c0f94401d0303558001d9038018003a25204503070180750302d01880c00e0441c605481c50b8040752811405124080020394003000056203924280582e80c8065807001c2599414010381c0f5000c0e410260083c86a4065868113894120f0b080c06109800e0081d41c1000860000d030b65507a03288075428246589410400c41100480b00025809000311000144078017805480c100d1420300e090710030610944400f0801854400380 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 986032473 1250 986031223 986031227
    0x415150515190f02120304060b01080f0f19060f030c060801150e060f0d020703181202030c04050601110303040305030a053402031614010614010801090b031204060203030a0b060a 78
    0x2d5851112034181880346000702c030003d909100c60030079004100700000040204000d200d40c840d4803900c20076250030929856444540c0c0210b82c0c1100e03440703078205030780b00428132880c121240152102c9081c2000b1642d691070b49040000000c141c0d00450f405070050b50b052003140d800c018001e000d0a01001c0449400a8402c4010b06401d284c4407694000c003c00210714900000c034000701c1ea101d224404043d0350782c14940c43d0041030a90480750450503549446004280d40203800110f18000e90002d0040c4820381d1020100002000081c02060500c64003280444030000103202642c4030746c0c000d4039680d0716860460711030400d440b40100722140d690320750002082c0f282080d51070020030b10003020001c181107400c114207030715500c1500f40c03960019031005a00410008003011055400f41c0560080c058156100d03a0284601500c258003030224440038018444c02c41680d005891190b4002c003102e00c21500701100f900c81d540580c100e540180c0000041000c199200e0150b04c0c82c407a0251500c47c80c16048443c0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 986033723 1250 986032473 986032507
    0x604050d0c020d06060b0901030609060b0708031009050403020f070626100806090309120604170c0c04050a05060108100303091502030705010e241005090415150515 72
    0x800c01440080e40d842030030343d218210490021a030241040081d9a00c0741314000e455084166064002400c007070001c5100c0380c190050f44201c6510015207400d240055559446581008015007a0201c40800000b07000510780106405a0b0203034000c5d111015060b0b040c00e050181c0c41e003021007403041000320880c0d8a251081745020208046080440ba5210380c1c2030708e400c8425640c03200304184900010310007a100080003c10408404481040485110401160311140100c0380a0b060540314a40c01c10b0102c8040000c01003c0700039000e480b12501c2110005c3d0850b8400e803030304400d02e07a95a013000b015581000c1c0c416045460030402c4040702c4e06d182d40080144140e0300031807110f20120302c104000701d8020001d50300c0c5298068000e0158194080712180d4078000c4032407166010400a03401c10300e0750300510707485001c3c3c00f502811012207414003080c048400c0c400740c030842780790013081110389901019214240a826181f050300490701d140804124403060210003a40240e0010006543e00742c0107094 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 986034973 1250 986033723 986033743
    0x102040510030c0210060f1e2318012907020f0f0d02120318190920130303200c042406030f05010909050a0201031a030d050d0509060405 60
    0x81d003c0f03416190980120f00342042003004106030350400e0030100e4000f495548442c1501d204038100c051282c1c1804812107160010b115a0b40c5100c0e0340004c6111100c0d13040244120140050009403118002c20080c0106d52426400407802c0c40c4c0080408000c0d000c0c6940b003811080400c0710007420100c2c5174000070081c1c405941268400c0402032051800b5841342c1c9030032002150003c06118042c400458159141e80c0501c0301c0000030501d0359074004030780c944200c5503d0442038542891041c00d003400c00c0c0100500e0203d003400d0141d644081c00c07250388800d00005042e4030404920160001e031451a000d0014159400303103220200c0001c2c00310500702300005441c2440c3e02e0844000ca40c0a41a00c0060690030744840002c080e007461003000b1840c10703055040000d0000364201c0400c03039680c0c1e4002000c100e444400004003640c101d01008005584079402454025035445800407078210f16000103450101a500d0007000b0a8011030800340c00b4040c2d204039644610b0580280140b0720380381e5182d90300c0380c10b048 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 986036223 1250 986034973 986034977
    0x110108090c010c140307143a051e120a020313060207080405030a2306040b01170c031608070b0c0a081c090c080d020d2a05060a060509090102040510 65
    0x10f801e4000e003c6000c4038403440303034151001ea80e41c8591a00385404c0700a1020b98524881c030071544c210082103001a8800719020418071490f8201e0314200c0c0c5032298200b0f6001a100300031007409034113000307550a4161208840c24400b1303140c0d01e017503a4800b2003004000400c0761034442e1060040021008a843e0807a10807640001d0041ea201c2c66850800074502454004542621400c081345c0c082116000c81d003415004c052254460f04010380b01038669030b01040b01e0050015509000400071100e041007410316003031000d02600c0a01040d81d02080ca0000122030070700038180840010410750340f0504c860742c050100c80060500d000001300c201c9941d4180c0c850300900c02000003818103600500700c01040307a00c1e95481024003100035241048030090406000b009454000d41801c44100f034000560f51150800765150038a020b04403002d001940b01c41c6024560120204620100002c0c409000c8284250030b42c1e5400102a4245828019803d034024140c02c0c003603104008c240600c0ea90b03c02c000c8510f801c1c038 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 986037473 1250 986036223 986036237
    0x270c05010c151d0d171602160b03010f0b0c0a030c05010b03060705210603070302061c1a011e02060a0e1212180d0c020d0204060905042117060f0a080303090a110108090c01 75
    0x154120315003d400680381242340c126280c013007850700d81040118100d40702d07010000e180544800c010b40f4184210510300f8965031043c503091001a00801e1102d007078a00030000000d000c05083c1c0804e04110f01150300d9030010300009802d03460140e5070005074080d150040c1004800b0301d45030300401d649001c54080030f445034002080410700000705d10801e0000e0a541c02c01030062403011a2804613081c128104c450220700c41c2c5054000800c8403141c1c000c55043c6990040600780c03034103a0b00000602280703840e01d51030301035200400c00c1d00001d90010300544901d0110740c4c031245055a49a1800761000b6132481841c3c000803500c0203129072207140c089159030100c800700c06591107880060010700c0c45170b12013000c003418401040b0a1001310a0500070211101c00a120b11800245080320342d4203e00d44c1e5000310072094404a580303400c03c5008580c07442c4016104486207a200c0c100c0510f16001102d02d0b070032030f80c0550846403c00411001044211400782003008140c1460910652035940c00b2a1446c1003080c0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 986038723 1250 986037473 986037511
    0x12606040e010213090b130203071b020301020d02130e0906040804060305090a020a03030c0203060f011226190e0a18230a270c05010c151d0d17 63
    0xe40c100e900b28400800d0304d84002d696001010040c040c9011030900c55083d00069100c0340940d0300803648034103216a41d005103894072610001410030300716400d903015982070280851040e1584000d11034000381c03060f041030b00c900e0012185111240204401c109810282c24400007814140c26074060b0303541420b01082c075a0383e04030714510f0030504036070184d8064203d203400400c0c5904039108000003802038060700c810340da034071841412821003882100400101031241002196401c040101b070400240c24441040450010350100364206d03c6400d42001c20103085c0710342e0f054001c10308448240d026a0b400600f540b03022191003100040d1040c207800a0780710400c600c07241941c000c0018980d405c10180e00400e0504130f242c1c10080076011030030a110310890040e408851480045c0390710803075000015050090400d03004403881c81084404640100084030000a0454180150020b104910368508113003941201c1e40740ca011407801071001846001221a50b004d1a9000400d9001c48801071600c48010 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 986039973 1250 986038723 986038751
    0x1e060402070f3f1206050f0d02060d050c040611011b0f0e03010f0c020f03040f060c02011e0815040c020d0f09091e0606020f0c0d08161101260604 64
    0x958541c125000000f0000c09030380c402418040304182030310380c1c1d130f504020f142005148003219418050194064146203200074940fa050104411040c4080d00c41c0b410441e11603201c50586000350b5944032025000304062081645c400c894215a42c03410009001c41da03040c4480140038542107a030607080000010448503000d002d040f0070080180040c00820510808003002c400a003018501a001405035800702c8010700390010550381070350080d0a441202910308441540d40118425049040c000c400d11030f44854520b40c0d89034111143c1c0307600c407510a4602500101c0070950140480e601c154586024a8250740c0d000070044542116410a004680340792241a50301032641d608c1503c40301d04283c108941804c1c044c40e04030b0540383c1035405001c407a0b140c0c40207a0312103041411101c2e0681c0102d4245d20345182031041c1250442c061940380d850130894880d01005400c03419010340c0c03e0030141ca0080784a503481582007401b0940b00352100d900541c600194500a18050041842030361a4980844038003 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 986041223 1250 986039973 986040023
    0xc03150f060402070f030c1b23010207030f1a0c040b090d1e0303150501020601062a08040902210105030d03020315090f04050706050307121509051e060402070f 70
    0x2d07030130580e5801c40c09411b2800602c01c942d024421900040f080160f04103000c0401c0702d08003a580e1202045262412130300707061000c0c2c25041803045c110304c0750030000000b2803003140c82110300c03134012100c4034032252014011550402c4041e04241d0040c10400081181c10203083c1503500a010807200c002d2023007214180841c00307000310100b4446494103490000101a01075100403640142d031490551481d907501c00681e1200c10034400c0c1d1010440d03c00000241916400d0048220400d4420512a40806482d410313000d0300290032240241e40d00080c84a22600c004900115800012003011815070520b00031940314a07920036580c0070f0603000701c01b24119004c090035080c100c0030003500841e424949541d1140b16200d0680d001c3c2d80d18009c060340401e641d441a0120f81c0718a0040d00c46d1044007010300c0f9400000d21a00c2c00c1d141c00390a0065000c510f84406001e49801141c155a1000d0034a800450000c4070441c00350040e845a0b10401420300000d03070f607001117a140c6410030303004c00314210045565404d503 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 986042473 1250 986041223 986041237
    0x60f030b04050a0b0a153903121b23070f050d180e070c050a0c0609082b03020903031e1206010c0201080a0f022503020c03150f060402 59
    0x1c5400e20080040d0040e0f107074000d2104410407508107103000c6d03640311001d40c030003241400c0303500003070910b0b4090456503540030b07061802c1501001d4003040460480c010b1500b00c200400d045000801040503603882d4206401103604a840c3c240c0300080d10541c100c806440b03040301740e0a00801e40c0000301880728090300c22050b11240c82d00412080b00d40b80640c6000c0703403a5441390808002003840590b5001c050003545656006884043e0040d508035140c0080035540c1c1504a8400c81d8548110020000080c2003070111720001c2c4800d40350030014500b060319241c00d000e0540b561b4a58051007080309100b1403419006884045400e04005a0740d00280300464154805d2030f44070708280c40070901da2110030344400000e0800010340c001c2506036032151350045440c0441b04802030300142d4150301180500e03040307600c840340010010800601e0503a50740b05075071102c0a203a0b910642040b05100f4103062640501103100845d00850162180f042c038214000e884640142241c80215003910006406d0b840702d504495107 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 986043723 1250 986042473 986042479
    0x120b0d0203010f0204030201030507050c0a060b21010e1011090d140d02071d041a25050904060812040311060f0d0b0f01050c0309010305090c0d08030a050916060f030b 73
    0xe601c00c601c80d0013a600c544800c0340042c0c50900003504592182c41a10302504262000c0d080091254460401402c8451038640e4040c00c1c140c0801004003036000904150340808001042c04041d100e1550f0500941c205484003050828105600020001d011189418006c5a001103690001d060000200002008400961050310301780003040c0e8000aa140c100c4002c0303a082c11400559041c40494140d05480003000f044070384003144924070b07c00c5900ca902440c00242401405c5110928a80954901c503250300401c200050f0294213003428015580905124401403403081000d0117452014800c03484042c100c155401400c1d400c550f035400448171491090002e003529003159900d400c000b042a11181803164181840c105e030f45502a01c1607034031044a0030301640c140111100190007904001300070303a1007801a008183c402d80d864090a000003400b40700007035140d00e4007401007022150040c15a5141c0d601005a044130103296100010a03256076280404040400980a60251803548522a4 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 986044973 1250 986043723 986043731
    0xa09211208150102010b13050a0f0501090e0114060901120c091508301803030703020d120608120d0e0109110321030f07120c0e0a050f01120b0d020301 66
    0x1040ca50010007203000e958107100c100165159000103900b00e400d02501d0540024240d5071490244515502c02079100700c9651010078070399031545000e801c481090308648411903440c00e00aa100c3c1d000d04c200c850042811410102ca400c1100c00502400380c14840c031214101024600c000700807120020500603c00001c050100d01c450518812003140140030381201881038a446482c80c1c0d0809010a00000f088803d580e010200074107000c04590025011001c003c0180305504c065440401c0101041c9000354060602c070b400b1190000e000141d0400c4070b00040c1e04040040c845000040b483d10817081c0700c00d641030380e10780d840125200a800390802580480d440c0030410b10034000321750855070300c1d04d6044040d071303070014000031103e14011500000c500c204081030000903142e035484011540c01c880c6904104c58541c060300e08520540e81015120320001d00c288034104a24201008050080c00301291301040342811100000c4c00020b03030301c0300f414105445607000102a00c0340f100ca15006500500244 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 986046223 1250 986044973 986045003
    0x20903030c010c1713150c0203091815030703030905010815210f1f0b0a05031911011412041e0b1e01080703080705070512010506040608030a0921 64
    0x381c0f500ea030078104c0702002a80000068036840301d410b40d003103403c0d80c480080c43c4100152030241c40100303981400c60007548020802d1b2a60381c0e840007101d0151110500c5001e49500d80910560f0325049110003403802940050300500c0041e4000c00d0f45000c0d58000e2922b008160768000c00e01801115480559070440c3d041510b0050144002000107051200c0c0000c0342c510000c050b6000369a81c2030024109000905090b8818200301190440203544100a1103100e52580310781c00a03040004178842d0702c5001408051903c01c11052400c190b80682007400c1210129075803094001b038512445001c080d4a070303585e82c002000c000341c14108101d10340303045003004c80f001680d10780b2400911007643c01040d180004d403039580300c1d226030003980e50503903680c040034001d50ba00c0d5a844019079000901c04941500035100c011034991a1003022901c00c50140b000410207041c840c050bc022160550800e450719001001521071060b040410f032021913410607940d50b0380c1c0419051b40460040c400720001c10300180300ca41c030 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 986047473 1250 986046223 986046227
    0x20f040306050c090f030c01021b1306080d0f020105070f0e040f050118051b09151204080702091b031f080a0515070216090c11070905070e0108040510020903030c010c 73
    0x42d220004d4191404190a1800001c05076250080c98555005900589081c4000f5a5881e88074480d0079010700060b0314600c0c5010610140c41041e00600708a900c0840080a8290f210b900d800403071019000130891414429001444201101c44d00c0c8140034070603200d043c85131295448032110710203a400401c00c030358484e040000126102d00200c2c000a050071b000c2843e0400107100d29502210400c1d0040c84c210050f4148400c1c2c40d482c000340300544030f0500c1540f21007035000e4041d6215902c151003c03075952100788100b21b17041d00040c150101400301500c000100010820480b601300c0120000d4410010545810b8030f460101e54004106a0041590762000c01c18005111ba2040c49112410402a614140120303600c24030590002c01d1030714110000c0005590300c0c0d002c59061780c09031034212082035105170340301c1c9064030a034040130717403687d441c001c005409501640301c0710740987c246450301450405807151a0303203a0140e014000f01d154000b031990b060f0383e001c01c11a03280000341002840340c240d0b40140 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 986048723 1250 986047473 986047477
    0x21809030a09080f1506120d080403110f0604020105160f0804090b011706010810080313081e07031b0f0305030a0e04090209160509060f040906080d080a020f040306050c 74
    0x2407000c14480c46012402c40300200740410710b0b4035844000c0001d440d01c2c68003008094400b0300441d42015940390301c140018014023801d4112030341611907040c3c900302464000e092042c603072003407000703504074400020300c0000100e0400d421507024682035803221f2070400e066082d0010898014200c86c8607203528420031803418094022200140010041c150f2840015075151141d00c600d1030401c0381140000d95076602a0708142d401000000c007042c01e054580141925551100f00fa004a960f9500b00c10400c1c040c00b00904030601d0a8914508031502d00d00188544d01c2c00a80402420750b854100080000340600300644001c01d0041488280c4a9580c01e000d0346a5000030700d10800903003045103281c103074280340c0245100c15a0141580250f079030f6420001c544030020640d10390070000c00f0030801142e41e850001421800d03048107000d035a545c0c0703020303ea00c007100d1556002e8103080c3c001814a000312500b08038400da01040c0c8400150390782184520f262041d00c074030741004140038500b00c14407111824803c0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 986049973 1250 986048723 986048737
    0xf01202404021002030c06040308100b070f0b0117030d05190204060c0b010f050d060506030c040203160e030a0f030518030d03020c012f22031119180902180903 70
    0x184580740c1106103c0880e1a403242e540300b542c81d94454008180000d03c00d40d8000c0c2d100c90343d1405030202d252600248441688020b4044d40d018039203642501c14441d1a03040d060041813025003401004480c8641c0036100d00520b07411070403203070365000010071001e403a541ea620702c401080300440d070765526050301a01410403034405a4810000400101d90440500c000c102641d000400c01801c54a0f16600d0070040c24005241541500448000007619140d5001a40c05110740300b00c0910a0203174404020600c10003500498401c1c0d01200c264804030b8854500c00c80030a0301807070529612240d40c1c061198108142d41000d0309807003031040c10903900364198040c00c140810b0340024800c0042251140d2480c4a10f4803220420322200070098119400705802007180180070348843d03a4400480b40c4e540da40b00415401642e1003290000591102d2401d17400b402d01101c0b118010742c0459081070a25002c0080100102c8a4a0b03501c06124080d9601c142c60201d03048866a216069450402e8465480350081d030 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 986051223 1250 986049973 986049979
    0x110f06011503020913020714060411040c0306050f0105131206090308090a110f031501080a1718150403050610060206070314130816140c0f0120240402 66
    0x9507016200c00d12034021114004e400034201c8062454070035558000b548a145c0032206810041c03004d1131403810510903d03206a029109905c03007811010103100584a81c18680e104251a241080c4615a0340c8422451182c00170318000307854040d8030401014060b4550048440000c01c40c0c44842004980c0c0c10002d0301c1c0744a995100011740390350100307507079847c0f0a542c020218010310b05502c60501307014400d0307a0301c0c01006084071641c62500c0c040d0b800c1e805c0b00780c0090315160040800c00c000e119148030800b880000840c1050300d04038240000c0300d0b50180000c4518840e80c0b4400700c9080300c185c203806480241d40c001050310001c0c1450b40703468103203c00911074840503000d10030001d08824000c2c4610003808508210710714072039a410141d51091a007044084880743c00c00d210b007440c40c00b403088081c0b48440c03180d6841030620781c0a0144d10b1400001c801e00c02d02c101c6002c04440c1650340c0c411840c004a140c21194011900304035a6024242410084000c544142d0725007504400c81c1889080d40c0601c0c025 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 986052473 1250 986051223 986051249
    0x17010c0201140f06010c0c15090326040e060d060e03070c0f081f09060c09080709020315040c270f0b03041703040f0c0b03150909120a110f0601 63
    0x45584001c1c50396085aa0781004002c43c0009051035014080c201311140c414114401565180e107178003840c1a03102c1e021400000e01c0c9050500400c42c20554001d4000a080812040300c00303c0107600815104600031400c1e044041004689940c44045d10211003e03032061040c02000f411810b4940c1d260403054059074141c041c1000000d015031745002079401d40b207907407003d491702d52140700c5924101610b9001104006a48045400200b04c25100d101f9024805981d817003d89860080210300d0103015070440009144104207200365002c444480d0100c251040d10b01082d21084a18295041e4000c495443c141c56081e00c0c032582a03100031040303a0301b03442d11445103107596034503500811850300048800409041001c01c2200d900c040362009143d03c60300c1a103003090f524a035039a80340c0016460768007100d03100b1004014851442c09005008441c9802950001a40e24200200c02e03a5182c4446a05440000002d400c00d00c840c030564101b108450014110b50445000c80d1515944e000c00b4801d901700315802c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 986053723 1250 986052473 986052491
    0x80702090a060e0a0b0d12200615040f0f111e2508040f030506010e0c09030d0503061503040506070e18010303120603140105040314040e011e17010c0201 67
    0x41c800d00042d2408201c3c0302030242c0d1603c1c41d440042208030078890784034030891246000036072034007400c031540030041e0340c1e04030080e4a120010310702c075801c030303e11078866003080d810070117504003091815815900482c0c0125a01400300a800c3c002c101c80b003602d684040c2804103600840c20f80300001c4c0101a00445942100d00004a818005004200e04a0061050243c400907845203842207200c281c0d0042203004d161039134132040001401501d510499854000800401050070942c00d10341d40301a192003090700d05041000043e444446d181c01c50014414003101048084d1104008030007100b038515005030340e03400e00f4200305170b6400085410100049445481c0002da04100c00345403400303641304020b030b00d4503425581c042c0c414a0360240c400c44856030f01c2100001240b10711031442c17040f0000e8000085e81c3d0829040051042d44115100150420104420020f04806518443c11540c1c02c40508800200c0302c442c0003410401e603407211002450303200000d03800400641c46100c050744550020800405 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 986054973 1250 986053723 986053741
    0xb060a030c090b1305060d0e0a12021204060807080a02090307140307140904030507080d050a330605090411270913030807023d0b0a0501050d090f08070209 68
    0x12030108000759a2584c00310801a5042c80c038050b20000581241c0490300c61502801c003854440d4407102600d0707200440c2d03928100300d9014000c079070451030000212480e05051030005003280401070a1402082000302c009000d01141e94150b812800e00102500c0d4200e94860041150b00b140e8041c441c07090043c1800011001d01c0c0941c0b6000810016062081c140c2d12500e09581c513402c04407065995032410002c1135400d80d0140325040c0b00d00824030000808035540031a03003a8146240101d02c40145000a03070b0b262001150000038110703009407030015900e501d07110120300503024510a01400540100310b4415841c494000001000e8403810300032040e018040410003421019078006c0c02074406141c980022074428a18250f20046a00442e190b0b554515031000801c28007a00001e0f00401140354141c0f030f02400911030144a90084050003240c0c0420002102c1100070b01c107075030602100003a000020138158006000c51a044039520041d5261802c0c0500d40f03a000c08012482141080005100ca40c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 986056223 1250 986054973 986054977
    0x9110a060207050d0c1a030412181205190804050909160b0307111605190509160c05010204301106090612011d0f040302030a0c03030b060a030c090b 65
    0x3440036402050214070b007009000c01c04058480c103940c811544100401c1c0c3d071840091340c0c5581440c410215a5914207810008441003105281c030040003404440f2000c1109040d90b0141501c4c600390f2240f643d038001d840d217640b8012580440e109156030b40d0b80444e080c400e13440d0142007101c4043c0c907000d003e031780d46a00c00b90f00c0c5d4650b142a1454200000c40a215078170088020b90340c004c10b40e040840b0070300510070f001850440c000ca010315458055103000d00c00c81c01c10070b40c15424130750300c1c101889440b41018005200640f00802040003240091444c2c002d15200300104158586c1001c000c6640f15110405290485200c20750100503041d820204105c1d009480300542c013058000d00902d09040050040040c0366100d110714650140c0d007131040c0ca50381401070341c119008003074140307400402c010540154120008000d0141c08411480310400011940200c210b42c0384030824074001c4402030311454103400070b1841070348040d00458041031414459800d0390204040c4134a43c1c42d082e40090350f44142502078 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 986057473 1250 986056223 986056229
    0x105040c0f030b041205040b0c0c0120071a093d02031c060801181704080a120927110315060d14041b0806160507022209110a 55
    0x5a200600144c04120781601c42010342c20320349003017803500d0b594900b02000364200d40128070040e0401d0a8540031583c0002000a140103051180071900e00001c10b816166038545c40341900103055802c1a44071501d500741110066030008204400340902070604848035144c0007840010303419821005924528100a10a12451030768000c41c07509101c440c11403404a030003406e590080e9110313140032461100a00070f21560325a496464288072400742000c4c40e00c11303907400c400c0c60000300420042c40425030100c2c09551142c0c01c84400320f02140d0300101214699030642c4048004402c0c0c604842c03541050042e0921029180394090006201c100c1e00110300e840f055803504404610b4025030101c2c4c0c24084054002c0c00c0309800d00040f2035410b1841c00e000907104032000c448080d4180c54250020241012204c0a04400801800d40b860b041e16968241184070000c1800c0c0031021a00808554566a1220510801900a68107005031a40b020040d018a034400c035455502031032502d100c0e05010700c0f08811 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 986058723 1250 986057473 986057483
    0xd020c0604060f09050307140f0f013507051c05161803080a021609020324030a0c1511010b0a12210c1101030b0a180b030f0105040c0f03 60
    0x81c003440c0031815200d49800807600014049400d8000469903000d1040600400c04040303d1031440c00c4a1040007494283c0f050b4482c4244003088900520782d07402410000d855032412600d41c0c8124510b80c00c84d200c004080611096000724004019070182e0000140400080c40d20000351030b40c641e004d005042e10400ca4445034a000422454006544900041e0408000c07400d00912125142d4849400399481031b16a100540d101d0204808204556002e0b10010030076003a0440c25420110f40d1544003121494920540043c01411891140d8045c46880349865000e4442c16440b9070702c10b0300b0001c8201b2111003402013020f03a084e120619a041c02103c020b418010503105240d410844504040c6503d14001e0b580c1302d143e50700348018245ca044904003c280d0f1360300c404402039054a0036120000040100a042600301000d25881f9116003000f5016106107070310751501280704180f03603401042d00c0802c40e54180320390301c503180740048190300050080d80107031100d800d1591aa404065401c45620000785 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 986059973 1250 986058723 986058727
    0x7050d1805090f0f06040e011a1005070506150f090406050402040506030c0616210c0c0b120a110f0409060f090c080f04020411040b0d1a15070c12080c0d020c06 70
    0x104a04644c03545990203800200002104201118050300310752a01026015109c150100d944862500c4117005820121920b0598902079203075071040e0300e402000c0c14103040503911002807a03a5a580440706d8819600c090045051441c20341000c00c0500020b680030b03030040c2c1c50315000c90300c542408141c0f0b0104582c050722103031038404992604030841d04030071400d90745040c40321000c041d9100141980304605141e55a0048951685d060003400b5541c16807003071741a1070042200f401485200c14403503500c041407500c005500303002d9030942d40952240d004d222200003800640810412600c0d80254281c80e005810394070160348a86801d01110704504002011507110030010714140b01c2001501e42c020b102820228034058085280e2070380b500181c110148044020402c485031034558440e2545400c0441514020410b01c18003240070401640416803501ca070000e0b0391000c1c05500d000c1240104140c6940f004028803a00f80442180c20100b461f92084c09850849104030f440001c204041d00402071050b4 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 986061223 1250 986059973 986059981
    0xd0c031b1b0312182103020712050309012a030f060605042303030a12051f05040906020f030114030d030213120312050903091005210c07050d1805090f 66
    0x243c1c0010034064080005911511000c140c0c1c05503242d2030b000c0e2841901003000c00e41c510180014251100341143c02011720510150010031100ea41d003a00d180346909107035542741c8503680c1590140110943c0140720701b01c640000020b400e43e158102400e2040b580e0304101e8034180082d10f0301500c10604c600400600c081c0b0084c810b4205500042d23100304101e541012288841d6400310381950404044900030a4410785000750000040c040c0c0c56100e4122a5114941c0216584107010140c01e40101800349640e14211010400c26a040307998601d03080c2039441d1650303502d00f00c1e0680d66071040c005138082d01840f2201441d01d07029000396501d038108280e09410190410311700701d0030300419803000d070b0400884480f40c4105e4805481021b000d800d03500c01440c0e072002c000d410700400020f0a2100010868100141440409424a1408085142d981c4040790342c440c050002c4030342c02802c00242c8607010304800703c0081034000150000b07190010816040030780d5500304000c10014101c8850b220641480006 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 986062473 1250 986061223 986061227
    0x501090b03060130021c0b01090e15031b03010c0906021b011205040b0a0606090e0609070212040e0403030b04020405031b0a0b1204140d020d030b060d0c031b1b03 71
    0x50001c09000130b400c80d4003100641e414200341c41d0180303064441c10b50f0000c0c91030410b00c405000480041c62048090042c80030260008210700b48074400c141e802d01480e000310b80c4140046402d0024150f000301115642c241500d1030b51030f041c400200d200e00c42e629206010705281d0144100034100c0b11940c0240c91070700b440c000e000c680c0003140414541003040e4480314680007143d40c071400b40118010034400c0050715080c030302d840c201c40c25a00518148036100804201c16a80d5801c40c540c030030016030356801131741c45226003a850300203a9103508550981c0410081141c01040c5090f511035800303581c1c280109840700050004900c154080c0540640140e10f000000d205010b900c460114000f425103038019940c1e00f060b6403107400010019100034504004e0106100f250040c40b00f80704074400240008044403000a50380700e4064078140141915000010380c155a0801a00c142c84084031003400322803a924001002070241c580600d6410310a020052303500d500c41c645030861110880e00323400d844200d680301 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 986063723 1250 986062473 986062487
    0x61207030c0e130b0c0307121b110a061113091505011107092d02360904060b10020c060a0516080c060402031908040e0c070203070e100501090b030601 66
    0x58081c5070800c40f40140014609450580b050728110001074030b0381082c0100400b4009a541c0413045507050000c02c2c0d140d00d00d0300860301d00102050405040318440e000700c0600b44000d0b4a40035040b1442e11008641e5440c10300001c140100a540000c0141c0303072150307410011285d21107035040c60300c200140203101a5014001c1039030b10700900000c8681c025541e80e1403030107551500c10395842100c01501c2401d1510120701e030041003101140025810407480c003440c00382c00c0301079804e501c0003c209146556040448002c1d00c149440c0080d1140c1c58914080c00c250024002c084403080c0250240da41026400e4030204003018003100c010100362a002c0101d108460b55001a84c441c0800c0510107041d00c0061281d500604500c54402c2c0580300303a00d070034010581085d001028076644805d26048010004410b803003142c0903600300e21402d0381582c443e00d0078941c0501074000025018401c0500104108418070400c5104180186031420030584030740c0115205010384c440c4900080080c00410b00640c06408 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 986064973 1250 986063723 986063731
    0x33e0105071b170304050904030309020d3c050a081e0304050715050a090e1b030906040c050409080301030210020a12050a02071a090409150e0105061207030c0e 70
    0x5000d034244100c0c1d84401007810081c00300206004854a030402c507203420500607407107a8410782c0241d41420b1512000c03c1c0d0358540244014101551085064119650104682d41c902d030000b00ba1740309030111049009401c200d4a40c0e51700e614500351080c511204140d540e03210010703801005464071480c19a69804550840b001c0e0049100c545014500307403125050103544654090340090005901c2c0c03410510740b06500105007001c019040080302c004c29002040102100e1021a06584070364606030304e0354520210080400000c100001840202d02d000605a80954010380500c400c1e25600c500b0082216900900103100704070500040000d890540d40c5c29010310b000d4016100380b01d200390f8803c641d11030020304a4020402c049881e003030031a410400369015001210000101840d2045099400d0295581d1184115116404802040307402400b400341407120700d030300f48450701e4101a00c6010705812200d15000d140c04a284400203500050f000040343c0e080200c0c00e0129041c180e4030383c2a100002c0c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 986066223 1250 986064973 986064977
    0x1a070216030827030a0303021306030507091502030d1a04110406141803030309030d05010501021614130e070518250203090603010f0602060708091c030f060f033e01 72
    0x882c120300e80d2130034403e01c49113078440d44d001a070b12850346066010001d40c641010742050f10f005c040018a07a08903802c1c3c0142c0740c5240d5440c0340c03042d14040172491840ba1114006010741005030380c6034400c5c5021040742c81ca038000c03902441100350004500040303010301d01c40d07031000810f1120785171807141200005141c0000800440702d40c424100c40400e02d141d10a45000f03500780e10006580004034410b100d8140500b0003440a0a80c0e4850117100d0008040315024010036010a0701c28901c2c81d550b01d0124010300c21100740c081c045040102030b0262991042c0c4034a038044d007480e4080c0354801e0142d0741043d10640815588020b5004c1000e09200b420020503c0c210551108200e07402c8185d580401644c001d0680c2c5900c41915030070000001e05202001e05030609114050301446142ca0010618840c0142443c0d01007407010480d01c011405807414541491015251200106184890b102c080060b6401081c0c0360440c9103001c1400a0308079002079060134012030503401101280c8c0e8141e0824802ca13414 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 986067473 1250 986066223 986066287
    0x10506010906031a041d1b010f0e011b240203060a140d080409050406060b0c060f060a0302040f0219020d02120702040b10020d0216050a1a071a0702160308 68
    0x12801040407280000d11000404103c184d80c200803403010440c00c020b051850f640103807e10b20314070019009150030a4440c09105a079190781c4144c1c0d00c81c8294607160101d403c3d403000c2007091810800a880140300c4e1001081314840c080147d14030060003164003030750b00a4405044070b0700d05600c400003120b408102640c0101000b550b0f001183c070310806800500440c440024041c2814a020b20498006c0d074047d0f098090180300400d05603c01144075580490901000b910541e03a00000803c8032100b038000a511038540502c001182407940c0c060302074403640408880c3d1801c01410180e9581c0100300041300107902061162100400d4503019013039042c4007420210b41201420002215210508031100050b401014000040c1c3d5042042c5401c4d1000501005003070303414500414200c0c2000e0003071074022441d50a100c044140c0880441c0c903640d0b00002c01000e416506103200d42c81c1d0070150781d070030010b1046110811074804061080e03000c40b0ba20104640c68004401000154a850104c0d20b40d044150 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 986068723 1250 986067473 986067521
    0x1002030a0e030d1505010903030806311b020309030a060e100c0c150e0d0804170a1d012a0609200103050a050603070506070804081e010e01050601090603 67
    0x100700040c10412000071000f0407138108144000c2128070050f0321080c100144d80c003041001c290040705043d04804281c911440a05255081c0610221403403d0160009400340c1c0740c1c40b03400a0369103c0a200841c00d00303022085024000220703aa4000c0c4244141d050304414501c0300000c0b102e0f0322000c01c015545007980c00203c2908407a200302d40300c00f80b014001c5090041220b0070442860b002070282d4030442d10803c1180400021503558025581c0b514090101c10004a402d102c41e01c840303403102c038200c6a1025130b01c0b20580f0000b000085030754818913000380d4002c582c03119503000d03541101e85080c00345d041000102070201035100c0f0039420718041d9811036540c1d410780045074450a107107070b5001141ca44070a0f02c801840005044800041100e20305a00d000c2c280001030741c0c04101ca008030780003200c406484c0c0e2003e003045540c910455001c08050f2081680a41038000d207201c800318a01d01c0b486c000c20000304013200301802d0390302c05c1726418002070b140d0505100c0b90b400b9520003a5000b00240c0030030201a4 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 986069973 1250 986068723 986068751
    0x90e0607110a050d0309121409010f2102070b0a020324010509090109060f09060b03072604150b01030207030915031d0c10050a02030405131107121b051002030a 70
    0x1100f013810380000e8440300340c0410b002040551800c0c5144500d8881c52014240c1d4001c0224010103044604020300c4a034104550780c0306803110b44007c0c02c0c01451510142251441030025801a64100c0e00c1300910000a80005400e2003600d00c0744000b03602c1324640010301a151610041c410076401d041c000c0502a41c0308540312104c00d50301802204900040329414040e015500300201d600048403542403440600512440030152074105015051070680300b4140c1c0c04500d62040b00d01d803d61414031002c0100414046401c3c0700c1e1050520914003000a4601a0011401d034803c0800260220310f210070104003900310074000b00c0d03050070a4900019101d2201c5884003100014049080d82c1e82e1258008038000e01c1c050f1441e1058070114144140b4188201901a480b4000d038480c6a03c9004440300702c070350b0003800d03801c212081c4036505e07103540c2d8803042e81c544500c10250400c4080006907940710044074054000c540c0340e08880d0030600401007001c440c003a2101035400200705540c0d03680c0b10781c00040072407 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 986071223 1250 986069973 986069983
    0xc050c010f06080c0d0206070602130b0c0102030717162a0b041403070c270e010218060f0906090a0801050f0f100609050103231e01090e0607110a05 65
    0x19074858800302d91030b880c0100203460500103039001840b410b84a0000c4005a4038072044600640c1d0004000da102c800586c02c5100c0d10b101070707000c14114000040c25000800c01980214890400768a54104c01044a040800200b1080b924000104500700b0303180030407130040d001380daa8010a203040500b0390000c4013424031000785040b012160341c0c0348202400200b0108901074070f00942d44000035424505c1701d444605400c0ba4512441d800a21301c48680107021048009c0800c0508031303241c1c00c1c40040d4004514038001d5218560031510002c5920b2080c80314a0540111004c0c1e111401540f4105132421080206079402035501ca80c0c849900c40e000110810b081c003035a446455074280c03c0b0102d18142c078001010300305c024007c40d40380d80c0242c41402001e0f04102c154090f200203180004007114a100b015120140101040e004280b11404201204001000280d0210a01569980350343d031707035403298410340d0781010322041e10742c12840c0002c44071880f0308403080b00c800a003001c0714000c200e103071945070601c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 986072473 1250 986071223 986071241
    0x120f090c140a090c0c020d0c09110d0f06050916031b020a051005010302090f07111b03010e01060e04060e0304150315060e091b041e06031118040c050c01 67
    0x110011140101692524090b00e4000306103145050083d61982540100318650000009210703050491001c4e0920844503074000142019041c02c1201110000c5aa1402d82018000c1c0c00a2810038120540900c9076028000032102c014103403200c0c580b1880801c03a203003e00c80180204156844c01d0b021070340f55000303100e2580440150003030841c001c0281400c60034070003a1821541510b0420004000603101c8482c015402000c11401c19402d13151400111128030b81c042c000789003403051024a0b1075101070103240400d46502103008101c001086108a802d0b155540306180980708100e0006002c0b40c001d401c14864a11032000f900c0c900380e21038040384648401e400d442800241d41d0b000f0034041e042c00d000007034060030f040e082442080c0e0a00c0700140300d4040c020301d103034191100c00d841c2040b0303a90341c5016030b40604100b000c2008a5580440b01d01c00e80030342071003000d0000c0e08051000d0480303822030381100c4c403020007141c2c03482d0060b844805000143c4132054a5100300701041008040c0c0e40401e10803441c0b2 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 986073723 1250 986072473 986072489
    0x706020702091003150f02070b090106140d03020c0904020d020d03090e0a062304020405031e120415110a02130509060f06010c060b12070303020d03060b0a120f090c 72
    0x128002401400741012000700f28540c100c2e0000002c3c000b08468401004d0100124a00032881ca811244000040e018904000381034400001c1800b01c044030642040c02940c15400854080324466400c11810900c1110040c1c003503041030140210b00e00317014030119070180c0007a246821400c0305601242501c3c00720304d02035000a80c400c805025200d5038205590300400f00c4e507000e11480e418050340c00001a643c01e1780250803601142d840391341b5100c3d9010350b00108070050546801c0d0303c01c100c039044040010405084079001c1d035801da180b400d071407900f40e9003a22074050240d0240c0f00210402d6441ca0030704a040390309482508800710040e5608800e4040ca40c80b00da0f80880c2030306111000034900345000d400075000c2c03a000c40c100007841c1d81c4043c44800725500101c0120301d1000b8900400c110301c03030080032103a650081d1380d0003009154000076951682c41f41540c08204003940e03250740c40254017800d00d40d940040c401c0101544621010380007c50203880118000801440644c2e41e40c6103541c1c41c1e406030750 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 986074973 1250 986073723 986073727
    0x71b240311070b0c03040c03060f0902150406021c02030d050a0e010b0f09060d08070501020708090909121e19110705010912020411070b1504050601020c010c080c12070602 75
    0x4440d854000c0300d40e4840a20401ca081055030f0381c8102000a0080c860442d0060110006041c841c42d10042c80003540c10280c200000e1500000d01c10150460706010303030040c01c0303034007814040f111040221011512280d02a10b01441a95242c50030082c1c1e402a180031884180400c040e0b400e09849440d0182008441c00112441015092400e448040244900c283c10b1581070640a458248503181c1c84402103071512079203c280c8c0780c9a20303c0d025020019200d9840800c200c400c02c059a4020f0016140880f802c010a5540c560060703503980c21007400d00200c51040c8094807041d1030300e0204101c1100b00a86e014100401041d1413543d90190051000004035440c5011041032024440034000c0d09003840e0111403130342041c4070107442c40d1070650b009010359660700041075603410140540300c035568040e903030520500b001c0500c4000c418480c01c219208070301d01000704078158000200080c4011041c2c454000c6035619880c0d024080d00070002004290151100b00304041000000824100303205903001a = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 986076223 1250 986074973 986075039
    0x1c0c080a030c09090c09060f02030c0a0b0f090a08090f061b07091b020613061112010e010510120902122e02160609051207051c14071b 59
    0x3c01d4200c0350fa202c0030803186440d0416002582c046106070a641e246c0c20b1020582c003a20600b03e02c0c521070895a60f840d8040c210720341c0704025603516010700a078014400401c1603102d8949041c0c454041040c0108040300410103148070b030800c6450700c0701c2c455000700451f00f450035080509003800c03a0ac401741000364200b002c003407200b0681031181e50f030203611100003100311001a43d006035170303200050040124190190242d10400c103940d004003980c2c0100303d098644981e41148100c1c05aa0280505c58a50384c80100200c0d280c20000f512503001c0746d850340c03440b43c600d0011000c40e0051030401d0059811010044e00280880d100300458140b104821440c0c80b405000721509042032a2640700d000b00740d07401081040e028984228500a40302d03040070300003814071102d00c2c0603403403e480c00c861140c400c0c0d000b240481c140000807400c55608000101440310300f00060b14103c440034500c0d00e545800c141c1c02e1051030046116070640403482003454903038050554851920403050150705007900640010340b10320b2 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 986077473 1250 986076223 986076227
    0xb0702090702010c0e060c0115080a0303180b0402060c0a080a020307020a0e06010c02100215070309020907090e1503030409020f0c25030b091c020105060a05060405031c0c080a030c 79
    0x380d9440701803803000b00800e449820000306071503440007203d48125800300700000710010a60041e207000301c8040a01d1180c41d038410040340c40303052001098010138941800708594201090a414103158041402003d030307500c6a0800caa41c1d04a800e02c500117108200b003140002c2c40c04001001c200e440c40d0015501c03a4124410016510029040348070b10580f40c9003804500d9801151180071142d04a40b5116850301e00340c800c03840c0151200e001a61841c2c0e032001e210049406038022001e03140281d4900902d543e038120f003034600c40d050b07202e681e070742c003107050002002c004031208000b009002c01070907285000e95654880b0f090360440100c1c0c0000120020b00741d1840034042100000040881080015074031420240001c2503075244005841c0304070403c00100d9114081c80710b00381d03450342c00c02200500101420001d00810f42180e10034012004500c0100b6989000402d0b1001c13620000c006049020014101903617032401c1c61415014420403034101381c00212070394013131700e202680d42d500007031084402000 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 986078723 1250 986077473 986077489
    0x307060c021e0721063b070902030403050c150f01060f0f180801060b0415020d14091c03020f0712210e06030108331b0c070603020309061e28060b0702 66
    0x18240310041c00c6c41c072111440303501007420720880d40d02030740068072965503040a50702441040c019600354040d005091256042d060689401400c1903118010941c0c2c031148181ca401103102c26442c00b0419851000c85445e100e1540015504ea001c900b54554542d41e04525080d16400d40196540ca103002c40c090100208001e812070661410303100925072a0b0031803c000d05402409101c26a0401d00003d00b8001c0b0b4449110911010702ca010f4080c02d04082424002d4988040d207101c203c0074090440000b586110b034031410000da9401c40c09410765841c80c113201d1503980621a100c201407210031301c0c00001958418014600a0952030b010b040e02e040e800f81c110b204034421042c80546c3c1150744241c40c01100070500c5e415400141c0c13501550100307240c11030f41c5119000d03200e40081c0c64440c00e20082040c0da40354020f54011004041140c803107841c2c10701d40104507000e40113501e60311a85070740003c61035000c1880890000034441001012024cc405001082c0c0780703a50010b0083c0c50300060f0a100f1818040c41c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 986079973 1250 986078723 986078801
    0x1303032007200a0b13180b120f0c01120f0504030f08060405010b03040b130519020405060d080f2809290d0f0e0307060c021e072106 58
    0x40341d00003468000040c403100502e015004a410012403a0403142c0c0028801c3c030090642c41002c4841b40c03800c40080c2c806461f01c0a515402107500715840140e84a0004010b900045d0882c068020144000f00458052242d545510b403401e48406038042c1014092240c00e0045000380d403119440408102e0240c107550000c0d154a01451602c0c1c010017011881c030301601c0e0000c0d8440040728154841460607407068060380b0016009008030f83c036000c480300034140e40c1c3da5034620a6405001c40d544200800048581c602d101920409040200e0100c800039100100500c003000d021902c202c00d8124000c86601d1400c1c010680407030860382c014070420179881c0b1102c05107149607001041e08030003021071203414054640d603009155100d07400034120f8110343d08100e0480720b0400c1182c3c2c80b1445402d004001c1c203031000389100076000705001d0707240c01c107a80f032200d1101e030850f10003c0c01110720b0141280e41610000c0d510050b01c18440402100146040c06200910a509015040c1e4540052070346150201152 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 986081223 1250 986079973 986080013
    0xe0c0a0b0313020609060706141e06030a0303181e060b03030702010905120102070b09060709120c030b04030905040e0601150f09140a0e0c120703020c061303032007 72
    0x110800140300c0121440780410b0358141c60803038a4044100c003041c0280105100103010a080910000d8a92564a080e5104e0707034100e1300e4640c110751694440c12080500b40d0706a07130140c03c40200400400e009030000c0c604c1c05100b040c0e5600d070484c0c41d22000d40c3c281741604800d0454909404002c00d21250340501c803007480044014504d8401035500103020020284a01801070030b201048011508080d415911119042034104003e46805c5510644607a0308072142d02c00f04e200b42d800401c82000d5804411982c541c4180c0c11440346086407a2981202e6008100703e080052244e0081425140c41c000e050400444000510040d410700000910b4842280e14003000c02c400c5216079000e460b4844003240856044c007024401c411082c00100701140341e00d8104540c4480301d4024071401301c0201e03000341a1100101041c500e15203402004509a00c1036100f422600d0340250046089507000043c0100010712a0500041082e82d90006203540e01802c1d5405d620300d40003017000018003405e9200086802242 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 986082473 1250 986081223 986081227
    0x140a0606050418020909010e0d030e0708030301050108132d06050705092209020414010311040b060a121e06060e2713020619170f1503030d0e0c0a0b 65
    0xa8050843c9154a07100041c0c031031012000800d850303180070341c032913102d852418065a050100c4ca0300d0190190811304203910061040810015500c8004002e40e416904140d440d05000d84030f90030488400c0c0501c1070292440090501c1e41e284e00c4030700300030946182a0721303034000082c0106410a982200d50081c440024040c080040912540d00c0150a01d9420354444030080c1e04282d25801031b009000b00480250000e14140e481040c510040ca4042c1c102d911400311240383c2207081c0140419190104941a0031150501807158414012000b600c01e805042600180003198020400c68001d0400104040d0b1581d68130103002e00d580c0101c81524581040e141c04890754000043c0c0b200d002144210b040b00302c070326a07012580c0b41020310b5030070540300d0f0001c0903d5101e811070700c041c902d18103420781c6000201d0880c101d0b00c41340f00b5034008540d00c00c5596031982c4841e40d03141000124202920751110b5410b000402c1104030500003807041c03850015492005002859028003440480c0207130380c02111034080e00f = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 986083723 1250 986082473 986082491
    0x305010519031124030a0504050609010902010c060b1c140c150d11160302030a090920092701030201032405010507080d0e012f12040c03140a06060504 66
    0x14080021070f0b01c401e89105a02c03030760740b0041c0c0501303690682c2c0c5648850800024048012010340006004501402c1641c8903919000000c0d0308a13141480000d000c203c00d4080240403560f00e60091034404009002d481c4520090103004240c03a050354001c441c800003820020030494410400100320020985543e040385181402c84c1d5502e00131008107001090320b03410540c1600356042c040d94000e44070582c007000a12664600a500d0741c01582c8110002204900f0015040002c2e0041622401c1290407180032070450041001081d8048442650840380b20f84011014501c482c1a41228000380c0262410950440c4001030a41e210020040006061200e0344070041080c0106802140c109080081c1c0d185074501e00a04140500e0706004400b1345054100c000000c01900705d41e2030040c41c00c02402c041c1e80b0b2010380150300300110030b041014150600805403141c1080800303a4006000d2030291440c030b83d403980c505002103840c1204071b003250890b0718030508111250252801406c0c003203909101c1b01ca8 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 986084973 1250 986083723 986083733
    0x60f0b0402090a15111005040317130308090c031227090703020c150a05090c060f04090e1e031305040c05030c03060d0c0f050a0905060a050d150c030501051903 70
    0x84280a0525030441040300211428024170b00302c540403030f424044d141100c00d9010300e14020101118150302050101080144800e07041c0302c002d2042865a0300901075441d141c904072404000240392850324450700c513050005a80400601c0d9520315121202540c413104103c03a14a410050a60340452100742000017480d5070381c00281d26484070b0700e45801a15000120303007040c60115404141c2442c0880e070710074041c00c140e06400040c1309201e031100301d0300340e189480140000340c4250300486014a100f4402407007140696000900141c82510803a0420b00c02c8190380e00382d080d03a000f142c0005070f00c0000c040d0380411104a0000050108071820041034210420152003071000a01072850040000002100340e665400c142524642004084100546440241280c04810300440744114043c10380040c04605034000e1a02c0fa203400303041c19034034a262000b2300281d09148001250305070604021000c2d0404640325a01030769146a03004662035142400f445401200a803501d0314450300c0030800c0c80031074 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 986086223 1250 986084973 986084989
    0x81603020c040507090e0c040e100303020d080c0a0c17030c190906050a0f1704200d1205070c0b0a0302130503061b0c03040512060711060106090b030a020d09060f0b040209 75
    0x28100c100c00721480d94074406080024801c5401a486151441c00ad0080340245510b40c102680e20036001c5070714003a030400c025100c2d50000c9810900c10b060400c00309403d940301d54070b5490210300c030701e01500f00c181003805c8107110740d00300315030b000ca11100102d02000300c0140d158030703c6094007080c18200846c9051450040aa1040c80c0540d0306001010313079148010b620512206c400348a9025410203241094903240c0c03e03c0940f43c210898002c083c9c0d030b00054624140c0d0500d8117090380800310301c003a141d8402094900e9003100340d06031803c1d003c0540001d07020a40100414425083c1c0d50010b07600c16800031001200080d54111354000c0e0310031805c11240d103642c9140e078018000902d05658440100d4a151880c602c9a078000c0e6030048400300c000c03204848001800c900a096580b10310242c00860900280d58400034824000040c161890800402c6545801190051864003002d85458080074000c002e4821641d82180c03903940c0c980100b607002115200343d08554201b00e405604d0320740c011001813050 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 986087473 1250 986086223 986086229
    0x105041203050a050c010e21090603180114070305060108011211090c041206050402130509060f040503040512030a090602030c1002090a0f0b12060a030b22081603020c04050709 77
    0x10080000b401d8a6084c00f503000d0716000c5244a0083c0200c40307104141c0303600d84078a10081103060b840840096080480e010039561004800343c400750841d5a450f0070344074010304601c01c1c3e102c02e541c0d481c1d9030b44400051480d0303076100b0009500e0100311800c0040005200305416070182094140c01d070300800000f425848a00e600c1700c011650342a654a404082140d94400d90303000e030201d03207107145030f103800c00c6030341c0d00300600c118002c483d44000c203803840d010754064400c11501d040503a0003110020b0f4101560203181c503002401101260305140d1100080380b9051030302030050685910100301044415030049611000e4042031024604200100090307035a9855607681c0d04400c5a004949038050703407140c20103034000345012400c640d605907458030031007020fa0102c10100d040c0a1110001b4440381080802c00d01200e0384104105541e2f514080080f42c0c00ca107465204a035106a00000d5020039013000151107115444440000076121901d0f010b803418441501d800c2c007807410881040314440d0801400011 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 986088723 1250 986087473 986087477
    0x307030903121403100801050c07020a03030c0f0203100e011506020d0c02012607020d08091203061903030806040f090515070207120602180f130b0402040801021c0b0105041203 77
    0x11400e100107003964883c00040b0201c049070008010070150742a511150340c225414000200140d0b12421280502481448006074000e1074042c0e0810010740704906244500d1701860307815030001c0711507000030304051840802940c25512000141c0034200d0a200b8516014004419040d01516044029484502c101c030030800340419500c1510569009a100e9084074084229403811003019144000b190442604c151005220b034402e8a4034003406941ea250140e0301d04c800401046100d0325000203503038002808141c01c00c1c2e4082c02c10b58928014046c08010b14841c2c0c0b41c06010b0318101c4107000031038000e402610355036410851200b012800218800c004c0a031124030480d15035641c600705074a4000c280d840411800800e8800100f44440741c2d0140824021280402040d035448808102210003128581b5078001b882541c2c41c080e2040c160f2141034941d41c040c10150410f559484d034182260404501481c0c0f04c00c0c2140c0c208284a101d1141003880c0c1800d00f45141014249207500403031003180040102 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 986089973 1250 986088723 986088743
    0x130518090c27010e16020d09050409080408060a090201031a090609060427050601060e01051b1c03061a19080601031407030207210c0b0604020d060e0114030307030903 73
    0x120018441d901c01e000c00200c50b2400344036594440c0c02e0105404101e03591080f10500002441c1c64a101190500b6900d215540c0e414016003406c00300f0000b001826400c03600200d00b0040020705038000e0141502c198154440000d032000c41c1d000141c1614100081c2d950358500711004134005a0340c0002e4160000010f540b040200d5440034007007002401c1e0b9074114000210704c03034200d0034070701d282d070503080c0003148101e060300c15a036a662002d031048144001d080b404110f06104006400500b1440d4490001c2c1281c110380c04980121140c022416604440d0800661683c00601c02c0301401d10002d0b552070340e00d50800d03280c640416070708061040f403604160304010321400403a20a80c860f402003100c0c8440c039007480138139080503000900250311030407086a0f5100400385084885411805040044000c2e8840c00400c013a6aa19038008040080c042c5920a0b400c4c020881c802000d8826000a0300055142880650501c80510074400b4603142e620303c0399100f000030a00080d40503c0c0721040302d504c882e40c15 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 986091223 1250 986089973 986089999
    0x31f02040902070b1e0411100306031202030406020f0d0903021e1c06051008030f0f1e0a09080109020a3003020c010f142d130518090c 59
    0x40060311032940480503040c0085211020b0100082c48680034502d01d11802e0001041d0f40d484e00c0c1030700000c0b1000361640712041001e0b02141020301400218904501e400121242c41e562004035031014000241d005900202d8180319603a01004036460358034003400240303410a12054000c11030760407030100034081c00440d44149990514013860306128000240b18040004003e005802e9407500c2d6641070301c100d403c0002040c00c0c03880f241000400d5410074400b03145132011040c11300300b01b40c0c4a4110000d407401e0400c4441044000b00209130400031301041c150faa070340c115050003003441800d034000cad0180380d01d80307482d940c01a43c0c2d00c564a4201c80b901107000d0b0340c1c2000391210b4058900340d044608104000c4049400c20540d0204e203450410009888410600c2603040049506180d00c080050390144200151400d6030701c1da0404d10a9608121004c0040743c411301d240640785d40100c004480803560307012050210b0320781050030320607114400d82a201c0c00d140450105581e8005032086030b000c0c1c12851040 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 986092473 1250 986091223 986091283
    0x71103270102150a051b1315020f060f0a060b040e0115050c0109210906050f1615140703090f030c0501060f030b06090105100906180f0905070206090c03 67
    0x18100003100340043c3c198034085624401402044440021a40300040141d200744801c3c0b0a03a15100c5105420b00f02c002e003882c6a070a524911016a002907204a00096404003000c2041e10f124107844001161340382060781d180004c1d140203030800844090140000d00c2400740c41c003180c0b81119100c03241a011079141600a94240c454001600e200b0750a050601c02804032140c4c05103090f50103100e4031805039030000d1088a42d40501e020f20340000381c0c10003124013450078a002030000003880103149102d20360b00355940407a0790041e28464000c80e84030b0b187c500c400e0f0700c0c000c00340e540500681070511242000307580c0c6440340c8241034002018001c03002da1407402e11071700354820409028903500144055490703052000c21032004a03040391098032840004212820401650f05500003180c0700c02c0c600ca42407081c262022503c1c07200c000f1541a04c10380000300481d15800c100001c0c000c0d000d0010f00307418149402801c199004010100c194480750302d4050540380050449500c60855002090f456448601 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 986093723 1250 986092473 986092483
    0x20a0305030a02042409091505060c0c030316030206010801060e04020d0606050603070e0406050402070b01211506090e0c0a1e050612190e030409020c010b030d0305071103270102 78
    0x4000030224841c060010079050f8441000081c4003070303c030517941640d501c2c0726034141c5181c04080e9230100c0b10b5520400ca02d0900c00090604003070560280e400164030600880d1464000c058840a5030782c10038040004d041d0103200140c05440c80f0350003400201c1c00e2650a080b0048082e0000f03000d945030450200600070598010070140c04001c080340e9070390804440013884500340d051301922403480c0410002e040d02d05442118201c0750310254507482a071030310303440f011a111907680300fa90b41009842d03440f000a8010300c5000c00904551400543e1605201d0b0a40c101c0e0650848540564009130b140c2d0741a03a03c200c1d101d01215014914241920b41e40914481d446a0720b40c041e81d0829004030f641700702c9148107551140b0a074032500d00d0103044400c0420f160251802420f80300f1841c3c04c10441480000a1742d0001c0042c051a01c002041c84147e00c0702092071f01408002c0c142c006607841041c00f5403145e0000c80d804142c41c20f0b9000b18184034003001c01ca40e18001e000c02503000780c1214079201e41264002c2c0b00e = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 986094973 1250 986093723 986093729
    0x22022101050106050c070806251205010b0304060b06070510022a0d02012012070e09040b070806030c03060a090c0b0304140106050a1508071803150b03030301030201020a0305030a0204 80
    0x78400c030750391032401a080d9002400c0702681c500800501082030380c000110f0a01c00d0510891980300140d100c000a03281002c100c0411007007220306201e4040807074039401024002c000260300c00d07030340385080e0910300100e555100b000344c41780300104403580214074002140050565481c10050b511207150101031459031b03070303100901c010385070002c54101d00e1080841c0a410140d91600240700c10306e411042400310750b010310b004045e54081801748201d0200550503030751f40308080703080100350f4119035800200300550031282107664403602c0c000c20000d1036120f9055a00068180e000740740d040c0705080029240d503030007003444121555a43e0300b81d081c400d500c1005002444800b8a451740c0c6d007414180310700000610221181e280d82031010020782070a000d0711031403c0f00c0c4480c030b54030022440000201d9010310042d20280411150580181d803440d018202000110301c1200007800e804081960740f020b444100d42000d200c1d400034001000540d03004207401544540c5850320680c0c0c0c4d40c0d1180b01a009000f290 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 986096223 1250 986094973 986095039
    0xa060b030f070815040f02120a0e03041716151e12020904022808011d010b0a030b040c03090b1b07030503131a040506090d020304180f051302092202 65
    0x101c510381003046c0c00e5000380b40c3d81c03c02010300510b42c1d40310095407087d5810650840703826401003004010040902200003c0b5880d003000350303074082207428104000c2038000e820903034045000040d054a86038000382400d81804204c54061602007100c00041c02415030f1114a840c2c03160000f40009513170382c8a5040f281d0301c4144071601c002c080c0f03940c4071032005010560008408034000e0400800c0c007113102c1038034072401050503d650b0060781c05c01c0310751a031642240c0005805e250710f804007031800360785070300585075003440566000603d51190b05200d450000064041942c04038001061802105204126500d61b509400c01c030381c4e00c1e1111a5542c15403254542c001c1c00517071007030360003040a00e10306001c03500690180003259015192484a01e464640640546000d070f0700030803003004004d180107595040d4400d0050002143c481c000302a01c207032442110f0310381d5510251440c01085291038030f202604045e80304640301c184000c4645c0484000c1d04441d0291003000120038641c440c00566842d030b8412005a = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 986097473 1250 986096223 986096231
    0x10507080c0601060801030219050f1318050d091703190203220e0903180f18040515100f120606090f20120c090a0b120a060b030f07081504 61
    0xf1380c6000301404002c0c0402c03803048011100070403601c1220b10010040d210009e01c02c610442c0c040080100c202603e80b01202c0840c0c8882910022104599444000cac1c1d00480103094100303110030008040708055000b158001031b50f14070121400d4800030542d4140c0000c50421805c807101c8010a0f8698040c0f400704a83c2078249600030040f40001880010448022405041051715007640b17640e00c038000c07040c46061144459015080c549070100803040405805060550782105081200213501c07012a41558603920205607403013550310810041d0303809410344a4100101c4e040144070300443d8020f101d150b0084005441d00e405028103035002900078165440c08003c510006503444014040030750040c070542c507940026070060f1841d1000c4034060402c0340217007006031f44c1d09007002d020798222040854101d44000c030b0108030400d6040081020341d8490120304060710742541e0607019580e168000c821606070034401c0c4070345d0f08072b0780403010341203c1c1c0d50825110641d40c084a048045840c030040e16406410 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 986098723 1250 986097473 986097479
    0x60e0a061a0a0e040b01092d051504090b130216020a140307060c060209091e07020111090d030e04060b0912060108030319060302151902010e0606010507080c0601 71
    0x4503800442200c07038080d071900d5034024038180e095a0307001d158180d0010403003803075441070685402e91095101c280e050624640c05a01ca000c5070b020341c2c489000030045000c0741c500002003401d031550f102c1d00500381120074640d05400e007400800c15000380c0c0705098a00e502c441700e1034010790710426007080b0300b145100219202d000303041e0300040032154940c1c140d000c1c5d2843c120110b2904015141c01c90116000b40003040c406240100c103c1e01805881416034100e5400d00c4145c500d0340c0c0300702045026a008401c01c0000c00d85034409001400401b170891019a0702d0f10105202031603442013a51641e890840c0c42c026800343c43d060030b6890303000c403082c0d075a4440c0c83c101d004070314103000070042c04980f0020380311034200c0c2a82c582d202e680d6920a0040c0100369009200080e01c03001c983c5400041042c41002c00b040c5103680781e01040d000310140c906e00030720340e102044164621442501c42d21121000748024801d101903500000c1c1c9400300a40b400d4100140000c05000303100e0b101040701e4419030a1402c6075100d40e5 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 986099973 1250 986098723 986098741
    0x509281a011412070506130315020307020f03130509090f010615140702030a0803041703010303030506090903090a0b0f040b0f03090c0910060c0c260f160b0d060e 71
    0xe090040c10524850411400c01c5800c021a080301d00c0064040100a1641000c0400959821420a660040e107040c003001c000910180c410214411a80c0c50258490401b6a800f9040c11607010b0030021a50061003504a0307040c0c4c0002003c00c44009031007900702c585070540307010300700201e00090204642c20705800191040036080e010001401c190b459500c19035000e803029607140310b083c1001e507040c0e001d20f8071280030071850350055404c0762140154050800f500c0030541c4868000768801d9011907694002c008403400c10440d115444609200038618040c42040043c44880b214081d41000c10307808640312600b00007900854015000014800d07480d40c103180384420203a8400c4510030818051005126000c0c101030740301c940141c0d07442c03079001c4c40701e0302305207044035101c10404003034035204620b142c00580c0103440c40c01c0c505003401c134044c00e07481e80e01c504007818034014840c408503400740d11100c0a521800c0e0030a02810a848100a01c2c5a5650b42d80c0c010320b0140100d41c00600c03a1803110020b01120345 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 986101223 1250 986099973 986100023
    0x70c021c0b07200a0302061b0c070b030103050d080405150c0912011e090510020d0b0a08160509090c0405100312020604143705060a0609050109050928 66
    0x1040500d00200c01459069029261205128000c0150b400880807e104080200e41301007a00c3c91240c00f01d0034409035002c1309207403112b0b0740e010b620f06020000050050100c00d1014140010140c00d100700036080c9070703450070f507100b1340000d12480c003030100800300d003e540500e8115030f141d107001444280503280514129000b090034080c52100242d40c04d81c07444010b6001c0c0101c4100c1c7e900400940b0030704082c0c82c821806544200490140d95a860340f018100e565081d402d64003809240d03000341142c000c811030840c5040090b07040740f031240b110001000080200040c0358280703c002901d01140546404121203203080c06a080108010340052004003103950024080d03100e04d005250411900c030300c002d08941c031101032028441d425000c001c08031181c050451880390401400c0c0f00b4501d9450740580300c1c64203141064a005040541b6110204129001400b65a0140c0708846080040341482e41c0b4a42d078800707141040500780401403441c002000c00407082c546203240c1083c101a28140d030308003948410 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 986102473 1250 986101223 986101247
    0x106090303171521061605090d05070e01150809010e03040519030c0b1c050106080402010806180f0a060b180904080f03040302030307030e150402091503070824070c021c0b07 76
    0x20341709240000c0c00140000004c4a1904c4c201d854051500c9016005d08c045060000c106903414801c0301d000007034421909000c94002e15224107048959104040000c082c0e07207010b09012042e0703061545c0320140e5517001c401c450440c0c2e81211001e10188540c0c4100356103e210742e201070003141d05040e000541d0250400100401c000503600403011b0032907901b04604444003801108005889040000d0065004000b0036401c20001443d14410031200c100e10340707100342e013218840140d100351404e022109107203002d103c0103000e840c407846041000c01c0009442c291008030b0410721940220300400c0c10b200ba0070003151903003a40326112642c0ea20309802c000e5500d610550300480003034a000300135181d80d030340441c0f80602454040600c4c8050344950302008040107000c1d2102c0103181e407401c015011b580e01006503100802032040030f07103e151003880d400c2040410700200e01d20260251001c0106a81e802441c0030750055044550f41040e5407080078ae1034030401601001042450f542c010300440c1c980099040c086 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 986103723 1250 986102473 986102539
    0xc0d05070e1810050606190c02030d050c1009030903020d030c0b06040216030f030f0c0e0907170a090303020d11090a09020a1202030a090503040b0a0801060903031715 73
    0x341c484440c0c180b80c80003071030b44031040ca400101505002603480d41090707811540043c021814400700b1884c2520004000460700007041480b4102001c42c00d091103100c10780c0002c4c0c02c1103030074420800b07050754403070a6072520703e030407660b56500410030940218041c0001d150013421000c0c101c20140b0300078000c01e02031001502c98101000000f401843e01e0300803281d000500f0b403541002d41d10f19a40c10340760b02ca5010950001c1c9611030320000702c003465a22441140c214107a48202405140c10148814030502070030080406c802c48000c400c4d01710030708e041c49400080084000402000b1810120024050b48024440300340c101b403001035020154202070000070908032005001c5650740ca8841d012031103410240004034164540076a500185503020315840045030760080f9118076107988080c00c580c0150450441c2c181c0c04507a0755140c80c0c0c000300c01c80c05441c81e030a00850040c00c503200900035400003050310407a07422000005081e00889000907040403800351002e10380d0551200302c3c2a4000c040d0b410f00003 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 986104973 1250 986103723 986103749
    0x90f010905060a11130e0601111009031202041a070f05030a1d2202070807080c01094d030d050c010b27090a120503010e0906091203090c0d0507 63
    0x18903103401d20102c031580040c58140785807030742c5003600075860400000d0080341131065001550690000500405a003a8405600001c81c070580307190140140450f41c3c000060143b0510052110901d0408403600324042d480b00311384ca41c0c24520785214200d01c0f46800a14038000460303d125400d4012081880c44200c1c010300038424444101446885688400c6041c902803840c2c0c4004540041d650050501c24003031201e080c54043c958a8559403640b000c0d10410f6540e40d60140c8100340036910000f9190070040046002001c0c01d80c903030954581045c011801e9503501c864401c0e00e1000c2141d40c03901c0c802c2c10043d080d240c00714035031800a0300301d822000c402807007542030405c08605441c0c0100d07104020060458144186401c201d004c0b02d40542c0184007070000c0c400d00c0f03c88404228480c0c101845214250758032560fa42c18001a0703141e0400c0900006000ea2261052040e01c420129420240280c004001c81d200c1d90749000a528084180e0001500400c2034082c91092200c08556101911810380f0181 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 986106223 1250 986104973 986104991
    0x9060c1c090b1e0c10060810051303020a03030513021e01110708100f02040803071b141e0102070f0605040e07140a05071113050709090e15090f010905060a 68
    0xb45003032150954145000d52a040c00c0e499218542000c0d00ca101c02e18000c0344c545800307444d444001c0b101c0581108003035911050f44c14581d820309006080e445100c10b031420310b20b0b43c6550342c007070358403408035200074141502e4000144880d40751100c1d07001302e01d4000303007000ca0015135080c002e54040400c214043c0099103e0000410326003000900744221104000200605c107401a2200014280e0081220b90581c007040001032010041015000b054080d941c0c04110b00c4964a03403500106a507404150120004613441000c2d541d262001c01c0610702c04c1d0251482012310100403401c0014070340069411884011000c10000d600030060f105441c449a0001400d880e41c820542e84408020507107080c400e400c01100000320301c940c01030a0024811001080c06040010014916a1340b0034241c8219a54440800068503031002c2c503c0d0040040d07410030481c20b40a0b40c9101d88400c607012400c0c01d48640c48021a003c0e00c01001340700e2a4013031910007082050500e01d007003038581ca000c1d030f100d500d050306040c144 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 986107473 1250 986106223 986106239
    0x602070b09010f06051503040c0801050c04090b0a050109090b0307052701080610030305070c0b0d09210909020901021f0209090c0918090309030703050d0210090b070509060c1c09 78
    0x484c01d403403000b095503582c404002900741040e0b10051080300c601d12080c100080d1071409000381c0c0e000398400c81c283c54440342000c00000c02c480d44400d5161042600c40c50821580c0d800c4103402c4103940c0c0c1c5d03144c0400c0c2c0c06a9807010030f02c2c1c080d4a503c07994101c40d80f41d802d4240030100c02c100c0c0c0c1540480c0020300301c4690341e803c42d070341d0354a205849005440410013410000a40950024142c05106c2c03007104140302d40d031f541c550b50282c00c070301d03030303240040c2d4580e41d20004100410341d04444d1119408035a8025480132900241501c0e441c1c020f40340000e40c005107450581c0e00070404034806010310300ca016141442d00c580070020350020850240102d403c400410030100c2100c040d200401c0d0060303c00d2840d0580c070340342031700c50103405468450140000c0202c0906a00c0c14850200a940564002c041845c4082802807502034030040d004480c6250030001c10009480900342c1e81c0015041c5400303600d821403a4006141403240c98005000c901c0303545252601c4113040c140c0312050034025214040c10f00c2d5034400c4 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 986108723 1250 986107473 986107481
    0x1090606030f2c0a06050106050d060e0f1504060806040818090c0a0f09050d0b040c12030c14070e0906060a0b03450610060207120308070c0602070b09010f 68
    0x6080550301964039010742d07070000d00301043e4185180104541c140d2916031903490458000307801080000da00041c02c90001d8056010707650040c030300f0030105155480d040440d4140702d078020f443c840c4150030008100030550b03519001000541001c106950182c1031510344044142c0c01240d017054100100340c04480e051501d4912184603000c100390051611421070000c50b034207440700040300144601c90300046515140d480040707a0b43c5106808224a6041504041c2a102d85680c44203821807180c84114000903401446444610b0740582c00c80301075a600a0041e061202a4014203402c003800c1041007200707400017500d139002d000e0070ba61008506464102000c45440101d9400c400c103880b40e0000c0701391045400b920f03400c1106031184d11100ca001c0340c0e00980c0c40340d841204109540e00c9802808050b140804400004040e41c1c001055868500b002e0a09240d4404501034284494940000c41c480d000350250100194446821991645546000d4003501c6041c0e500c0700c41c540c60b03c40d12074002d00035482 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 986109973 1250 986108723 986108741
    0x30c0301061d0a110409020a0908070f0b13080a051014010509130203070e10080105060d33020d050412080f011403010b040603031e300b0901090606030f 67
    0x21224042c400d03020141555034020744042d03581507070f0300030340c030341504a0001500c003620a8002c00f690b11404140020603040003500b0010071604600c404000107200c07080f0020480f48448442c0c1d48410017812029241496a8082d04560052280f80001c010340410443d03020f40710794000b00200300f5441c0700c8a00005003400340700d800c00c02c802c0c0411404204003c000000e94801011100d070503444418080800e01c3c00c0e2621080e0040008090000038400c0c0941036100b0b00c180c0f41c1c9031280809442c1d01c082001041034078840500c020150240b000c10791220301c10344c02c074200e0b010b543d0f4000030322040e0020701e001c80c1e040e108044107841c203050480c81426135900807400c04940700026401e04465046801510000c9603140d96603d03031002d01508d43d0b0191100950094031149200b0601e800b91340441c1c84650800020081d1104200380c40c01d80e0080c690710107012442c591850b180031b2140e00c100601181d00e03c10b07800000903000103548203207a00901d096602d295002c1c49030465523008c40040e641402 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 986111223 1250 986109973 986109989
    0x309030717010f0903050d0b04090f02040b1804210806011421040b0603010c0c0305181201050a0c020c063c1201030b180a02010c05100c0905030c030106 67
    0x44410008103001c074503200c0e0a04440000010440042c0401c602180e00c4290202c0218401103007200340c5418500c2081d084c401c00780d41c02c0c4981d0f1015030341c03101501c00a501c001d1240380d072100b00700d0b1661940442504101e003074520000441c20141011015801c0b0940385001640e03076003881ea03d196100b0844580110010b03110f01855050b501c00400058001000411a101d0f42d21503d07240150407282041c01140105550a01c5040c907005140c01e41d480044500c0c244a10340b076140000036030203812944c0b21402041e0301c1c00401c0904c000103d17808204101200c1940c01c0a060040c00300e00c81c0c0c4040003495060302125141c56485017807004034080c2c0e070b6442d081031065402c0e061942880001540d103404898592560034600106045140c2c0c1041402107145800c010040c0100080e00300d00d42d030020382c0c010307440c0788869841c1081650303000866070007130402c651424944200030301081055140c809102080c808007030340000040555600d8032803240302e880303a00c580b407110381010b02c90781d420f840e200 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 986112473 1250 986111223 986111233
    0x1201080f211c0e0a03051b06331503070e190b09062203030215010b031612061403070902191107030209010b1209010b090109091104111b030903 63
    0x4600001c403a02a42002c01541603224400c03281c03544400e0150455083c0702e1b494040d100d02082c964520a9402c108003806580c1c4200140301b500c20700004942c16420b62048211612550a414400c980710003100c1d0540145e101c0c1d801d41e04100307405010b1403050115684540b9000d010200300300081c10450b8800300910356403402031084d04a040c0050130740d510b001e00202d203403058480c02280741d203101d00da50b541c0040c20b81106204140d03045c80510340b08030145100d90415418030700d12800c41e20010303069400010520051110050090f00f85454541d070000081165503543c20401c850200081401c034400e001d4482c000c02c1c050034600c20750304107200140526101110f0080d0544891000700c4801180b88240c090000060383c8105405018160300d140b80c1d61681896220031001600260041c1c00c2da9050500001964460100307040c111a40610041441c03aa02c1c24001680315416900b550003d0602050f41402440760f0b00078003200346864080704006058a00c52070703c0b8001c8604196241d000 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 986113723 1250 986112473 986112487
    0x140901031101050a030e07030501090309082107030e1525110f01050706090503040509090a0f03050d020d02030a09110d170a141612020708060f0c1201080f21 69
    0x8143d010346911541c0e8180068070b0350031034207094640222030380304031041c1c0e444903281020180e1140036030001340b01480013008045000320660791903098030782c0c01c00d40b010000b00f40318043c540b2900170b007200000d001d880720201e007002c1c02c11100c0951201240c0049601740b115003030300e810003181a2185054115002c0540e103982711080000715034841c040a8100b100612000001c98042c1c451400440d105030015552246032106111107458011300120140e001690100302140b0240c02c00340100d6858500a40c0e1754881c101114024010034041911451010003001401e141c0d5074402c0c8003035405400006401006441003000b00c1c4060100100030030f01002c00d40743c2000300b010240049401c603040c44050160b01e5101c4403456000b00e0244070041109180c80740074003100650041c9100030380e2000d485024200b00742550780b10005084100b42c1c9104400140340c8813192002d503003c15840c00c1c0004c0555a4502c945695424140c2c61408107000d10046c1000c421a000b00e0019110030b0600c07600c0c140a0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 986114973 1250 986113723 986113727
    0x60c03090306020f0f0a050309060c0a120c1b0b0f0a061809032a03081f060815060408070e0105030118031101090b160305091603020d03020c03010f0501140901031101 73
    0x4516881304132000340014201c0304c0c0020003900345c84440303907902130b100d18020408034600200584014005103007000b0414001c1c1e03201d0290035003d250240702151176584032000b11030907100340301040d404000400c00c1d80100400c4403243c3e4040c080b40c003403d00c915240c0c0b440308006c8611610030654921030051401020060a402c017110700ba00a042c10300700200c551741580c02e5200303000300006012070049180d00816030403120b07040d04130300c50401104131000302101182010556001d1603050001c0440000d06440603501841e0303030300e00701038130301501d5a948983c00ca03a100e07081e005119001c10800c00109050905118100c500c4013640c4105000050948007501c540102841980d0390f135480381c2d0100301043d0000c2c84c2c01c0c0601814040e0301c04821040000800f25540a422403590740c110903202c400c180466400c40f015a50103ca0408040c0d0352483c3c1030385424229a49643c26501b010004d000522556001034120369041c2004074483c2d03141002c2084950003408000c10b01818100d26080c554 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 986116223 1250 986114973 986114977
    0x110f07050d02010f090914091c0f0309050304080307050d200712060905010e0c03010f050105032d1f1d0d030e07030206042c0f06100e091e01060c0309030602 69
    0xc0139091000d65181c0752150b45d000ea03034480781e1405040111001344a84400100300c9031040110b0142d1219400d8100e11000340203400701c030000010940c9a101400500505000701d40003041278404880e41c0d0141450a941c540c50004210000304026242035421080140c2c507c0d51840303c070070041c264280c01c0041110410400c503800b50703880c9031346d010300e580021424420116503a00850052844503660401c05082d1074000c513100282e40e040500401c19502d00251807021694460494140311000b0b0b04402d0341a60303c1c015004140c0b00e41e000080f800e219810540703a4a495000d01030080404d488180c5420064080c034021051744403007c0c003600c0354420350001c0220400c0c0020350b10842d0790303600050031980060700040010030300a1940034206612900c60407450b18004202c0c40189460003c0c00c1d1391000c010143c0d405500c088140f0940c0b603200c0c8410201c0d6440040a8100c90b090521498448001500d034141030400f01600202e2000d00a403200741c8942e40c90f942e004505421035075907002039 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 986117473 1250 986116223 986116247
    0x15050c0408030d050402030105100302221407080912040e06010e0301061d0a0b1c03050f09090f0403021e0307021512040803040b0c04062a050607110f07050d0201 71
    0x1044188004215100d0602c0109440000b02c40d0105842c2411300402d0300b1a14041c149c800080c041c106c0400041c0c841400381044285101c80078291901c03070f048010301822000c0454600b80031100c0810403040e0b0003521841c024011207080720f130300184000c902c0c20701c0e01c10390103041110010880004e4040d8464002001581340c007800200300140e8960342c0307802400c44e01010341d000d01c659104000403406c451041d40c0b00f16508940c0048400504840c01e10b5080b50341c00050100000000d00781003a0600000f1103c2513080a4030036605407901d0340c400448110240c80460050241c400088022900d4151015050200801039450000b1950800c0302598203450805d40030f0906020510380c9021703c204040c070a5028080855880c0380038034001b1884c0340000c24803200c14405100071702a55a2120b10106804983d1000c0b0740d100220340b29001c400d1286400080280c4940700800100b10b5024030301c546201c0d4140100c9900b1a40514856161103140c029160815401c0340220050b6100703107944400 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 986118723 1250 986117473 986117491
    0x90c030c3b10090f0c030f02040e060621010b03090c09060a142d0a08030304080406080613110c07061e0f170901291f02030f16050d0801031505 63
    0x201643c0e80196001d0390600a2060390301e0356140b1103030090a0b058051001801c0c0382000451400c2c0c00d00d01040040c80014281c5405184040307001409120b100e40003d4440300304903e000b0b403071341c1e507008909101c1e8011110354680c3c2c0151010095107045c0350002d140501c0000f070008c2019810107000000000100b40d8040c3d0107040c42c1c40c41141c1c2071660340204d00000c2840302031005840041e042c44030342d4945034400c100e00d42c400c004100108035214162401d5071600d1030600c41070307260034000070680050041802503907844c00c980032840d00b640c04002d103610402c0350191403649541d9281136484111118a5184c89849003400040c403e1240014100c000d603d4208540c048020300c1546607981c50884138040c1c80d030340d0341210f5082800c128000c0480f55038189000f40b8966100300c08201e24055510b506200300c6a1054020941402442a201348c9102003c0442d00c482e00340383d0301d00710341c11070b00300588180c016420301c40d241034412000c05042c0c83e0410946804804810600e000a100003014455 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 986119973 1250 986118723 986118751
    0x3100506011407050c0108060d03140901090503030a080a051006091205160b03070201050c09010522051c060e06071b0611041502010b061318090c030c3b 67
    0x41980e02c020140000a00030740040028080c800c0002d0310b15000980220322074420481000c001940c0b01ca085e89418142000c1240c5401648006840440350303508495898000812001415035020007d5440340480c00e8040c0910f0301c80e10323641d070300003501f82c0501070000e103200030305011000140c804a00704a12440440b6010303802100645100142d40d085041401000820320500c2a424003a090b0010301088030075262006040001c0c0003440345032840307028046d621000503d07017100b40351200024a0046c0980030380801c03030032040c0395401200c002129401c3c9070401c1c007501448001074051240704152211490588400f040b828044a40141200e0329a210040c0c5801d904051000e44000e02070200400450400c001000e805d4400c9008000c0c0280014850030750300d8400b4803108000c403207905605200ca000c280d00b50701d01074590014040c011441c8510000104240c4445a4048543c00010844080340e800d000d400020058010307c1090030080c8082c0c00010400030042d5000440240343c44 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 986121223 1250 986119973 986119997
    0x8060a14100806060919030501320702070e070207170a050c091b0a110105090c010e1302041e0f0812040e090a2f0f0904111c06050403030f02090310050601 68
    0x81e561b100300001e00403990400780c8082080080c240228000340f0000d0301c00e40e51004012071249c0b01318a0100044100400d50408904031500a101940107004030100102440c0b0f003012000c3d503900a24070461000180c2d811390074082200205d0341c4000070340d03c00083c2c00c0c2444903104000c240c83c0050040384900d11580300c20141000f02c94020196480280c862850803002039203940e0071941e004001e0581c50300302c0240c10015a07170059106070410b008941c841ca50b5905940302c9030003030081d42c10601480c00c0c9290380803004090040c068040314000c07505103180548a0b20802d4540380350b420b140c1e503603150500050203883c8000c41d490381d000d14104116007a018443c2c490310020f80915000304050401e984005582d4840801e108001510035102890910b1143c0003007100d840c8010b0000e01111000445e89940d6914815000e0b62103084507610003401005040000007444180e404030042440c107844a508145c042c000d9504c003c41c0140030709144a811600ca902070540102100c5c10400000514 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 986122473 1250 986121223 986121229
    0x40b0a030e030d0c0804060e1908031009061e21020f1521060d0206031311090a0606080f2203020102130b0d0501050118090b011e08060a141008060609 66
    0x201000303113031340d41d18000641401c1c18841d08a5141d0301c80d0302500d400189148149080790b0030a15090340e480b00d1420303665594454030103000c00043d082200e05609103000010780f001665134062000c40c400d07061a82451743c0e00070035004040c90083d0142c5420321400c010b0050324001d91307206441d40c400b602c40000031140d24110416a480303440c09100040789039141c00240c0580d0842c00d90300140540d02c2c440001b84030b40024441c5c1c08020247d0a00c0511041c01d081000812801c401c0c0c1104058808002402c24510039400742c01d850240310000713001d107000070b01100104000c0da8002c140d05a00d8044582d240c000b10202e04410050079800d640d001c00c6403000095401c0c1150006210200c111501c85290640030010f403501a802241084605d4086072980340d1100c1d030322011101310140000740154800010781c1c0e840824810200701800300c0d403130b80245031707005290305209103412a10b000000d41c541c821105a00c0e80800c6180d00003019a80d001d00c82401256819000000240700c40e0810b6401000 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 986123723 1250 986122473 986122481
    0x5060c1e0408030c01060503010b15130305010c0c200a060c0314030a14060f09060d11040507080906091501062102310812092d0f010302040b0a030e030d 67
    0x3010803550f00c006140c5480240c00e00c1000080c4c08110001d00610700d0f00000a07401481000f17000d078081a00007203200c1c0c0e40d11201c2c07100004544c09402400810307201d03140a8002558004c040e111040001c0394030450805040300201c0394803000741168225818401d003160781890b1968110144407100c01051441c4d42039402447c8078050100d004242c1c200791081614410790f015000901444406202c08400d60700c1c40b0761a41d01110a5071101c2c030b103060a003003155034100d8103852250031a242c5010301a90950004009108603000b004589003500c94034061945ca00451425004e042103c600510505114080c0295000d00c190b002c000780c0106211510708a03840350103102c09142240c102c6450326820581200507800c07081224030242e9290225090301c2c0c0a440c44001811007001a03080c095945428504241c9081c00c0c0d8054280714058075440218002d02d0421446110010f00580480d8800d008581c10340c0c40c1c240f205403d00348900c1c0c0c00e401412042e10070ba1914041400011130f02946885 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 986124973 1250 986123723 986123729
    0x10b030618250e060405011103070606032105070f0204020a030b03061614070c0b031b120106030e010c05040e131401020a090f3606030311010c02010905060c1e04 71
    0x8140081c0d481d110b05400c0c0c21190b4003a040c1c09108900f00710041d43d549203c01d0f50112a07080c28819504001400410304503c15101d00070000c0d4a00b11703002c014050060844400340406070800c440d48020340301c00360b949006421008000301b2904c0b9805006080c1070b0003610280741d0703d090100301e0070000d000080c2008022140f0b8102004c152202d001059880701200d071400200d4040145400101e80b1071848042c030500500c102500000080f420624a08a4012401c117094000701e4550144e80c03400300700711400b841983c0c0042d01f403542c03e0310f0070354061045240352711441e04e4651900d07103021618441c40000030f200b60540c450349582c0e0030224200100081401c15603500041ea111290103000c0c18081c02d030b4100c4501d44a034001c0c2440841c60f40034451401480d21954040b8846c8402c030503010b80280301d11002005070615400208041c0c01894501c5046030b9100248001559103004074200c90700c0050140c0503900403004543e581395100006c0c88138546c0c110000040a07024900782c2038543c4546c0c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 986126223 1250 986124973 986124991
    0x2100512040f262a0d0507050304090e0d080c27040207020312040e01060c0222060503070b0a2006061002030c01140103111806010e010203070233040e010b030618 71
    0xc0b1100d880307039080c411108603201500400e03120a008204d10ba6141503c81048081c00000507041062200400070f071401000c0102c42400046039580e02a62203c0c207802851010624200c08544a41080da0a0f5005a41c403103c401c902080d00702401881c3e446881c0b4248d801c5a030800c000401340c0c5082c821012030610865400369210b15000c0204000304c016480300c403c0052450981e00165140680000c8490704222100070b401000031414005010b0380d40503d5151095907800a02448901f018003245040e5407102c1c41100d4000f600070080c108100c109800396081800050001e16140311450260307149881101d00f000d074403060207402c41d890360b480740100c051428010400c0141c0503d1001c001d241c03d85240c4e40401d4501a030080c4000007514103030500009913070301c18007030b442042520140b9800401c2c445940340f044900c80441c000e83e40e09505469079030038895103000b0700c090484085520004003004180c1c6000600c0541c0c1d00050505940191141172078004100e240c120a40260014 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 986127473 1250 986126223 986126227
    0x609030a03080f0906010312030b21371202070e010e04140a02032805030d1506050a0c02040902120a060e010e0d020c090a15080a02100512040f26 64
    0xa07031500d0303c0150010070300d61207a44160f0042c00090501110304103207846500300401c03201c51220028010118401003182d12a05680c640c031050750300012050200800580404007900d00040300140c0c2d546001446002c41e20700515201c00030b915464180c181c58281c0c4150303804107458040c9022824401e81c04a40700b65001c2d824030090088101e100b076080c41d10000146000481c56004c84d840300c2489202941c6c08408081d06000c0c100d28101401103264072800b9243d03945034071340c008001041d14410840148240050200c0c005001d08100e4100d403441c0c0c1c843d01c488898590030480505101081280c00001c043d4a81c070098200300314200e0725a208480c04624070403d06042403c490000f1020f11075603000b00d030721000d42600400d0001280340161000200341c0e0b00d2500760b07405458010403040d19401c4034007001800000100b001c21100c2d200315140024014101401c5800c0c3c00348904891007003601d00c0c0850002461811101c1e01b40f1304c41d80500c441c0014044204007800303c8568140c0da40800 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 986128723 1250 986127473 986127481
    0x6290c0f1912030203060d11150706050a1409031803010209040204030f11090c07030503251706010503270109080301061206091a151303121e1b020609030a0308 70
    0x2880100d02d000d584a103011411868420000381b00200c003400040c28102d0101c5034808142c0380d1a064042c81000c000d0712710343c0c0307204c1890070303030300402040b16000c110515140c2441b000030a10b003440c0b070050301050011800c16000d080914400ca1030118400e606650800440e540d40d1150300140004600400b0290460142810480e190030b40d200c0040e441101c4000421201c07050000a452078070307800d031078610780741e44d98544020304510196038001c0d00b0001002d52441c600364851190f0144403024001d80000d509d0395001900c80340010340e1400365175508d58542d05000c02c60242a0f040101c0d9441c004100d0003030a44403070b006039000b17800c024001040b00b10401c0d8041e00c1401504014520104104000e070044811541601822424070b4420001c181c00e00c0101c59801003954a4095840f1210001d1641c07031600c4040c110424030301d240842d1120006690140203080c26003803d40715030720390f00800080640c040581c3c502c00b001c01c90b4880d000b40001c1a40d600c04004508400d84a80c81c1d141da5810 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 986129973 1250 986128723 986128733
    0x17180d03032337090b04021806100807020c090403020c030d110a06021b03181201140411131b0e0a08191712060406290c0f19 55
    0x1050000c81903070641c00030502c0408101c0a8814843c0b25500808401c1d003941c07601c4220741a242c14030b00064450401d4264400c0c400e03000201c0f4043c07032003118050f5203901c1d080090501c14500301c0d0702d9a44100c0d01c60030422224003440d0a2035000c187c40c416189084030002c002424034400343c5040c2c0c0181c1c0542c1c5100d02504040100a88402c020308011040d100072203540c03681c61100f843c00420381d940201d405144140b80109002c50040210300341c0792600252a0561018039061480f58810f02039814446000380040c415002c060f040705000c040d56075220749901c448014407210b22034111483c00010184d1901c1d41c41100806110700d03100782181c0c1c820740360007480040310f0390005126444d6071004200141d030010310302003007403445c1043c21441049410002100820802e0302400101c000821208180e10156101d1242c0000c40c0c0401c0f89649803101602d030403803040158048045c0c0d511031240c03540e10b94030150081c0a800001c8030201040342e000c907818030140d042c0310a02035407104d4401e41084 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 986131223 1250 986129973 986130011
    0x1c0302010b1203030a0e0c0a030609031b2f040e06160f0f030f06090e06060109090b0a060c020d0623010e071b06090209151206010317180d0303 63
    0x1400b20b0340204604090103030035440b4440500340d1061941c0d2441d4000c0f103d5400d1281d841c00c500010084c46a45a403070034240042c00103080100c000421489001421780c8107000740b0403155402180700d82c0c0c01540c18a00e00c1d00d1050b0ba0304000e920b8026200565800e6507980100080711201c0c0d0043c1040307080c100c00f00a0510614011041806801c005003802254030455001c248501898003190607400484030f00d0003808241c0111200b6030500d00150151301c0c0c0061102e00810003a40c0340c48409503201c200c4c400307c4680c4558580c0c00101003208214440c46040c0040105000a1a2000b054107503038a0304100c1d000c130040c0510f0510081a42460760000040d443d00401040c0c1c560680c5142102c4028401c41032541141c401ca08100700324410310059030300c0207480b10340c0a0031300403031401c02506030a23455007145021392103411381503101c001810001c50054100c0794040c1d607206581221240003005034001d0b1600c13040a8490284510596440510b00c403040c6001c0d4030009000050911808001 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 986132473 1250 986131223 986131241
    0x6030b01121a04080c100e0f1c0e040e030a030501030201020d0c1106031f0b040906080a020f220f150501020a020306010303030c020c06030c0c070e19050606091c030201 74
    0x8184005a46001c140385a425040802004580300865981e40c1340051060013214400244c501c10284241d10300042540a0305008841e074040360074040c42642665540d55915104081c0c00c002203060f019190b0007003041200ca094020700200e281215440c9091071904400c0300b510000303459100410555805010404c6203291a141050440100b500c503000781a000303c00c0c9500400000002401c21815200040302c03034129a14068802640c0b00e160b0070181c0c00600850813894508a030005008100052150001d0381c05000101810f05020402c603400700c0c120905d4100c90040300402c2e068048a1058203441c08400b040000c03032040100f80140301c03003c0c540100e410740d80800118009650002051411603915280c0801c0c1980e036070344100c0c2810002c54480780c00c0750000c02800a804241c0b00949418a210011249040e41d201400c180741d030310584920b114141404441d42600354150060b540c0030b50041d00380743c42c20708030601280018001c40894008121180002400c056080c00fa003170701 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 986133723 1250 986132473 986132489
    0x30c0c0f080406141303030f0e06030f070207060221032502160f0b1b03190903060509030301060c0311162706050f060d0e15011a03010b0412050a1506030b01 69
    0x2400744100701d600005c030441c080a418048200140000240300f80c000d1001400c028082c01d4490420700f40e01140c02c1c08c141c454070090701500a021401b1440007074401c0e41c4031200d00700680d040402046c03c48060344041e2030340c0b5642c2061360312000c0c41910040460020b405603401010003411056807103440704490b8000069210310301c00d04219591085054902a0701d54039100310800003810714103131a52103801c41200404130141000c905041d0000c41840840e07006220501965075001401c03901ca00c001d0045c9800b207201c802c90b03070010a10802800099200c4102150f05001480c0e42c50340408013194001d02803aa400c003001603104241e09514007074020303043c81c24042c041c100b00c00131310421905004580680c0021908001481d00d44e004201078180d500d09440d002d800c10902d03000200e00900a0a160200c00340480d11a070a06400f124100c0358071a116509003400c00c540c810104039004019180c0b48155003d40c0049003260292400c03000380e90034005805460751070721500c0c00710140e00000c0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 986134973 1250 986133723 986133727
    0x9090209040b100f06200609070605131d040302160612110d06030503030405071211091816060f020601030804050f060c16050a050d02010906030c0c0f08040614 70
    0x1a29118440e035002035000d691180595280c524550102c4200c1c0e0000005100c428000501c840d00249602541e00010000380c202095030b50905075251740c256120481c90b44801010846684a00c001cac10340740200500f10a8040e54500d40c070b035650074072100d28814400310b00c02404105a01000281e9144903001544842e803450810040e050800c9807110070300c20f94a030310840c10b080d05442c00304c5041140380c60041003140e8690400e503650f6007007200e048036a8400c048002c99445140308540104561104228807140054010f004402c07202611074041c0e007410710000c040c050002e21981070304240c4030141ca03200340c0c54104001d0840c40c40301c1c0c1410541d00020014404103444500f102c040d520151060a040b508400c0428064030031441d49440c24054603192840040b005140c00b000c5a004030b455000950711441004950706a03c2ca009002c00c01c1140200101e45c081d4104002c00092410070800f141260381701c00c20107500c05501120394500002d0188203064000e80d250912610b460107280c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 986136223 1250 986134973 986134991
    0xb061b060114041a1c0602070501200f19120e0c01020d03140a1d1608010b010f022a0a0612050c070f03030213051302030417032a12071809 61
    0x440c44000684c003a41c000e00201c80007112003030900001c4c400c1242d101100f1556010347d402e03d107009041c4941d00950791a1503251540c0001d0302002a9201000fa1045071840d003030807480500ac40c5464004c64809000c0103014500300d0912038801d1291516242010f45045100c4034002030811030a084100b040c10700e011303403220b421404a2981c0d03500c9400e1795400244042419040b1203034134a0039400018a100390441040314400c0801400c04036402c1900a004840b158801074a218001d01c1d10400180c1c040845e8030f10604100c980303006500369080780134007a004d0036030101e80002c140360086404144450382c10500c190051240c030741e01c45108007465040009036520304070303015550383c030180c00c1540202d11000140300c52012030009100040001c0240001d0480080194104860a6031149440000c1441d900404012a4403a00b1030598004e912010040d65414149040d49201c00004081c4041110000740d8030340e035406100e154031030082e42840c004203286c0e82121504000100ca003407003204 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 986137473 1250 986136223 986136251
    0xd0306080a031209120f030e0111030c070219081b090114100e0a090603060b0301060302061c02070f050604051204180209030c0d0606090c0503190b061b06011404 71
    0x850380103a4986890164203454183e1039020700903022000c0c10180e240150f80341c00c00d42150364040d40c10a0380e103080c410040d500c0111800c0700e0200d20b8011603070404100180202000704002c290151008250040d50b040071660044a660380b07802070f0919500c00d82034140360000701c0144501141080b10b02c101e140d810300c1180c00401035514556801807600035101051107004200000050b00090300c401903160b600d401d071001510081c40256455480c00350014060b0a06009040c140c81e0054115445c00000000c4980303400b004442000f0340c0f0350300b8090700000a00420302421881d000302c008248605203400e02505007032031040c2f104946442040200100c0480c120b0091614641c40c03401611950320101181c00d040a0864840c3e001210002d194100300c01350b0b011500b51074002e0010414010681415201d80c842683d411a204003040c0030140050075a4004016605006d42805e082102c8240744400d51440302e0705554403a00840c0051001a0358411680e9041c0e008803010701c560011803100c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 986138723 1250 986137473 986137483
    0x10e2206020c102003090d0c140604050606132a0903060f020d0e0a0308070302280c12140f03090a0c03061b26090f070b220303050a0c1e0b06030d030608 67
    0x1182071040321902c40081c400c0c627642807050b4122038000e03a0030b0b920745454040e884207000c0765041c0c800c0d00d0074481e4811541322403040e12400760887c0e5007912a4540007030842603940203e481e404c01c004020340080005180d81c001c41060001b00c44e0056194245030003035074140c601c0303981690115030241a030040420361190081c0d4008002d4280142d03204401220103951101d0b1080348040c559912528001c045d6000013040d2031540101c0105203100b1500e41e003254814544001085901c50500c9264440c089490003180c20440b0301c42110604442641c0b8800503280e030b40c0c4255041580c403203000318151880400c8440b000c2ea90701d4a5100803840200c1c1040c903080c05003c60021314030450004003c04400c02c0551113a50485089070074160345e440d0300d20341aa002581d0704039041403100080c51840c600e030103804241ca81c96201d2a00340148403400704c4203800031050a0311134101240602520741804110317150070318080d0b02002624900030f811316203030103500700c880e07000c0600c5d1820070401e100020403 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 986139973 1250 986138723 986138743
    0x9020112090c0b03090a0605070201050702030423032406040b0a170f03161106040b070305030705072405060f030c101106100608010e2206020c10200309 67
    0x800007071039581400c0c010407a20751604240300c0140000b0038407146400000302a05442c2c800c82c0140200ea440c100c089007a103100356108400360313106103c140210507048900b40d4903502c4150766240c102c0003600000b89052101c40c0035104104845c0c1c40f010b2040c0300100407941c003100950341071101403641c001041004480e4403d110000001d282174500e940002e0104402e02007205007181c1c0c40c0c00e034130071245549000e4008202e99560031400305c0e1040382001d20aa4003210704215030f40c1d04140848c0c0b030588503a40300805190801c14200728450004d04e01450b40201c498120380c03010024106108044101c900190a4510a0308554851002a038001a04441d201810344004c103a81500c9042500c002070380500b202c030240101c10801c0041c98400360f0343d4003250040ea503a00d45030390365410300700b070000300944010101141c1c3e0050b651403c09402c003d210800c0c82070000603c1d0280110b4803500301188003403504141c0b03496480e204100c03009000c0c007070684158150305c3d82c9141448000c0d1a039480c1c100b0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 986141223 1250 986139973 986140007
    0x10b15091f05041d090316051c09093801030b0a080d02120f04050d170a0809071e120f020604080309041b0806090a061d1603090201 58
    0x14404030252520072039070126500501c0394006031002110081c10a0708180680401c440c030a1022440260090794405d0040024401652920884810320710814030150802e036034034403680071903640180000080c55000a000c1d90350640c0d131401c00042c0f07010340320240d844100e020f80707100c01002203010340e0440c4504145d10814108684a0110041e0701400607000402d601c000400300c006002c0c1000319078882c1d0f0b091250f0030340c0e4220903801c8407840c071402088201d4508000a10080c450780c1402c5005c0005140900741d60155080340760b4007540070394022442c110010b50a0014060400e00400403e03011b03002c03401c10380d400c00500c0300c6421400382540c452055420104040c11301403059080c1c52058598014092a9a85880341c0d4002d41ea5481005480e0142c2c0c03405000400d0542c0d11500c44010015560b103d0031035441c0d6000b000700c09000909104e880c1130b40c41c4030004034080d403542d580c0910a001c0041e0082e620749040c2507080c1442405802080c1410700740e1f2000140ea100c05020301941d540 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 986142473 1250 986141223 986141227
    0x90201121a042f07031d0103090210110708060c0a2d0f0207050105160b15040c03061a03010e07050f0f040303030203040204051806070f170115020f010b15 68
    0x109040303000c01e41e1644020354102e868600c0101403c2c983d8015003001005540380c1e4100406a5050300306584038448020307000450444071462200031000c2c01140c0f80005160114100e1140d40001700707000b071140e205001190515509081e110424010720340100106405400c071031510f15640d000500c61517010008100704640006601061141e0752030003240500411600c1d4111418007a0a50300c0c07060200c4050703c00c0d00d000240540c41001102ea43c00c2010030700c2071517014680d5441e410a030300900102c00c0c1040c81144003c0c1c5440f14880d0010301491039801290480c602100140070014070105811240c9003000140408850040c0e2590480d881d80341490391030701072000d40c01280c0900502806070702d8001600005140d4150043c60040e03000b19000c000c00d46170a40031a903041d000d0720902280c1d401080c0001c06c480e0143c0302da400d8004890800070302c0070310381c1580c01d46544000d030401c1c045c4111511081c859a94100f144004072495000204441d5400000081103103601c4c1812105020740 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 986143723 1250 986142473 986142491
    0xe0303031f0807080102120c03010f090e0c1f200d0f020f3009030a12030e010905030a030e030c060f1003120c060f090b010e060a0e01030b090c010309020112 69
    0x90010250041c4070385019240c215450704404c50213544210b0f1542020740c04c2101240c540c003051000c0324101d50410940705c40b41c1c1d2820301783c0d10191100c1d6104145d20300070303c6101c8003262103003907074124000214125000030700001303500641030001d01481c01c0600300d400240b02c00c00d4400040d0701a00b00c0c000f0304046185607900d10080f85018442000c0e50a80d00619840195a200b4400d4525042407020f0714030901d01e42080000e0054040d00901710b505070301c900c9855003c01e04441021151040529000c5490f83c503403c070749030940e440f07940c04550036400080c080c90400e9040c481c80b4031030540d400c0658509800001942d640e1600642608204500d8201080305c100c051910f0780000e40c0c1c02120340794101150f03500034100709000036040e18040e040882868400900e07120b0342071700d1907108401201c66402c2c240d1070825030000070304503074101110002c04102921540e100c80d00941c0f00b0180d500992800034a2942421103c55800c2c0c10703d414901e04000507a04002c40c0d100004105c0c0e4000707202d02d5 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 986144973 1250 986143723 986143771
    0x2031806090d0f060207020f01141206040b100c1e0b180a020d1218060516020f030708030706060b0f030109020a1e0f180e070f090f0b04150e030303 65
    0x180000004100c00340000c541c3c0100300e096000740c4a414000c60b40000da9055000c015289080c000d4064850030400708080c40321398061446440e08014040d00005140c0c4583d00030941044c222140781c030100c1c104618441c1001070190441c20302c07502441c1d499088030007131f84e150400100080c0c8001d594201404450b2080a0b081046102454000307003210f40e00348050421141c11200801c003003000130801305088061481d41c403841c0c0d084070220350b141032514140d02060550004424002c0341d10407591004d58107107070303020405030026040c000041c56480c4c00910384181118980e900c07032b50070003030103101d440400c514030400e5174111000070350050f0351400030303040c02c507440c4c6c03c0b82d084008040800742c854038a041c2e0103a00a0340003a899110010015540f46102ca103440c0c81e44106401d951080c1c002030303200c074850245030f8910b1915040410103544c541401c42800815500503c84021001c10100140c032000c03007284e0300e40c80c0c840c10b0041d800b41000c40860b8580c031004000664141e018507849020003 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 986146223 1250 986144973 986144989
    0x1303030804061e06051804050d0c02030c0310020424081302010309020a03080414040504020f060f130e0417030f0601050306030a02031e010506031519060b0703021c0203180609 77
    0x1071030303c28540400c84000c503444030090544e40030781da01682c1c5914100944aa410b141c003806150040c00030b1000c0042c0300f004445601c05020120303018029426118aa920704010440c0104a0380902503101c9007410300b1100c3c03820101d40050300054031038204603c41a00907081540121029042c00c400d440341c1d0005802515494000a40204200100000740601c100281007540e01a01900d05c0c21841c03842080203031642610040c0d48000301042e102c9081c0340c0345004118860030032089500f000d10004981251111a03803002201d60048070403c0200011441c41c2403005c0070040300c960450501c50311031007030144014001c43c140304c400004510660307810400c103171030598001c080795003410351512540301c0a10000300403122507081c0320204000c2e00c0c0c0070030007020240c0e08103048005903503107595101d5026244140c0821041c0e5980000c02d6008005005001e140d0080d00145040110420315240442190b152581150800d00c80b15001650641c03070500c504008558031a2103062103c0006c440c0c5d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 986147473 1250 986146223 986146241
    0x31216170a02131e05030606010306081009030e1903020f1531060203070b06030303060303270405090d0809011814030c1e01060906270b0a0617010b130303080406 71
    0x101c41455112105040c41c4c07082e001c140c0d08160207171442d07a2034000066082d00d46500544106401210011000e100698000480d0300c3c01303890320141d04205100841d070000c2c00400308141543c4030724030034401d60410043c00f81001c2030036503100645c0582604005003074080c04102c2c0b21070051480030388035900b18203641d0303c0c0701e0444001c030451903540d03d2401a6a03984090800c80b108820740002601c1e9180c0802a24481d183c040c014515001c1c8005603984d0032a8905010402e501120f0071000054a551241c580b0030800000105000900070202a207600d00042c805c40c03e582c109003581d580b1101c10119400030552145149140c0f031034442540d821f500a18035076242c1881034001081d918001d5290341e5040490901c001c218858596001f0320680d2410300030720006c014480c0300c1a03103000010000070090710500c8c0002801d11601c40010714910f4640e0b100302d00144000c80518250091040c0701401814800e80803446c2081d41c1107080b100308000d11000d01402407403400582442001d800010305 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 986148723 1250 986147473 986147489
    0x6131e020309100f200d0f05070c03110601210203030409050708061305011202130f0f05090114010e0606071721010b090d1112031216170a0213 63
    0x4929003100e0195841043d81007442c1c0d4a41803030940030b010316452181407500d1030715074840c80001182e82d420051640c4400e4a558010f0398402c44880c0f0401d0794820780c2d0181c2d01d280c2c0c070114035030070b2810020f21a24900045000c1030704910010041050103032140d0345a0101e0005419100a13180002415400740da4041020281030030f00300b15000c0d5120a0551090b8400c40f0449000481c0d0015242218000d0050607005900710158030054a0308100f0480c00480c8024046140c04035529002c06503540950329499094890702846817100f002c2c0100c18160018110181140d0706d00050030840141c003524080c002c2c42c0c0014082c052201200754103a800d41c0c1e4401195070350745010380146446860301285038290150100125030103c172042150581e040040000d444c43d80581c843e20110143c043d2000e510640c105400d820100d01400605190410860a41c00d2071500c200c0d500a40518024464200f0031803424050013080600c407059000881c8500040c1c071020044070488100045400c9110 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 986149973 1250 986148723 986148727
    0x60b031e07030b0702060c0301050d1401151a07051e03090a08030c1501182d0603050601050a0e0a0207050109170c0d0315030209130209010305030d1406131e02 70
    0x500c840016803901201d2003042e41d01c0c0b01d075440040c100d03151041643c0300440f80700108010800c80c41d01303407846040c40d402140e25600000c4050206821640d1034004960001020785040101441013000d8075420174603000c2c418909a8690740c0c42e915503070131904c0649001b0b4450106403551a082041da40c401c403010b0082d8071039503241c0ca00c484d40d9400040011540344110b58103180b01440a0359024100c400b240d40e40110881c1805980000d0500303c01c94001c103603a000800009146003190107081d81c0010040003c50b00d01f1810601d0400d02c058101e98000d9000c0501045a405880b02c3d207540701208070b400503141c40591500c5405042e1901c80505003144111803c520003508800500300440c5d02c0c030881d01391035034000d03050701a10055424038450140901c0f081001d401d1001e8460340c00380e19000e8010140d043c0c0e5002540703400303080c0c0090300c0950000c06c0d203084411140c4608a80740c2c0700511040300c2e0307103040000501804101116001c4164440c0188886c52002c4900180380800c1400255 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 986151079 1106 986149973 986150023
    0x711010f0215011206060b070302150a1806240609090c050c010608010e2a040b01050918150607020d030810030c060203090a06050313060b03 62
    0x15409900220a400c4000024142c0030b4284803410080d010300070304285007180c0c1b0f1500b040d508480f0401c04940400d40020700145c046404441e903800d01d075222400c090280100181c05000d41210404400c104505a000008146884c86460034440361149007001c3e00e00452085902090380b181007440400c200750003025140b841820003034a0028002c0400382100c030710354051859655240b17203517400802c0512400820070390214020310710020160081c0300d2110003842881c0300b41c0d0707a0b00442c4c016034051420b0380c400200082180312001c2002010068150084400403154034800c0f1000d1020b2400300300765200c00d500a4480c10261070150340c19601110060404003481c0400103001002414581d10352000d00150760113076445201107020301c00000010b400c5001404000c1c400c126403002414501c404043d0403a40c046644080c030300210782480760326085000300c0700d0603108407 = true := by decide +kernel

theorem cover : BRFrame.Cov 985971223 986151079 := by
  have h0 := BRFrame.cov_init 985971223
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985971223 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985971223 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985971223 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985971223 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985971223 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985971223 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985971223 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985971223 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985971223 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985971223 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985971223 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985971223 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985971223 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985971223 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985971223 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985971223 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985971223 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985971223 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985971223 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985971223 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985971223 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985971223 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985971223 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985971223 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985971223 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985971223 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985971223 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985971223 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985971223 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985971223 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985971223 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985971223 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985971223 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985971223 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985971223 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985971223 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985971223 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985971223 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985971223 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985971223 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985971223 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985971223 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985971223 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985971223 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985971223 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985971223 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985971223 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985971223 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985971223 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985971223 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985971223 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985971223 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985971223 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985971223 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985971223 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985971223 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985971223 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985971223 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985971223 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985971223 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985971223 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985971223 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985971223 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985971223 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985971223 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985971223 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985971223 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985971223 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985971223 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985971223 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985971223 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985971223 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985971223 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985971223 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985971223 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985971223 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985971223 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985971223 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985971223 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985971223 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985971223 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985971223 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985971223 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985971223 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985971223 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985971223 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985971223 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985971223 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985971223 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985971223 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985971223 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985971223 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985971223 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985971223 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985971223 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985971223 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985971223 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985971223 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985971223 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985971223 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985971223 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985971223 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985971223 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985971223 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985971223 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985971223 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985971223 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985971223 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985971223 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985971223 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985971223 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985971223 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985971223 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985971223 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985971223 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985971223 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985971223 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985971223 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985971223 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985971223 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985971223 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985971223 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985971223 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985971223 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985971223 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985971223 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985971223 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985971223 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985971223 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985971223 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985971223 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985971223 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985971223 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985971223 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985971223 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985971223 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985971223 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985971223 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985971223 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985971223 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985971223 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985971223 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985971223 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985971223 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 985971223 ≤ n) (h2 : n < 986151079) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
