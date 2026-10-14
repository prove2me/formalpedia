-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1961
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:18:30.273738+00:00
-- url     : https://prove2.me/submissions/87d88c3a-89fc-4795-9f61-c72a24fd803f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 352517985 ≤ n < 352697841 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 352519235 1250 352517985 352517989
    0x1905040f060e060f130c1d0405070603140c0d090b070f1707051803101e0b0d15091110021b030c0f130b0301021b0c030105060f0d0611040602010209 65
    0x203402ca8004007040640158a040d8a40c000300c0c40700a0300c0380d10a613400e183d00318100315603140a100a0444000048004c1c1070f0141c8101440504450072105400b079400005501402400f420344080c901c200c10808a40d908034406220f90042c4d0401c801240d200e051031004500c3d21003d541c01400b05995008101000c5a0003520f100e9040d20b40222a0740c5120030020312540c40400c0c0d440300c002014034100b440031440002490003000030b07200003407180340c0000035484c1000c0361490011400c1c5ca220511101502c9000c000001d0500d1202400380800c1212003103400b800d0394080c100d842c0c8104200381e8501303001d8001c522200c0504007140c000d640101d0100c9601180407003c070044160440090140d10303a80300205e00ba501900341000c0c0907131201051070a00c00d13420b0304082070506000e00210340310340303451050070700700c4201c125810640d01444142900c1c07400d06000d007070f10400010700180c00c405a4142401030940d02c10b80c05072900b694607984074503002040c600034001040c00340e0016843e5003903941 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 352520485 1250 352519235 352519241
    0x303071106040309090903020705030d110c100905090a0906050f150a05150f0408160f0f05030c090603010207060c0e0f010c050c2b03080a06140102070b031905040f06 73
    0xc16036005a000004010020313a106543c0d4080c1d17000f4100216140001e898184d00e03144c5c0f541c01083c0d0600a00008031741155108980701240d542c0841107904a12484c401c3c407506034440020000012441c82c8184058103040c504282c000442c200000b0f14101d454a91904803a03041c2c4038032040001c0d4a050103054480c02c05407034200c04c0c0444906607c5440c100010783e10142d2200c1845004d41c0100c2e41103010307000c1d01e068600034620f060a0380d1141d40d0b00e28070340c20703440040d004048075905558400b06403d90700c413001c0c0d002d0f600d005e001070031484c07a5103081014298005110a51541d002c1004070002a0706001301110713000300361107881c1e0140c42c40c420000941c80d4906058104140d403c04407000c243c0000d520070b014001501c5100d038501c889501d178a146190b9400b9000e0404449410300b08140c0e000040c0340c802c810a00040040c1900c40320701c0e14100d00c070200c1c103900591040e10203000d0040f0040c006c503000714415003000c400c40c2814000406540d0304440c15905014040040341c14050140 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 352521735 1250 352520485 352520507
    0x10c1814030f01111308030309100e0c1504031223070809120f010507020a080711010c02100908060601030908070b0601121509110403050a081606060801050711070501170c0912030307 80
    0x201550231460421002070f0b69003038410101d0399450301e42c001300480e84401d2085501000016001e0583e10b840c2c3e006002e0380b540188400c035000d030810024008024814100d4550030703602c0c00f56403141c140ca040d00381c0c0b056402c9550292030301d000c100400c0a07650745003902002131200c8400640b003581c0182d0481400c480d80200702c0401d540140b004c460018020074201c0b1006544203901c40b800900a100407615400320950003504991000c4903680d07041c2e00311050381e00310f0700004200d4882d13a58031030044003030303450340d0300003c0c02e0b07200502c01d102c00500100d45066020a040c0f4002c0c40080c1d0038003490b41914a2004140e9441110810900c81c152142c01000c5c04005041d90181c509460769071440c2d41e070407040c134000e0187c0d1404511080d02440f000384000c4081c0e003060301800501e49400b8200e000340b4041e12010041407400b60034034a00080407030345100b01d4405031981d01c0760b60381c4c01035062100a03005201c50b826080c2005200c0595481c81640451514003e00031a02c0345801c190280008402d0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 352522985 1250 352521735 352521749
    0x30f03060f03062a0c26030f090d0509010519030f0f0209031002090f0105071407140306060d080d090303060b0d09150b0d0201030f0b090106050c010c1814030f011113 73
    0x2003420f558540000300100c004da4008580c49031b179840801e40c088020050490403d0344e02000040c880c2100d03161940900600b0040182c070300119250300103032041e01c103155510b40070031001d00c038985815131565110380f2141e44500300402c001000c02ca1201c02c4810140980340b41d594045501c1000e400d04205400c220a4480011860040f540002410403070440301e02c03070304000d000118001003060260320303800300c50268000c0b100d080c3d888548189076403104152684c000e1003032000013601807420366450a0803d4009029902d8001203100d404041d100042e0240c00340368807100d00281c82c8c1c0684d0003e02400200e8000095070208502e131030b146541900101c40440c07070a02e00c4c00d00442d5a8a0740b0344090a0742400d001418105283d40301000e41004103010303900112005c000141180c0141c01031821810740c000800080c00c2007001590102c5000038040300c58000248184840088419090380e40d007401001c680740c0301401c02d00b075070030356014840c40f001c0e081000ca01d000348445d00c52440406481c0d0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 352524235 1250 352522985 352523051
    0x160c060315050613050d020d0602070506011d0f040318120803060108130b06130f020c0715030606020601030803060315070f090f060c3201020306090f0103050a030f03060f0306 77
    0x194134800440c0c21041c099640b241110807821005c543d24400d8580070750354409415512082c603418616280c590911600d550000ca803804d0000011458054902c15a42c0d10159032041d21561001c603640d45800c000981070881c0d00c01c0c0441c80390150b50302c0c140014031908aa958900e4058001803000308083d09090544c21a10042c10000782003010240e0700220948981d039204000c0180030000d001c450405005491000400c0c549071600860440140c0e034040c06020b02c09084880c0481c226040d40c420400141c00003001400000c903c03600854020030001e086860220400305401d0071400165004004203c0302e1844108894001802c5801450000b03054100c2a01d8044003030225843c0c660000c2052801d8106000d1321751842800600b500c6007444414071580030181954001c1d8020388010384100031440010f42004030307403118541600e44c000094000301e002035a059900d0541521840306040d00c0c3c03600881d1000e540e407400802980200800f088005d480b4038400c0152118100450206c01 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 352525485 1250 352524235 352524247
    0x60c07080c030a1a09030913090605100515091801120b0105090c040b0a020a08030702210c0c150c0d0e1e0109060c02030c03060103030302130e0615160c0603150506 72
    0x4a074500c0d0101103082e00c4c04a24090307482c00d0003a0308600c40d42451035402a505598400b94210f44e900500c0301d148540010080742c2c491000295000c0c50b184280c60303020520384801c583d94608040a0018440064999809400006417040080344240c020503088103802c01c00c1818030442c26001401406d047e281d8103d2070901440308081d9110302d00805480702400200c1d40c2402e031003000842c19440d003001219880f0300300964029242d2001d544200810b0040c1c02e5058418003100007252030015000000f070a07404050303400c0c07040310b41c801c0725080580380f014415803081c101c0902c02c107488080c0b185e5031104903216000810668000842d10890307002092140300c030803640c000e0400401d590507070510a41c40113640c1300003894602d241031019058054a4000010940c0540146c1240031a1160f03407158a86c44180615100200b100c0241d03000389042500c0303404d05281402005104000c400301d0300d6011b441c3c1c4507460078185e154044400070f951030412800c070714107004400b00070707000481d20245001 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 352526735 1250 352525485 352525493
    0x70e0d0f02030f0f0715030204050303090d0309030c080a14160302090c0403060f02030106110a2406170c030d020d0210050a0b0306090a0b130b0a0e0309060c07080c030a 74
    0x2000104000304008406491030301550307420004049052422800c0320007040c0c160503000d03202d60861041e038100361041c0100441490103802550265100a001941031910020421480109001041c7c0c180400d0480200100c0c504860110250400c40c0c020b040b00c400c1840e04001c40641d10041daa02a0000081c503209402c144516004990b01185c1381803d546a10002140c507110726071006140c5450810880a2020300e500590304a0355503807540070b02c1543c100f6080da00c0d800400342c010480b801c4205542900d00c007003407003c0301070030348008001613050f01c5030010008032074160680075403030307000002400701490108120802080e00d171010345914112200c0196075100103c452050b019241c100091042c000c0c0c0e40211000c0200a0407203403203003042c103110b40e03e070320b0841400e80d588402c1000044458103490301340c0030540d920440300b0b0425076070021a40c3c010040920650094001042811415030319a8081e010b81ca40c058050001c051416907030074a03040002c005140aa040b0340c651074041 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 352527985 1250 352526735 352526749
    0x11e030506041218030309030203070504141f03060c120e011b05090f0312120702120403030c05150a0e060a1a0622030f0302190c06141303050114070e 66
    0x105610030750301041140d400000344c2c2c1329603840800c00b4801840060000505600c202c68204aa0083d01030fa40c4039900e40050200f0f85a00703046104540315200c02141d822585030b03890b080c20b51220038580f40265102ea50714000e44410112905c00a0703001d08401c04200114820b420782186800003c00500b6a42680e10141c01c2d88842d9401c11320002064041c03980c0c907007009a000d074000007019078800070038403d44980c081d04000e11000f454941540041c3c4414000140b12900350f42c80c2122900305803542e0b5080380c4040403000c0c1207940e801035816001039860340380c1d05a4050160010003041c1c500e80300003814504070b002400c00d04100e051894030704580d165003d0602c8900d000380c40c1a030f41e41c482d020a11402e0a00c035034580070031131040c01d000001d00a0071114a6201d600c81d5081d6203054080000310380c0010b03009500031b04903171100d17141004400c1c004d03a08500407130030080407103081c6410504000802d4441c1e42c02034070280d4446500d00a540708a8101e1075002c0842e00342042e065440002043c01 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 352529235 1250 352527985 352527991
    0x30c030c011b08030a050f1006020703121e051803160e060628030507030509151e040c0e0105090403050702040c050403081605070b04060210020306010e030d08011e030506 75
    0x611840310684110040c14504000c039a903000414240d89050030043c91740140000c80750100288200700c08610420100304510044900690040c1051819034441000d03280c110300b48041445000703c07840c15400c2800f03641089001e00b680320580c640d6091900c180b00080c0443d0b543d80b294101c0b50751070b40346a615000e0078041d0703200414051150342d5190081000d61259800c86094401009884075080014621516080c111983c0511060b20341e8481603058800a850841550700b050622540b1100c2040e1a2540000d24009602403c15180c000c090791800a50303040c0c0d00d4000307009040c0040541c0d901050700400051f40c08441130314054400800741d00038200000e00c91a241c8503441251407040041d24040c682010a40380e80f248070303441d20740d0b08030a45d020444141c0104000007415803999001e82e001c5640c3c98003c1d011001c000c49600c0000e40c0000d10540c14000011051410760f102000f6540d280130240e101c100d02941000581410f2106010340f08006980008003400000c40108403160 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 352530485 1250 352529235 352529237
    0x1203080112050307140c041104060f1404050d05070e071106150d0b0114041413020d061401030b1b030712050a24090605040b03060402100905030610050906030c030c01 73
    0x181250461502c14210f109146000d000c81850110010015401160303800340c0040c00c03a020440f0160124103c000d500072403107501e0214100c00d0840794030070702590400d01c040c14084103c3d0310302601c46c1d000403411031515600740d42c10340c030140080c0304d0980c0c04c01d500c540000c03031400c1c0b8415080a56450541d2001300a00040840d1740c00304840d080c03a151440d00301001c0340d220100603c0c541c1c40d00d17051503440403075166491040b400c2c90208080d5600380841ca80c081e003440b000c400010006a001d010051045240c219040c42d81c0d15412000d060400c0c1c103641c0618413408800f00d060414015440742e0520320103029070030304030800c1441201c3c0d03044a08600c2c005040d06012415a0714040c2c0340d03005040084240000c0034094200b19260011202e091058510108080100d561180700b0720040741c0124034503c1d0503a11030000718000d071400c8106048000003c0c41c20b41a42500c0302c0c042820200c0c150340c0100300300e2506109101c0351400c140320941c000c00c1500240a084040d40009031788854041c1e64074 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 352531735 1250 352530485 352530509
    0x9070f0b0a050c0102040b03150108010e01060e030a06050403030902030714010503040b2208041a0f0d0b130f0209010305060d020a06030209040b041104030203060709180209011115040c12030801 85
    0xc090900980a030b03202040200021900c071035817087d44922a074070441e45510201d103624200c003000d60288140034180e0701c02075080000d503030030010182c0f6806607092103140c0c9407040040c14000074107e409241d00c03480c42580c0102c0c000e021403042c58a0202603400c030200c0c0403990400082c06913480030549600642184180d5a1501c0d01000301c55a846010240c02080000030820030038040c90400400407070798000001807201095108260003401821020740c04600d08010301030320905280c000c10002403000f0840180c980c20143c2da401100c0014064400c041d402140251003580c140c8285688450140d03010030003074005900243c0e034231885016503014594046800303000c9484d103a10070510340700c0c041c20400070402c88001345902a006440102e00c079200b40d01c00602440d108524400c12030350403507959144e91007480e51880c081d41244002e41e0421881c1c0c1401e80c41c4000800054240c151011007c0940e81460f00385011410700e9900700c90801c00485003400006680a9002c5044521041d0a2 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 352532985 1250 352531735 352531747
    0xb0f18120109210207080a2003060711160b120403030b0d03020a0b010b090a06050a03020f03041b14061209070302031c020d0f05070b040c0f060509040509070f0b 71
    0x40e210545928440344030340c42c000c0d02804214580050300707201c00e000440c002040b0180701c030880e61052980601c80103a000395512000051a0072845d840340f44a00c001c051995115401203407810108840030f0300010a90455407000410a101e2582c40090107195120402e04145503c48103118480030b01000f4046500018185031090380300c0701071001c0c001c0c903a0807031184500b4001c1d6503c42c540d806984058030307000001002c619030b00444d0503002c0047c0070303030510070b2521400390340b00e400032400d050a040d004c000f0301100d41c80c903c006520507842200401c11103000c0d015110500c1125030800d4400e080da00040440d80c2c1d441c10f0030b80301616141103080c02c841c1e441019041c2003030300316800250588a020307210560300ca04884000c2480c242e9034200d94040b80300407012141000e44100c0000403480400c80312000c1502d2108041c0d000b4090609007120a0f0347e0075428001c0075160b8071002c0087d070040341240e401e103850f01541d50018500d00080449905000141003400c1c0b1314466504031078000034071 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 352534235 1250 352532985 352532989
    0x503043f0509011d12011109010206311a0106090e0604053102090a060e16080115020a050d030e10090506010e040201120e0d120c02120a0504030c0f0f0b0f18 69
    0x148170710030f402400c003d2104400e000800700c090741105d4006409406240d000603105540083c0b4013100c5501300c0c1c3c0680c2804054500840c0c507040c016420750741c2c080380301e00380b030848011988218001c02a80e40e03194500c074500115a0041e8030044d020038403e134200700a008241d982111103103401d407410580c030010082070104090402c3c005000094100c0514410000c40300d01950180c3c00b107814011a0302540d42d0741c02c16008054a10b007a525012030380440060005c5549111032030032002081c012200c801246403952850a1901108140042e45480b076408000c8010312000a06909444044c1706540340c6035141515540c050040003102440513001600350780c4a6018409492050042005407076000c0f80140d480e074064003003450104429604071200c891062141c10741d44c4a0543c00340030746042e40010302480340d20000d805030411505000100100705240010401840103002c01031582d49803184240c001407140d8005d03907100b00b0a2207020001007240c012100d45007010a5000030780110480 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 352535485 1250 352534235 352534249
    0x6030209031b12060408030a15060203072003060f0109150f030210050921060112020d0b0601210209030d0f080109050c16050a02040506120d0503043f0509011d 70
    0x340f8100c1034855281400140074101700114010005a142800400b45800d4000c8903c8214810030f00164801c01c20340021500480c014220500b424070241c2c85203000600103842d20f94103030b4011101400d201d0041004800a10034641380324007421000720180c1c6005031241502a941c4000790050a1100005203070728031500880b5000880105000b1110f4042800017440c1c503c1501d2070000c80c8a9580003040010b003420741c07082c119a00900041450a01d0f6440d62101c2c14060704603410700517421a0503a0310500f080560000c4004080010b88070104c0000f01751503c0030350301041c400d111104081d003141540c001b0000381900e44004001c00c080d100c0965890981c0710341c401c01d541c040d210a103150304114020400300b42c414000c940038043e079120311040002900c0103024a036203079800007150b0902c4074002c40107140c0c8940070b80d0350036240107074800b4107402024240f8186100c0040902c002e40380e0309034001c44e115003040289000b07403c00220100207012407020a80c2d0320224607a064000009036a401 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 352536735 1250 352535485 352535509
    0x10207091a0a23041814010e031908060603042a08010c0305070201140c0901030b040e03070302160b03041101030203040f05160f140312070804030c030b0a0606030209031b 75
    0x542200310301c2d0758950368078101c03203010050310310b6104100500f0b0b1068500790203520200c3c409261440500d0b421507469003041d840402c0c0004103035494500b2600039560a0002d002c03640c20202c0d00d2808401401c1d001007848030010980d9200303480c14010f0001141c800b044c11000e4202c411810a00c0d00e803101904804c6149a03400000158280001c0b04d03040c6516810180c040c2003a5002803101b503076800240260001c00315011001482c0c1404030015a6229401080d0540d02c042c01c0042c03404d84403404103007164000c0d0401d1780546c0c8501101c0000c0d0b1500049000203016241199080d41000d0b40c40e071840303040d0b0f020118101500403000c40c0900045000019a07640e12000300d90104041605191190899114122081412110010b1170050081054105110040140240c1901a013514555412000c000e0ba5001001e02000c00000c5000f06000c020354000e000020061400da020720094032842c0d00704000f09030051100043c0c0b914001107029822340b628060b105800400e5010032402030500c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 352537985 1250 352536735 352536739
    0x70605061c080d0b040902010215060d0f051507113a0e0f0402040806010302090a020f03090303061e01080609040326090d08040507140406030602030a021306020705010207091a 77
    0x44588008002c480c01c01402003404000060116000200401080307580b0803134064056040300244103e141d030040a05130b40104010b100d4580c0044540790b038450810380032400c4500b035002c851002d034006000d291740340d8040e069180c2143c8140c80802446d4440da4640911140103c450021203610207101d80030140380c0c1c00380c140c0392480d540407540042c1122030b0141114010180710700718540c0e6081034001c44058401c41802010103910b56801e00c1000440180403070701c007950074844001c5000c0740340300543c010490103006548034140f42c030070403440b010074036840c030b0300b80c0c1d48000100d440c1d0f42c0118800b0b80c04001120000d019980b0350400303581c00e03803c6581c0d80802250850b00b41c01d549060003031090144984804990300c9255040054a85120646000d4010341c02035400b0801d00c404043c09502c0d6072400340c0042680d0b590f0381e462400344d0b00259502c9003100d030086880c419508215424400900317080c401071105a24110010b500ea6805019071910107450700882004c401ca2001d400d0220880 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 352539235 1250 352537985 352538029
    0x90118080a050418090c05060a0507110303090406030305120112110607140f0f070f1a0309030d02041202041803051b1c020f0d090e01090c02100f06141507060506 71
    0x1d20f131070001000400001c640308030748000007141e507003014020b0311044409516404d14242e1261603920007200080d0b006941880300300140c581e00e849134010500214802d8031032944825422001807205401600a010221244600b08c408900c80c0f410151401500307440040d566081c5040c9000c00c5401001e01c0d00385403044205050a03414002210101103100e401903480311611034180d600000c0c89031250341c81d0b960943e1000380000c41d448004640019800c011a0b240c1302c0e5910403003040c3d03042a48511080310030304900b407080d400d00d401405003d002c1c08104c8803a00b8503d07134000c0c02c6405100201e146607400d400020b0343c80282084814500032900002207007030b540842e0001e40d02d088035144051a40034080d81c504095004109000c181c502903601100180c0c28442680700030b041610703003481188241c0c04d61380e104003064420600302500205000c2911420148114040551703042030324020074010314600142c41c08a016610340c10f520010106041c0c584600098001061105079407050310 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 352540485 1250 352539235 352539269
    0xd0603050d02071a04090e10050f1005030f10020d09080d0603021f0c120c1208070e010f020601030f0807080a0e0103050a0608060a050a060f090e06090118080a0504 72
    0x1000584060201c03155801c80b9009925000c07101811681011003409200080c00280300b588403c3c2c10040003c0d1811007118a0341c456410b00c9402d072901034490400c003256400610072449660400400076140550041c402c44105145855564046c655410000c42d4081140c880030740041e0001c0c0f03200742c0c00010060300d5a40032100040203205510040f4420b5076010b80425007540111514a81800c80340c030b40e1114150305880b41c0084000c2031041da020809403a450000184544145004076075131036844c8003252a1110b030141140003803000c2941071001c0784003010a21980000d270389054940c403200e4441d201c4482d150540c1c090080d110010190080810f0100000c0d030301410020308058244e80a01940d2070b02040003080300c1003030181295a400007c0094158a07068110a80298203900002519680c500c80c0c04050b0f2003540001c01c6680e01c60800c084e24080400c00d05030001c101c6c00080207580c2042c120400340192407607006084410106403140228010415640140800244104000 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 352541735 1250 352540485 352540493
    0x7140d06090524060403080d1b021608030c0c1302130e0f0f01060519021c21051005010c05070801090b061e01022d0f0f060f040201020718020d0603 65
    0x180c219103a00c0424001d022050b801c1c031010f400f6250640c00070340ba0034902411616103a050750b111040010b8011345584042844a45000c050010441e4680c06001c04000c00e510180d107003042c550150207e5072052001100e80d4002080a2880c80c00c21164440410103000001c4003074011143d54108400c850344000424150b0340301114070400c080d055040030395076001030082d40c1d00828007421b8000f0300144038240d00c440303c0003010352802074a070040700c004660400342d424080c41501032160000e9800d4420b070340b0040454000c00001226040c090140b454a40300d84a840301d03007031244504100340400c40c0d5090040c00d0201d08080d015420080c403121505041c103a955420542c1da590003140401103800000860710702d22180403405901401800482c0541e005c003070a0305040381489003500006080c000401007090743c402d40900c01c0a00a94403850031440c1c10318100521070900da0340708904110060380c2c04109101034410410200e00c04014855640d4000c0c010202040145d9240c0764011042c0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 352542985 1250 352541735 352541741
    0x3030203040f15050412020d12091805091b13051f06030b01091a0c060405010b030d180b07031b0f05060c1c0209040b031614060309030307140d0609 65
    0x28802c81d4484410950b901d54108005031901421030001440901040c0401210300b0b40207800b29000403d8500f030b02c061070312005c41d40306804051401081c65408104000200c091046800e200c2c008010402840d11546141d02c4030300e40d602180700244010100c070300583e6101501042340541000c1001945800560420800448080e000158054000000b18513101e4010014000410380d108101e41e440c00442e2a00002c2104000400703030300501103181c682030204032030b500c903500610000c990b00003007030145420250400402002c01080c0d1a0680c01c1415026400003140c0703c2907165544c3d5402414102c5020400700045c8400d02a03940399681840004040c000c045030242c400c4d039080380c0711300c05259103c0c880c4519048035598116a2503002c0495a8068541640050008515110701400003401d20701e914011408001501c00c052000e89031070b0010303403410368055884e18038500340382c0c15040c2d4900004103520100305091000c40b1650701c0010a0311000c000b42003003030080c0c0d602c0301c50306806 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 352544235 1250 352542985 352542989
    0x31806020c030c06030c0d05040c090e010906061703030c0a0215090c01020f07050f040e0c04060e01090c02030702010804021009030503030a020c0111030c0406081005130b0405062b050c0a0303020304 87
    0x100e442281d02c880d6a40c90044c041300c0c083c0c480d0075002403405003050300c0030000d058024010b03a20f8195641c40080c040c246805a100c4403803100d800042d42910038036143e01101c03d580c05c009100d40e82e00034040e441050000c00caa8203c69210b00703468699403c01030484c80c2071a070007005201803442c403080c4281041e0014040c1407840090302a0359855451131000c2da0b58004c18030a0940c04461005030002d0344c1490383c00074901902031029140d80340e60342d01c003082c0bc0c0c42d5a80d0260300600d41c100d00400c1030080c1e920a50760b6804451010b1840c0850755000200042d1006e4406031107514a00300523070703040d405001c0c0f40e0b00455204c015a500d80c602580c40704000c0d00000003040e003950805031003511000c80f80d01101c0c49064441e11041c10607003005001c54000c640203203160400d00b00070b02c000c41c855680005c0030329150101da4000c500080380d0000c1c08140d5a015010038000d4040c00c3c400c80d034003900c54558020307500084401000e0340c1d10f1030810625207018600101c0e001220548040180355020005000f = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 352545485 1250 352544235 352544239
    0xb1b19020306090a210c3219060f2003060a0503011104060f02070905040807210c02100203070803040c08010c0f02030f2b050702210f0304031806020c 66
    0x350f807009105034a400e40c4480040504510034602200000000f2081482c000940350100d0058056a100b01c500303496640c88550b49004c0c00703400c507944020700e021800d92281c0d140c0a004e20346141460f94100d52030010000344900d4032000c103406440015480030030640c0c94400040b03416a20080d940c4143d910640700a80204841c0c1008507180c101401080000304403815140c0c81e10380b8040b0105c60400300300c8548021805184030000e10100d041c0260390086004035211030387c03805289480a443c20040200700c00b0f030800421503900007a08204070a10041d015036448004c1d0b1301c40344040342103204a820081800d80c020003404144041104009d05441d0628020014001840b80686a1500904008005038420007400c21003280300c1c0042c2849226003d0030b5500c0c1d80c0340c04c10b0b0384044902000000009641c5d0810082e105078104088860311003d54a96030f134092001443e01060700c14000d0303d003c0000c0c008080341c1094491030203402100300c507102040096444840081d07c1d08000a403440c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 352546735 1250 352545485 352545493
    0x903090b120f040228060201050106091815080a0b15030309090a0c1b060e0709020a0e3003040602010e0c09040b1306111b07030c0b1b190203 62
    0x300d4001518400c440c40e8440c5195010803039a030381014800308800082040f60403601d00800800b51078001c2c0300206442c818602d0300d000a85c1003900c02403c417141680305408010b1480c80402c1400003840150001c00c624020200d0030900a01e158407204d070095100c0e18191041e154060180041c141d101400b07000841c4020209d100c40004055480c010040010740c00140400824100e507001d17400341100c40068207107030305090090000500f00ca10030340026030b1656103400c40382801d1001400401c0150105000450070000318100040000e07901100c1c0b280940d240d600040100c0605944440411420302000125004404081f0f6166005442100c000d0f6082c030b1064014540c01003064549903002400c80c00044c2d075580c80b030000c1d0a030007600c0144070030035880d080c0b00450254050200710000c00b080c0d095440040c02c1030743d9000141c001d40c030f100d9600105801d000041070000c40d981112210441940c8810061a02010b80d42450822071001e11a124140590098042040c225207000710300b03a03 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 352547985 1250 352546735 352546739
    0x90a1b020d18050306060628080a051008030f0d02090a14150403020117130b07090503070b030108031b0313030b01062d03020a03112208030a0203030f07120f090309 72
    0x1901c2011907009941d45a040b00d80010047d0424a010345800124610546051604140020082a6509401c10004071803404000250229025050b000340d082000c614200e40703002c070059164060349041d036142400001c0c800941c10038680540d98041310040035084016035841c81498030311014406640503034000100222900c20700d02c259000c6030f030182c40d08013001c0341140041110030002403484842082c820165030204101c9000a8440c444503218074441c1d500307003401c05103444d4075540030703503a2240200014802080301000740d400c91307038111021030840d10a43c11242d046010b4454902c1c80d031041c0c40c0000003400f480a120504880309910381204c1e4444024540300c030b800e040c01d2584d8881e03044032001c54509109600404000d0040d2400041c0d44070300d48240c0216521068444040801c804000302020080d05a07440080405900071440c1546c80703100039449010060020000134000f40014201c1d6020f4407120320680724000c010003078134113642c0002d070080102c070100b900018148040 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 352549235 1250 352547985 352548017
    0x5121e0a17092e050901050f0a3908030403020c0d030c060f02040302030a020111031b010902031b1014040b0a0807020705100c020f0f04090309090f1802090a1b020d 72
    0xc100040b2100e4140f0041034944825140769101044081c1003050401814805580000150001d10426a00c49110651000440c00070000c1c245407025025120403200c4160381030f8000d4200210340c0541c9958680c0d640782000c0e410904010401764020441c1d0000204050303021408020140c4601c80411081192004040c101c2c0924000250140d00ca081d00e4005580940001c081c0105041d084a1400446104100e00e404450400403843d0303440d1841d5004524090000d040c401a6010b060400e6a40e980000f40218411291090601c444805808101d021020842d0042d11240c042599940038414008040c40b0b03003268428014020a900450310b0701e0305800000703500c41d040e60343d020242c00750340070070903900486034119034804408141d81c4000d03150380c01001034950180d15204074491804a440c0c0075622450710140505181c00c5680d25001030140c3d010600d1b0b034064501210030b0383c40035040d1005000c0040424101d140328000081d007e030303001507081805100c0d692200355001140310 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 352550485 1250 352549235 352549279
    0x60807030b010603091112030a021525030605031207051c090605090a03050f01060e01060309080403241b0f0201050405030405040905031204050703030905121e0a1709 73
    0x100411030030746500104803451081e007020b00c4650194070541c5a505411001500e040e4480b42d003158160804142c8034101078052001c2032656448442c0700c0d0f0180f5000783d100790b80c05402621000400342c0c0b012210105840b0b0b600a402422000d42202c0d501d42100040e01c0140d0408501107030a48161003042903020304050f148202d14070940c8031075401ea424040c0a903120f800840c500c6412098012001010aa040003c400d6580c0c03402c000003145414807150f4174900300160010800d0604007405035002030703da48100c1e23040b20b4001d900030840700e5001c030440c1445480d001102445604041130800844103a02c60700f0a04010740d12600e089600701d15040e800c3e0381c0d003224041e2054005200400203418540c2149111a1140f0107591901195500083d00d04130300362002da90f10b521159042c000c01da040240b040c040e040807151a0070452a900d01a03644040d680041004250103400c1119481d108008201e2142e0b4007030304202000a0039500744419030424104207118003000442008211724003d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 352551735 1250 352550485 352550489
    0xd140c0139020c0603150310020a0206070804031e030603061a010e04180f02060405190f1a0a120621061109010f0e0a030b010801050a060b0a0c170f040b0706060807 72
    0x90090081d00c483d050070481c040e0001004024105058401e0550760350b42803100406d12280840c0051b12511000e20003803404800510220901c080c420a100c00700b13821025042010011442c40000002607050840141c1600c1d40014040ca04103181540c074a000c02d200e140880600780d0320803800010210800c4161810308811a0301c21505c0052040403c4500c410720040500141c01d09141c180d481c07021640d080c2e845d600c51a02c00890030b80501c45254200e0010000300b80c0d440c50401c02c9904202c4854061098440036001e21410f03c50680c10380015400480c0100710380e401200c0d12000100301a8114105108120b0f90545880990b42500303084500b610808081a034481d807054824560035921419840c1030140d200b07a00c07007800000500c986c0c0d050b9002c2d1040d180042480e0070a40010001d480050300714400c0c10340301388aa41d564542c4074804814035a0464041c0c2110081d110301078a50b03103d11408181c2c10170001802046204c2050001c003401407155804100321781d41c804c851600c48401d8 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 352552985 1250 352551735 352551737
    0x10c020624030f031303060b0604030c14030a060606020a02040b090c09010c03110a030c03021908030601031802041a12030f09060d0e0d020f1005090d140c0139 70
    0x201e40000c0500078107055086400003034101c44641c03010001c01495904109010303449503140003401d108200140c0269803031a0b20503580ca0341801d0856440080000b00d0b8024000c0c20103000000c0300c01550208650791326250805000c1052030380398003000391a507000c000300364011418403409021600f002654644180340503401c882c01c058840d001150141184107054040120030351845490b450244075242c90b10344a600d5102c1941550318010782803801b4174420b441107501050100c0042024082100da001c40c0910703000600f911000745041c81502e0700e40019405c1480d1104140707022441160380401c102d000c60b41640c414a218002e00d0f0f8a200c0d850480d200c800060209e40c0e61820a44060b00340c0c40181d0790041107445c03503590418609510b0382c08010050344501c41c031440c990028081d1803045420501e0500c203904c1c0c20002582d807541510b0220040101d0100e410105070380c1001030700c044946190080c8940c44240c1044007210424030348500c082c40d19038a03410655500071010742045152 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 352554235 1250 352552985 352553011
    0x60b091302090d0c0803070b060904050a030e03030d05090f07050a080a02010318080a09030314040e18070e0907060e0f0d02130b0301020409090c0503210307031805010b03010c0206 79
    0x18568400d40030b0341080024076003050380030300b844000540712101e0b00c0180020000454884003e810491100103002d00118000c4051109200c0428404941c0c0625540c050074080c1030840390342c011030301d0f62050751802c2e00c44d24a000148000d80401190403c6d40104c49800c5a1455854001b04504070b4000d00c0307212072903440b00c004480154020f801c0340440c088501050140f1603100d03111182c1c1c41d4441d100180c00079070003100910415400055540c1c1d504032080d002e50921b81041c006241140c2c019200c8009a070000e43c0c054034000b000c00c49a0060007000e42e110041d41440580560740d250507009243c041140f9502c9100d003414038150a414080c1c004000801454044d0284910f042c9a00081e040c40398a030319500100ea01c09000030130003001140c400217402c0c4042c0c140400800c296411291081e00040800303065545181c40c00d064400102e00c0590b560740b200241903004006275020401d450340d183e440030040c400198841994840140c0007401140c16000080703890300c100b11669442c100d8 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 352555485 1250 352554235 352554259
    0x40b0c0412030215070219150f0f02030415050c0706051b0c070815040305040506070c0e0114090a053303010903050705010e210a050702030316020307091a0f180901050a060b09 77
    0xe42204544003490321144000727211411001810f041d80c4480003c40030b420f40010a000c00c120a1400700e44000a10318001c205038205914442c103940304000380507100701c0d2900042109c0d001c09000803200900d649003059990454808411b890341039620a00c1c0383c27806070b85c0e049000309140418940c802c1e9450303070310b140c0f515007403400b04021038200100c00c3c1d41801400c40045803456072001d8040c041e0128208901a01c40700408105040c0001885000d10307504060610030b02e020712560324014900440c10a0010320344c200004080f06141002e10b0354107600308807421052580000061007410b02510091040d1007904c003d0702d6607021071aa5840c41100e0b400c1c201d02e0450285005007608405c3d42c58818945805900000d2864000c9007515490100c2500c4590440c0b070100300260007440b40e9041406000502c1181000429134688140c0c052101e80761440f980b50341d01444114003184c5c44226a4840c28043c00c0c1a00038030040325416041c0d40360800108019070014142d43c16540c0041182e51400 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 352556735 1250 352555485 352555493
    0x70c11100215011403010b030304030507032301090f060b060702090106050306061b010c020717031210090f090302010b0a08030304080c070b04030f0303180b040b0c0412030215070219 80
    0x400003210520450090309008000a00301c06a024001c0c082d0300100d400da2601e0a00305401c5901042c25148a90320400080000a4020441230220b90300800c2080003a19410700035444411842c0034204254078084400d000c000040d404841243d01810b010800d1f41c030310005200040c0316000c0060340c085402001005003a01c00c6000b958011005003006050100000515100d4116000c4010969440781d200005070b40e410031285000702108400304e05102d91910b4059280d100da4503214840e0b001e210300113031480d030a4136882e00c001c10050808214801a15281c240100850302e4228019420244080a90301e00b000402040d192004046c61550302c5640c2c550344180e10041c0e445115000c0c03840700190b65000e04c0c000d480194015911406441c8403494000c04880410816201c03040e0440080004156807a40065200f80d0000e02100340ea01c54019080c8140503030340c0081003860848118108041d408149480e5105031442c1d00c0ca0641c0341c9880690319001a002d4820f00c1d0f1120740b4440d000b02d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 352557985 1250 352556735 352556749
    0x60a051c0509031e13140f0925051926060f1c0f12020f19030c060f110d0501090507050304030c0c0e04060515090408180102010f0f050103020306070c11 67
    0xd040040c40340d03032078102c00300818030005d20258000003072460091394000780b038100380001c440da50300d040b903400c480c500d00201d40080410b080a850b0310845144058018090700600c119a019203d483d80a4446007001d0401002107290f004054159001035000c5205902038404003070045030010502d110608030b00040c40101c410032000000c0c8240c0c14009600482c407080d5141d01e039240a15084038805c00320703c1029142203150785540103a070380302e260101400c3c5c55030720000c2d00341981407505030b4408109040c040c0c00740c0200d120442d10a07190540001c04021640d00600c07030007130303544004e0010b4ac1e030b01e800001c100c3c1c404650040c00305008000080000e841655440b03240d44c4514440e203010303525201c2240800c04201c1e0100c0303003259210300303108078041d500e00040c0c1506002c990115003454195038840700380c014038240741000074000740d00302e400368000e40060030700c042240420006110650b5003400503200030b110070380c02801100041101548240341019205401c1509418400c0c40c0c04280044 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 352559235 1250 352557985 352558027
    0x6240e0c0a090317090118030b06060a18080f010c170720070b0d06080a020d02091e0a0c0908070f0b03060604150309020411070c0e15060a051c050903 66
    0x10802e40d52008400600024140100304d00c680084503110400b510000d0300c4041d91030030403485408110420000608400d01042c1d100c41c041d90300503141c41e401c6e4400e591030301042c00d0700b41084603246008582e07490009440412a08010002e2200b01c0c0f6051050b290284074132841300505a401c00081c0c0300364011441c6400700c0ba0f2420355081c0d032514280c0424144a06900581180742c0b00080c8024480d82e00c4c09500050807001e0068504688103500046410040c180002c5c0600e0705040044c82286a01d840000a0f002014140c9480c1c907002034a00300a285141554000c13a552034130100341d207500040e004040e1071061010940b01802c1007046110b50300000e004603403100003084041105025107040401d5001151404a070b55001403040006840300380074084800704040c0071010100d244070032110115480c0e5141503565480b0480f10318070040c50602d056400a40c00100b20001e40c2e072150003081011680c2c00c10720112190f12014105aa00c240e07142007882e070040c01010b0400c0c105036200c0003 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 352560485 1250 352559235 352559237
    0xc040e03070203070303080403030b060405030c010f0306080a0f021008220618081305040b060a2a0515010509040f20120304081902010c0318090906240e0c0a 69
    0x1003000e807154000381c500070258000710002442c0398248400c00d505805000070313012044030440d06082c03c01022944e01d0039400e0f000b9040003800c2c10880d4001d4060b50011002d0002070003a80c06c112042c1c00c168500480000d402c901900b00380010030704c0c0d2031044100902907210b5881261920303a00740340c0361a0300030300784005070740040d030324500704520314022038810503260320966410362607600d01800a03c01003081d030701140c01399050060403803455403480300716400340409040c901d58841c001d0510014074280c0c04d03403110812100041c1d00c2c0a000e0000390b0465032801004207007001c3c0ea243d10500c005038409a0700101000f451030301d0040002d124104040e69854035511000020040c200000c0720904e80c15400e107181d8000040520911400b80300042c0070807000e100e0f009502d103555000070309001c2801d1000d0200320001d912080e10001642602e0000c0000781001e00221409060043c000c07c3c0710300021107001080171032510015032050300302d4200d408442041e503a43c0e5a00400c02002d42c03000203084 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 352561735 1250 352560485 352560487
    0x20c06071e060f0606090518010b09150405030f0307140115030314090924031219140c010506010f0c200406030219030605010e10090b06070506090604020f0d03020c040e03 75
    0x101c84a0128030848009040c961b0f0386d500031901d008180800304c82c807050724402c114000d40051044403100c5040700d0440301c080d20702c00b80c0409a42035007001800b45030080c50b418081c40704a04000d500c000060001e05000704800d40b50100010b0400d8201e0310f00c05d04602c01c080b150642000441c0c0103266401b640310151134060f242150003000500d00700b10448000510041a48a005036414090100000820260014223100c1c1c07400380302421301d000d000741c0c0e0780c8215005803024102c0e0b0300c90400c02c040142c03c42e98040c0c540e103031080414060710084030401c0c0003800c54013817400014400e41c011883e040e040030307410000302d1129500c0d180711503d0821658200d500c1d080004016100c917509920a07092a07094040c01a007185810f41c1607500c1a8001d1010190103402d004502d640b080040084030041032001070001001c0d4042101070242d00400303003540c000c480400540d080b0100780c079489284226080b56090051404200171039040c80c0c40980180d00c800e95130701060a207035100031180b0f0060070440b = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 352562985 1250 352561735 352561751
    0x3060f0312091504080a08130e04150c0f02070312031410031a040809091815160e030312060d0209150108010618051c02030304030521090114090a080d030c020c06071e06 74
    0xa04e9100d502994111540bd15801d5400f04055180c4212091840145072402c850344480100a6407a140b0307010280805000c000080d012a00951229500c0318040044401500e4003c11004881165120654080403000040f203921a4401c110a04c1076078814021810216200103102d040d4100421003510702004d007100d00084d0718100001a803041280d60844408c2ca0042500f035402381d8866104001e00010181100d0280c0d80032040c0d824000800076034061640d900d000207a110300c11b00c00042d41050410341400705a01c0002410043c0c0d00f0b080c2c075504501d03603a804045581c00c00f0ba0548241100300010103200a14014000c01410f6800044880000d410303074002a0440d40f19500031079041d88501079240040c0307180040005030002100c0800e041c64292000a800348000e00c1402c000c0440008a03107030740b90744288180cac0241944008442d207a080c0d0840c040c1c0100026040400940300d01c9107048011700d0000103c03190b040e030041c15006151001141c4908192007114101e0340c0d02d49410704 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 352564235 1250 352562985 352562999
    0xd0203040c081009140105060108040f1109040303061e140609060d1a010f05040e011802070f03020601050a0b0316050a120207060b0f0d03020d0503060f0312091504080a0813 76
    0x1500740900020800040c0044031485d100b40c94411082120030750343d05200400c0f890f82e0f00321203031039882904200c580407080414988030f2074000e0098403546d4040590b005200606a01d680040107036458180c06400c01d02104900b254030380030501c03600e1040c90b06424042c0c828108000500050380d000b030907450070300046da140340040d078501404c2407080765800e0b400340504c1c1da80902e084000d0920f82c24842d10301401c255241c1c22032141401214138040310189101030141050341200c500030b4102450701000c08441c54020348464007032140324492003520f2808144001101c045078007440121908504c3c0030071600040ea0349810030540c00040c405203100340b01c4a070700f00380010100d16224400004800c076010041100c4d1025040886025194440b505000031750000b40805540d2003d0801035102d1b40c44400050040b240c505445070140150007210162440e08000361218400807034a0002850030442c01072458000c1d03120750740d46584a020941c011901501c0104039030312038113104401c0941c84040b = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 352565485 1250 352564235 352564243
    0x2901090203151c05031b0d170604021e031303020f0f030702090709050a080102040302090c0a080612101125020109030b0a090819020d091d0603010204030b10080d02060c0d0203040c08 80
    0x700c045e0f100141418140c6c003a0405000303070041f840840c240a5041c8812400e07200c01d050000b0a4036000e0395000030103107280807012050240840303074500c00395070380d01d8546030716600c0000c200c0044000d80300d040b10120081d040403e0006420811300000c1d4102605502000700c58000a0a00d80600c41110004200c6484005841c4080d1481d0030000d40d54610b98070501450800040c00744500381e1003407042042859100884641094044610740c0040e01c04480781c43c24004d4806065001c1e40c68080d40d251002c00c40000341001c2a086000242c01c20060800301200c81402c2078000d001030008041407002451000590b44c0180c40594009082d00559032900115840050403080703d80b107070f50752000419810040c4000401281c94061031013880d0003100b41d02c0401c8000c0702290031f140d540000300c59880943c140c0d8019500101c0310754440c181214004c1d03001c0054004d103400c038000d21412011550000403181d024041d08807e03c0c1c5401139a050180c000d4001820071113420030801000140a44200 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 352566735 1250 352565485 352565497
    0x15122901082203050a02060a050c0904091505090114010816170f12090f0d080405010c020103020702090a060e130b0f06031e1609060e04030807020a2901090203151c0503 74
    0x30302c4581d500c2d40c40d810040c1c540980109103140e0fa80c1440104110ad51015003030b1102c00d03205a03401f240340c00032864429400039200d90b50b01841803802082002c5094150001440e40c0314480c2159451790b2140441c586a400702c0410200d110421402000351409040200d0592001c04084c1e55480418060803400d20a0503046081c4010011808900c1c40c40e041442100b84041120b0b002d540c110195610f10a60081d0f210300c0341881440c0f4007150959010380c0454800543c0101000010300d040005038000b40307a40c0c00394002c0306103000d00082d0515415114144c0d41e9410000a849a6030f0b02d501c00c0c103020038010030194150040800d024084400c040d03c000306848080081c054900014031910813844a9038406842c050801c6000c00c2254194143c0035009a0180b0780742c461340e40c9044d8144d292000000004000c8410080002001528032000e440c280119080651541c0d90b60000c407000c1c1d0005403101e45080c1034000e81b4104515024211043c24402524400c0c1441c607103807503203401c54001c4 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 352567985 1250 352566735 352566737
    0x10c03140a0507030e09070c120201062714090a0f020607050a15050601020c151803030d020d051503060f04030212040b03010306060b030408040605070204020415122901082203 77
    0x2150002c10945c10100c44440d5110560b40786441d85080700000702a00c0c0380b40070107440c0040c1d05088680c81ca100b0b4028402920045040702d89805402d01003035941010203c91403c2589404444480b07015018070040c000c1100c3c400900d500c0e0201d85402e06410080c0e40100c0c1d10000c03c221f0803000640031f00242c1d21180c09101c403111003404c9007102c81c040c0c410040c002070464000c04c60b445074650740d08041d0044048103451941d19090320000d40c011310740002ca0425813511002c03d400c10701e48019001403540d407855200900254852000b0501488400500c00b58190000340007d00313002091004c855005020707204583c4054003c95042c1c800e644981c20407840f60400100500c140100c60041a00800503811580d01c0c500c0c00303848501c42402140070b51000c000300000c0e060159075840c0c040c0d402403c180400c107043d0440385000030b010b41501104040000d0300781080040c80030311001512614400c0307440e01194000b0301c600115540307903000705100c4020003c0c200b080d00789a13171641d01c00140c03480f03 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 352569235 1250 352567985 352567987
    0x20102090f220b06090402070c031115091e061b0c060403170d020702130f051303050901050c0307060507050a08011401020d0c080c0604061523010c03140a05 69
    0x31030018807903465403078880140514104a110304585196414040c039034620948009003980000000a500d48103180c3c009038441e00115803942440325400a03902181d225000440c0340c40da096040c8040c48118100710109924144941c001c541007800144480d0304107842c1d403200e2012800005a00e81d0416007510720a458001d0b40c3c0d45079282c04000c00300ea0b4090881d0500e0626255599485803a0780c4e100100744014008506c82d03e400c01d244c0c040d40d9107564001d20700496a05214600c400500388140c90807a118182408282c0640d8010600c28006400d030f034400785400361500054810303520000004a50740300c100001004101140700d5940246002e5803150f64442c0401c40c000c14008041c0c1104101c50000e008003501a070300000c03401500300090500350f802c0501400e000c0e460307000d6005e1010150040b0780c10482044a9030b445508201d5002200f846030f5510740844403104ca1000e45269000c1d001c40703000014540c0a8030030400503070f10929060811010005407a12290803140120307000c036030 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 352570485 1250 352569235 352569247
    0x102010f0f020d380a030605010605030610051309021e0f040626010501142205030708010902010203090904060902033703050d0903050c0a050f01050906010f03240c020102 75
    0x120341d0150302022021107800d505402440305900c2e03c000076140c0c4c0354a04845000008100b61a0100403500441d0444000c00c965a555031002e4040d80c41118803610500c198004007424034020307000e031003e4a004428841255081590b80e80084d4012040280d85c215a000c03819070041c180802001048400d0f064540c84500e0658060a124411410003076079840c051021146100c0b82c0d091281110801d1800d032404100d400c000124a10440d1000301c00c108a030410070405a84000c03410302194403c0d0121041d0320341d1020500e080310394226000780103070010001d0052034586500402d4000d070040c4c2e000594904194000385c91f00207400b031582d83c020581c1942d103005003061480c0026105a410741d04500e0140c03598001e10030f20070547c0c03100c15155500408010b140c0700b182552486050f040803281c083d0582d042031a500c40c140d0402d69041d41c05d040020702003001c0800c034181280d42000e01d045c00d04d4250391764050f5641001003240100180318202e201e080005000d02041c00201d9000140c0c0c41c1 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 352571735 1250 352570485 352570507
    0x1121107050607090e1506090a03050c01020f0d0906030b0402161209120201140307121817040b0a11010e1b030c031b061612020f2107080304020102010f0f02 69
    0xb000100b282c0f042c080c0603041005607144003d8030561010302610283c90064a160009040340141550641c1160119a000c803c011001405110728442602282c1c000c81240d582540d0340e1070000c1080c0001410840c003041114042e800c151040342e0700420143c1001400715103103918151240f402e0b0b84080c440382c440b404d01900101c45002500d281c4400004190360358001a15885a05000f60000100000042d4100d0300c17500000e02000c4a0341018002ca00d162840f00d01c01c101103a030f05940100701c2e00915000c00c003010044071704580d80c40c49001e081c0106007205943c2c0c00341344030f01c82071a55213079032000c50800810320214070415429280c081e0840160350925140c0540b20061a020317512005c0948a105102001a24102803c880d401c1da581420004541c00003800c20000302a03090b200001c405282d00416081e0100b080c03401211038000c0d505c0e6001d0b140d06e500d120305504074642004035401150b41140190351190060001094802c00d4070014003ca550002803111000c0c0d010900159403 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 352572985 1250 352571735 352571743
    0x207050102090a08070803040608041a01180f020c121b060a051b18090a0204090608031213080d0f11030a091101020d12020c012007231005060112110705 67
    0x40c0c13082c400240355003403e06070707029628840c50007000d0901403440001420070402072a075804480c3c22407441040e40d60741c1c030b20020070b240c403a04245282c030382428202030540e0b6080c402d80c0c241c40160801045c4c02c0304000c14000d41d5a121158000e10fa4400c402440b40a01003003040da1300881802d08006250f2602c2007481e040282c0c0c46410920f005400c10250030b8144040311160b500c090121400c2c1450780318609004004e21a95220303455140c00d100d80082c00d80c0b004006002c140d054a04c006181c0d80c1c4800e823a403580465214003c04d0b10b80d0502003600080081d03407008030b8800e106400024400380c40d040d5000150012034906003621f4035000c8050800403080d0b503035260764100b80001d190040000c1c6001c0d0411500300c1090000c0381c1d000c91107020b030505c00d41100050f4081049003854183c01e00720000d075a070340030f914180c60103507610034800c44a00181400c005510b100102800b0503142c0c400c0400e015104c007400d00b50400000591a82d4011180c0c400c42c8426603084001d503a4490f21490100d042c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 352574235 1250 352572985 352572989
    0x6070e0112020f181306060e09010b030103030207170a060501150f05090109170c040204120b0610141608220503070b0a050a0201060b0d02120a0b130b0d060207050102090a 75
    0x501d50052000820030a612000d8a02c0700040e0080c010b0040000400f0800043ca01c81c0391180803814003000080d1035802c949034082c11f000c19149910980c0c2c884191942a1000b03200043c0142d000b02010440400314214070404118a41c083d1008120585c441c3d00c03c0d65400e0300b080f00c96200315561031035019001050f4002031001414060700b41006240068022801c038810007981c00c3c20103403446410300b0b041c0440039405100900841d04c9944821080c1e103d0024200e04542c20605600814400e01d4408061801400b0613561007400c01405003209a0b150402441640b440b003190801000050115000d00848501e8201844c2ea040340010082d1003002240e0185000360840d650500406a40000f00c13800808541006135445030150b40c22401410180d100318070b08440494091140600e9070001c0010715001100319646032103601d9444200da502844240e030102195141902e5000700f50400e00100c0801010300031b1040c21601e4141c1039070b000c03210440f040d940c0094a0b989601c0c1a0280f480 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 352575485 1250 352574235 352574267
    0xd0b040f06061e020c13091e03021005090a0303020708070605160e09060d0f170403050d030b062b090f080409060e010303091a040902120f070c0203070e04020d0506070e01 75
    0xc0f0300030b91450040c2d2201c45910099005150318500200004040c4d08003682869102e000b8016010b00744030410b01810b10036004500500824080b450002141e00485000d0003c410107842a00350135941600250b003d80760031100ac0c2c40500100d00070a410b4801e140c8903203500320101c800000324100060540304548405c6101e4081481805240d0300d80c200c030b000203194000748548100c4401c0c1001d001038001401c1d0710500c45030001f03000c8200702e0040b40c0c0e588511030984040c0b00401d41d160420940b0701904480c02142c00c55201c00668014070011031800204c0f881e0000034070184207840e4600d82030b01c0316600f40c400c1040000c040018031094810080102940c1c09480055415541c1c003d084500c544140088602c3c031030f194081200098003150000d0031018021036032440404400a610300e0200c450700404104540051502401504810340e203550040103060010300f01a4990410761001d082a82c000b00c107003000c0c000180701041883e01802d29901d8580920340d003803000401f494071031608a4 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 352576735 1250 352575485 352575527
    0x80a0c020a0510171605040e060a030203060118050c04061e090906090207050c0306010b07151103011e0803131838100807080601110714040b0307080703080d0b040f0606 74
    0x10030503071ba104083c1d80030b4030400c0143c0e401035103545000844801154002a41c14081d5100002c0c2c004007900d41560312840c891020302980e642e05585282e98015840350710f0200d0481349580c0d45007484a58507100c0350f04281000d540843d262901c01d000c17681d00b034101c0c1e07140303540c001186414003d0810085030402c008400038041c0c0c1d8100807a80c02c0901540d00c0083c0803449981492a8225441e08079a070190321090783c20761a980d440c0004000c00e44a4454140072120800d0003280a80001c42110500c2d80304e05a228543c5141164403a4845601d40294545540d10700a010900b5030145144c520f00e004d9011000140a800320903420414624000e41e101d00f205a81082000b604414400e40c001041d0410391183e50f188001a10b850b0329031510301459000700b080104071194200f4001c2101780702a1010060030301c802060691307480c00fa0191102c958040b1200700000360848000f00b00d441d0610501048200700f00020400b95013035168103400554171800f06100c0c055102e000c1c20150003002c2c3d041 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 352577985 1250 352576735 352576771
    0x180901270f031d040203070c0b0901050f0105010f02030d112212120e0312030106030c091a1c1a0405060d0f110625050c030604080a0c020a051017 64
    0x1030740c50000300c0c9000805002c3d0801c011001c1e00344104401c110100003600a40d500d20346000002c141090000080360000d0402000c100401014440e191090040d0f000d041c003941d0a090041d43d040301c0e094411421480100102665002e85006241c0d00e800130b4110780f911150303040007111281c0140c0b410086041610721040110041c030f903460303000c03142c3c02c40c0e014101586140f02c215044940da13052582c01d0702c2040d0361075003103516060003503040311510f503000c0205030b00c0796100301c0302c00b8224841c1c001d50161100702d101038241008014140c1d82004542c0b120080c64682108040d60003055490400b10582c6e0000009403c05002d41070b48408100d4842c0e401e504260b039512407161601d40007034000d00c220782100501c1d4845600702d42c100103000306c0041a07003940400910310703030324040300403142c90041d07003c00066400c0018140d4083c9500014541c02c0503d40081120040040003045e41d0042d8240d42c0042e032526401d420601b440955541d003212401c4189000d2501c2801504402c0024404545 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 352579235 1250 352577985 352577993
    0x12060f14010f0816031a091008070801020702010e042708070c17100f02090402070c03050d0302120a0504050307020d0b09010507050906040501050f04030b0f0f0702240618090127 78
    0x450b40f51005034100020b446007040f0009907403d41b50b0040580040c2c1450500004200100b00d4904540500c2c0413210025240c8211500340e0040c150004c3c00310f0003c07400303603800380f6042e000a100c01240d02e50b00e00180c500060425200031140c0d105850301100064200b0521038404010303400303000b5105040440510b0201d03120794a250050b44080701b2a03483c01c0d240d4030750120760103e500d01c880c000c5c015901d490003800c040456003500d10040b41e55200b4000e400300021700030b000352000a07d2401d10800540c2d2204101c80240400801c104c41c40d00041086400691728610040021401108407001e1803908656050071640054154000d0040a00c01c145081d517504040700c06407002868000c1d150f40500d04203c1c1a40120740000300100720340d800300402c0c0d075023044043d4420780c0719404406150310b50001c107a0320382c0d920354503460581c00c820302c42c0c0140790300c440d019541040010f07140340d0244143c401c60510007003082e507054410341d4540d100c800e0000031301c501c000350400d00702c00410b18114550792 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 352580485 1250 352579235 352579261
    0x6160801050118050a060203040e13020d0f050703061a12061014031c02210306090109050c0c01060602060105030c060c030d0e0703080c0304050103290112060f14010f08 74
    0x120715030410a1084111980042d0a24404000c0101401008001d40c42d001d002c0d450b03030850f01462a030842c05c6c0000821009001910440e125000360006001c2c40303154403030850400361044266402d01c0351300340010004415101d03242e20b21084802d002130043e449020000c1e00140004500219800030050128079200c448242c800c689000c1c3e028001c1200003000300342002c08080e4000e841c9a4490700390485185c0100d04280d081ca221181d800352104e0722881c0d00f00d980402c1c0e52382030304600e0920042c0090034003a449980c003d05118151b6090484401056096404a403c6500107030000b50042105090401c030300c000e00201210043c0c280040e07141100d540380202c0c040c080c9402c0d00c64480d402c518600703200030005140c00003100c035078804103070941c1c1d603a070350081c0b00f141d0001c2d180503640c0001c240c41c0c2034215420740c9090a80042d80c00000011a9500182260001c00d01e076034500000305d11410280340d100034280707040340c4068214190009442180500c1e6100300f44803a6104004601d442c100d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 352581735 1250 352580485 352580489
    0x109050d0e01230a08070810091a0d12030b03030702241b010b0a0f030b0714041e08060709030f0311070b0309060907080c24070b010e070206160801 65
    0x1181c2404807650200048074444403100d8a5161401450110303101c0180c207000620700303c0d8480d05c65510584a41d40b0803100260116040d44140c0c02c44038092121140ba0340040380d011402540d403a4003408118006108180441c41c2111a684105800701e078054043c007071034070555401c034061410000541c002c181c900b0104824104480d25041010203001c4492041d2043c80c02c0c00c128106440e2003401c05035008249031b1075494031070005420002010b52000700c1c0d00068903480305c1f0005503900d5204045d145190b02c1850b03441c41480a00c004951880e01d1140281005003104140851903e41000c460030540003412030360402031000001e1000c82d0918a07030705140c6030306240c0505602e5040300b80a04020240e00090422003000060290880e40010707900c0c000d084c2c0905603184d1541d1010940d54443e90007445640040b031550b181464540d07005040503000d0250064a0f2401c102e503070f11680c402000b40c01192503105124240105036604000301030340708051f640c80244902d514500588040014 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 352582985 1250 352581735 352581737
    0x5060a0b090f040f11041406030714160204020a02030d0501090603120f03230402100309050613060b03010908120a1808030c07050706080106020d170c130305100207140109050d 77
    0x26000001c2d29281d550255910740e1443d542003214001d5a594400b0700e6101c1c0c4121060501c00c403151070301d00c1c581401100c0c05803150361680c0b01880303040b006209c003581020300750040b00080301801c1d8015032240d000800781c0a0b119405165038400c0001d01504070350040e00300307401e034030f2800070305000041410519a001c0e0800f0b040c140804003640d01d08401178031035044003000080450307074005c003d54142c6858501491085818252100f44800200c048482c4031901400c00d42c46100805c0840021020700701100c2d020f00030204005004201090a4400c010401c607680745c0002400ba01880355400120f42007031042206100043c500403003004500c01d03044000d0544500000401c800a21040c200c1d84440e511405481c00c2036540d4a018003254024030891001d030154480d07040a00303219820803041b2074900d1456203480e80300d03221421303115000541180c520501c07141c0c01001003801000320000c160044e490143c0e90b00050701c1e007414003444529003000140e0400e407481002800100e40c031030307030803500d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 352584235 1250 352582985 352582999
    0x51c0c02030a020603062403060a0602010c0804110a08010203090309040c0f050d11070501050708090d09050d0f03090f0806100e010303020613020418030c060c140a050a09090204120605060a0b09 85
    0x6d00e00010382c9444104a08861000c68844030942080000d000303035220340002c407841d02e00150349070b405a00b6629240c00000001c3e60800c00500040c0340c2990a103002c841c040c06412807903840340403d81c2203910644191045900115501c909450240180d8420140300c3c07a103d498214400c1e80130300980100000d2507915071320b401915001405941c10340b4642c035002002031016003480e00001e043d4020030340e0074078400c0c00303032041030803110740104c1801c0121403020b4041314200c04981c84160400c00844401c40800040110003c0d0b1541c04c140e21002400a40b80580201d04200194a14000103075014000c000885030041000c40c1e00420010340c02048524072014540d4203100240080422807e200d240b0b102030b2800400303069100140051191145200304a8103030400426200401c440440c280e0508041016204191042c80502000452410440d00c0e140e25035800c0d030142c0e0410b4000390b12030000c0c902c601040c0030307081c0685a003051046d00e80600c0c180c20302d81e1080c441e120781a60a801101 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 352585485 1250 352584235 352584241
    0x30203090102090604030615050a0f030602070203010b0603010602060915010303080a0203060103090c090c080609220302010209150903010510080706110f01060e1b19080402040b0d051c0c02030a020603 88
    0x100c203404031550300c08020b04495580c1d480b8030b0907200800000341000d48a042e049004261400c1003800141620a078250b0081900d1641d40e80001a620081e0100e03003654844411240c20348440c0081c1d4040c02d00f50700508680d10b40f13242040e00d4030004056000140701785c1d00040011031340001c0302e29001801c0a2006d6a2a51010010b80103440310010041403040d140c54001110740e2184d01c1182905088d40e640c90082c3c03106410083c001c0000d496005c41d44190841400d03502841101030455240300f07000140c182040d4100052500d098440c87c01c130b01110004218155242c2072140d00e41c010001c03480700c0c04440c20682c0d0b03039580e40c10b20b024500c144001c880030400c6481080290300740d81248407001f800160307150f0b000e0001c01c80c030030b40d4010050502c010500c00000814000d451500a0340050070a24040c5050304442040c00a002a03801661f507911001944d120f60789501c030f0442c00b07500200061000d80b40d2146842c110103000313404010172402041c00580d8081a072050032901129803544a403 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 352586735 1250 352585485 352585501
    0x3010f030510270f0b0405030d0e0a1e0c030f0506180f1e0709060902191407240e0606010f1404170705060301090e01050c030723090303070302010f0e1507030203 71
    0x1007807524000e49180d602100701b004108001004201072404041c05018030304081e100c0580c2c81c2d0f24404000c0c00d000c4070011400000c4074942c2601d4055019118600c22543c0c0da440d03448140300e0f185020380b283c0d0045003c000924440c448000002800f981c0100700b00e0080c5c01030319480301000b002040005c018084c0030320300c1e09030802c00710b0080c00055400300400c941d1589400c0c0250f00c15005c0000d01c00ea52018043c0490141240d2040b522024500c0d03407814202e86e40d180782301003d140101c019111420710030446041c2901c108030020300703013000410140c14401d002502540014080004000402e500c945800c5c041c2e20980313044506030f2030500c19448030407121074180111508100d4111101100005905e40e49811640f00380690000030089600c410300200d0140c4021900c810110702d01120024481d008116040e00080c51a044641840c01001c0003c0c1140d00803542070300140c0d107809d100301e240c481c03c1c803845000f5268000104211740e64544c1044100030000d05031028140e002c40003030504 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 352587985 1250 352586735 352586753
    0x1d0a110f1207030c0515120606040905090c1206060604090207060902042d05010e060d030c060f0b18011d091c030c02100b0a1503020f03010f03051027 66
    0xc220081c4420394110142a560b9070311841440140d88100e402600003400341002d00d4000d24403954101024a0091030028030015180003818664100070700704000110a14140714280c01000c4c800042d0030aa40842c0411464a07281d0000500c04c2d007014003404402e1307880070201c9048550100c030245e1203124a0408134010101c0c0c0501039006420308103000c100e9010403188541080c05c59208031843c0c60064145000c940e0240030300d01650f03010002081c0d00e031030041c09085e1454030070700d0000c0f40c081035075a800042e40c030700010701d116164440d4075085c0783e8506243c0014000c501c14901490961510f511524211107205541d26400003440100c0c140207030512190445406400c03a0007507110711000001c00070480402c0100043c0642420407a4192541c0074884070100010f2a064145040c51445800301d4410702c1248140b41d800c001e6410300c00002c6001c0e500070801c100d200244c0030310710b0811605185e01070300216600da141164610011034030071040900c0c1c071081120099246540d240c09100 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 352589235 1250 352587985 352588009
    0x4060803040909030206070201050601020a111f030608010b030303091e070909031205010509090705060d321003080403080a050f1308010605030a08040e090a0f030509041d0a11 77
    0x460000041c0450740000b81d4003e10516807195089540c0c580d9042c44c100e08a5a05540c1c03d40160811342092010070b1001c0ca41d1030080350001c0a035592151f4070049a4032020034070b492040420b490f041c08000e222820b101d4502c2110068026500d1898446c0103075071070b440808907109150021010702042d22008110100252105080c02c0205003100d040207000d5004950900200502b002c0020441c0d041080c01603014110100062104505220802c5895003100c901c25020035030310321020400101030400b80e0b0349288034444040d00b00740c01d140000f4221b1402407070100c1d40c0c824002c0820000308400201c0b41182d802c0302c2070a403109030604d4215568880c2030710202c015103020417040924103030b04080d6021603034204000c00000e5661001c1c5901e41c80c501001600c01c000600c000c00000700809809a80107107800c05503105112180e5544218050342c00c1c060300042c4022030302d4611070400b8032803d400b0040e120070b9680010030a024242d40e4558104004200c224448002c981540306c131008800 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 352590485 1250 352589235 352589249
    0x30a02070611130f1a0316050d180203010609050105090c0a02101a21030904090606080601061116050a210803090c0103060b12010509040302030f0708040e07020f06070e0406 76
    0xa0740f900c8520707420000079441d01030402c0c24000d0103400200c10074040003101e81c03c0c50401c40c1c4ca00f5039403048100100f420000d00d614061007010055920b621040b4480d030101c50054104551480d421401410300f111059007040000c103103040b006010664940d0007030751313100402e012226518030381403008030300b4400481d1001d88100e05042196041d128114248220341c0401e0351030100802100b880e603138407004401d54000050f08100f04101160810b5004414054010f0202040b42a650000c50386001400d0740240006810126406807401043c0704044140c0d401a00701c4d05901e09003400900350058a02c20b00704c012080300702d00b40518200400c400041a00170128a40703070300c0c240d00b625880c0c3e0b80501881e07000038075005011540080d0141510b11039440782e41480c0840e0308182c10f0040c240000f034425015840240445403510448074000c00d9850b01c40d06800d515103103000400280c420000d441c0c14259040107203c9480c0c15000545c80342e0001480c9003507e6410b4030003000c00c1c000e108a42100c0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 352591735 1250 352590485 352590487
    0x70308210c0c010c0e06030c0c19030305070801170c0103051812090f0109030c090b061903021315080a020a050f0d020c070b0c190212060f040c1208030a02070611 71
    0x3190034100042c05002004000a02002c00160801c84200b180700c12084d600c002c0a00c041460b4145602c00741800440c032008032540402041401e413032000d450388003100080e40b1202082840c1341e010304220300400340001200d00c03680014209a4548540d0010341d41003550303a00000d0669159440410ac4145866080d07a106403202c0d00016450b034080000e290007014458194900d40d489407800400b2607170051114903c05041461860190882081322a4040018131135803007440c040c2203805030f081406860050b501c480308020381c00c3c44d134055404850a4070002c460642c0994000e134143d6400801071000580d00c16200c00d05071800d01a0140c48101e950f804254241c64001540c0141049420f4a084072520f40d03544201002c3d9118000c0c4000440e08250640c840c5c3c040d00403034030154184002d20481c144040c00310130f00c0c0360030030449020701c08602050900044c00301c074882e01e1010300340d80021481c2004d00340c0c0320310307050b48006411404100d5002030444148401588101154160481d8003 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 352592985 1250 352591735 352591741
    0xb040507020706140a021c020102090319060b0402070203031c0e1509010b0a0609030f05240a0506010203090a03022e0513140d030305070309080c030d0510030507030821 74
    0x290b81d541d0600075580803c81000780b00f101d04600302c3c1601d2080305203a00401002c4807114881d90a07038010910241550340a2018001c1564103101c075198800400d0101030107454982000710581c1c8440340c40c45d0207207204100c05005603d01108507054111103044994003800d00d80394000c0185506060308811b401040107521501038098140c2d4050041c2030000d2001c2d060680400180b00420320a04011803010101040000c42d100701c030100c070034020019240f070307184111700140240701d02140008424103030300100241010345200c2c168208100b0310056041049240c003041080e40c9901029108114602034804490381110381421040c0341030420303040d2000812000340290b005a08903a0541d070700124040340598001c2040c00507030384010211103442d400b070303102a00105000340606040649402071000400c078803c0040c03240e400c2c0e81000396900c09000d6001d800300c52000d4401034900080d0802040400c01c001000015a9000031f11a55607444031100c5000c4d000c40200c10041480c081810 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 352594235 1250 352592985 352592987
    0xc0510050106021605030705010905090417030c04081527190819110a0605090f0a0b0a0b0a0b0403030f050c07060c1a0f010e0a0b040e010204031407030816060b040507 73
    0x1002190340c942d84c01000d1141e180c004040d21010307070b40201400560724601c204001e250030000550428040d1005404402c00750360130f058103500850b4001da076050700040400402400300030400f52103503a14a11840c2d4246283e8056a9070f00c4000108400d0b50952040c0110304014080c07100c07101da100d400c0c102c4441240ca0161031603004500c100f8039017060100607084243c06080c1c00130348a002e580141051080547e1039900528020b010700510344075554020349041d60401000080303d0050143c2d001602c0c0c0b000001c8141d485c1d02250710b0050011690400042041e0320942e01030301d40c541003400b15018407110490300b40c00740d01b000340410b1003500707000540d8942200c2c4043c0401e00a80e040031501c900520407022074182500e20b0f2000011540040044140000405070403080160002c90106041c2c0005010340f910303041c40300441e942c0040c0400c104081010f2b0410600b501201030070000f031070764858612078050100c5e42d140100131580e410003002115800500500c0004000300898141060 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 352595485 1250 352594235 352594243
    0x15040b0d0506180403080a020a1b03121803050d05060d0b010f262e0c08010807050103110706050a0219110607030e210705010219030f0207120c051005010602 69
    0x2210703070050800000d6145a0407010201c10711480d0140c1b640103080d11044d9400c0025400a0851030400407014041700c0503688220341c1c4030044c0d000f075441d05c20036a10142c005044444034030324a2a010003203181a0002a002005e8401c244d120041c001250b03950080030848420200c1001090304030100000300340110600060780907104200162294125038505100c50b282d840c6030034003c1c80e0f1100e40c080b8070000a03001c4048103844145800309008601880b128280c2c2c0c141840040071504c114018098030004000750340041c6407d00c0c0900020242d100c00e00ca10f40f1542c07102501c419100d000041490f00300740c04540d0340e0209404c15504000b55641c00034000e0804110300b55075030140c2c0300410100da109024103852000d106019280c080c10b00c0384414120030300c8610801680ea82400a80041a0302f031000c0c100040313000c04002d07507a0345002e2006040754000305042c00740700e00c18400c402c00b103200028181c490942e1402c041da5400d405c0d042c1949030024140c0310f2000345040c03900220384a40d000c1 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 352596735 1250 352595485 352595491
    0x90312100807120c09050901060305010509070815010501050f0d0605191412061825080f0622031b1101141602010e18090a020108010e0609010515040b0d05 68
    0xc0c0d62042d82c41d40103901400d110706001902410030190140304016040e40000d030414111000065000c0d40c82c0e555909440e811560880c2c00d8000da4410003210109124407401160002a0075829604280c0040d000b40100032003000e8560000c181c0700800c03003640e40258050309004003818511110005102c0c20030b10b00e8090b81c51207000c000807105840c2000300d0a20310f5481508080c112070350700d0782c2c28148a400c00f4020003005204103442c3c451803041c4885e001c0a1407400401c0941d085e8104040645048000020280cac10b034000780400c80d01015185070198010070420500303003900130b282821207010a40341710340020101d00ba1101e130200424583c0c0500f8841003038803800e25071702017012005824040e00102c460300c607502c400c0181c015807261910718031059000304020001d09000b0001c00185070100c410991035030022078110103540c0c20030001030060040398008052480c081011070340c1420107101d094000c04642403000001082d410039580505201a0070f40c0c0c54200d0a004140913207019 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 352597985 1250 352596735 352596749
    0x60a020a0f020c0a140411031303020105130f0209070507140d03060902071106131505030a1503110112020c011e06060f0c0f15020a03020c0606010914010809031210 72
    0x1e4214480070b40003140b1559562030080070440f40b00d2520900d9191402c0800910368050f41e84d401c008444901d00002c4d50182000b5000b05031b001c0824075010703003140d9020303040841300b1300c000f200318002848000c11424507036415a40c1482c651a01442034805010b6100010941c49000c0c00580c44048000341003200c0c845c0690301488440d0307480003008124462070101600380b4081114a00d494206000101a01281d101c1c5099445030349035100300d54041c0c003011000c0080c00000c248604030380a4017481400d4054039583e05802c901d0361351080b42d4000e0388820681032010007807122007109401d074165280b03081e04400034800107915407042c0401c800c3d2101d024040c546003ca0114220344107001040385c1036880d0b02c6145180c0c4c00d58031180c10711030a00c00100d483c446042032940c15080710340042c240455142d2005622407400c52802401c0c603c0c0100001d04004e20b1401c1000700c8016505e11465006080c245110740d500c88054160840c46914202400a807100c0140181c000051544074125500c1c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 352599235 1250 352597985 352597997
    0x102061b0703050f0d09050706080c031504090515130b09010e060609040606030f030c0303050a14010b0a1205010b03090d090609180e0109060509070b030f0a021b060a020a 75
    0x1850302525100312102080a410990a211001c0024000c070003d00401202c180d440f8200303000b12426105a900100080b41c1c9600880e008015441c0c101c03d00e1504070140198150851070070846075038001340c3ca012050300c21030716440b141c0b0912100703120940000c040d40800384490715044252803504c05920100f2100c0040460004503050410701c81c0e04842031624002c0c10382038403441e040003144003000d002614665500c06001000078000405001d0592007038484192220392400c5c0a022508000c4c1a51543d500b403807810711410b2240310f1914151405402c1c560340381c1c03403480c00840b190843c2d0030f0310622a0740781c140041041c07d002d1b405148204070301c004030b03500e2280245084400c0d102611410002c03078a40030b02400290214400c050302d810042100140c00c651307910003582500c2603040e042d83c0b4030780d0310820b0050b0743c48140030420180680f141694a5418501c2010400e11001002c030a03003950b0210390140e00c0019141c55491410401c0e080329880e0905400e8900250320007030010000c200 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 352600485 1250 352599235 352599241
    0x5090f0d020f0604020409020a080d0206010614090a0501030f0b03070b040515160b06180a0509010c030207050604020f150a0806130c05191107061106010b09150c0a1e02010206 77
    0x21001034680d00b1181150b014006503125a4241300280c08132480072a402619018003041c4c0b620f00b000b003d044e444c00780d40100503d5140204c01341401c6200382006491f81c1d13040002c5502e130f4440906c0041150001e00e07000070003541e000610401000b08510060f454042e050b4001201400c4401420544a04588000c512a01994440964401d1540c80c40b2601d4003801a0030109444284207640035002070090001d5052540a01c0701000c811142050a140d50300c0620501210903c034805615416040442c903009aa4644a42c0c540002b08001d06c2000300182410306915003c1d00710042030303185070403503880f10301049000e04413090484080e40038034120b010350424072419004204410342e0303d0300d80514040c9000903014800e00f00145100610500440130003040c081000303d01c00800080c1c1e40c12107000c518aa03103908206040c1d20100c59803805101c03000d0990f40354440c8040d282d2244500650300c6017000410b506200400b040902900180100124041c011a1404200c00c0c400d03030a030307641a6 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 352601735 1250 352600485 352600487
    0xf0f0603150204031a04081629151306170a06050a020306090105040903091e0906081203310b0a201b0f03040803040315090f11010302070605090f0d 65
    0x301580c400070304520300c4141240c05c140302000c11990440d0280c81c01c6403904400031158400745042d5002203c40301c00c1400c146240c0f038113084c2d5105240c407594000710302d203090441c0241c07003240814050314481c035090300030b000d440e1880e0342c04a0b0048c9610603d80e05548051446d0940721503040c0b0050381d800341010001000e0715894422280705100c001c0000b000b603400c00c410304c0010240c0c00c1d004ca01380043c81c5c001003052a49501c0c030b0140c41d880154640300c028185010f41050b1202daa200d041980e000e00c040035008a08941580d61001203e00828200f098845e048282090705410039403244141202c1e010038848030102c101c1c0b00d07466103c82030104100021800d10303c5400d603a201c0303460000074400c8607006a0803031072048111b03803640201c2e485100c008502c02e046522a51100149500001701001000060080e905a6200b881010859032031152030b000341980107807400502110402100d106241c1c001d034103450000760404802c121a00d0030050356a51003041c45200c1e403813841100d4200c80d40c1 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 352602985 1250 352601735 352601737
    0x501021e0604030302070206090a08030c1b0f010804080d06061211031006081003060e060601020d0215070804061806090b01090b01050d0e070e04030c021903240f0f06031502 76
    0xc0e0000d00010300907980ca540b01200250030107142280c0c030020410500485940d411b9901c00507000c4c4101559990004031000c4c0c2c40c00c0c10b0902401c00e90343d4658030703142082d41c48018503207000780300382003170415961107181103603551068024540c00249440c4010031055440300002440310000c20040000f05010520020700e808116642e02c04c0081d0b00303c06000d840d12901e00d890700b00301c1804001b500c103a100da650b0710030f0f54035640c40605150b2011301040603039a410401580c0001c080e001078121000d8602060210200051a020a005200e400700f02009a00d610821502006a000c20400040d034642440a0030b16100240e0b07401481100114008285109081807800c0503141d181c600405450300d613026080000114805e400b402d01d0005140710383c884000c2c802c5100340d4411140122520401c000c80c00c400c480484d01041452060001445114144000c0480720211100403400030490760003a00c80303900114045403c0c21480c280c004400d40148080d00d203d042c2e10240c100c0701480c05030403 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 352604235 1250 352602985 352603033
    0xf01030b180607030e030405030f0a15050c040e190c0203030a050f0105061804090c24091d090c0604090e060a1a010503090a0206040b03070206070309020a090b030705120106050102 79
    0x1c00e401020101d0007290095101c2c2030f141107a18143e03428280d03034500180c140036030642d5928080d00402c00c0e4174200320400303102c0c07207040107194000c10840c1011405503000c0d018900444a0844e0080d0108041030891468140103014801d4140b11031003610344020340b250401da418620355401d00c0003017a488190640000c1c182c0310b0280ca02c170709000440001f607036440c1004040da904503556802040214403c00c50480c09002e00d03034007003d2104980486010000c0e00040030504200c1100e00c01c0c4500485a5070f4500313100101c5049030105d4950105d1682804110090651b00200018000940ca17503030790000d45c01040b07018103640903952218907581c1a1a40808551214900c079060400c1c03943c05600a1504108102c00301c40350300c3c4c2d1590101e8040da00035002038107404030100c20092502c1d0b04202881d4800007a1900b80603203903030790f40420241e011b213008011a036500c03200c4c4c0c0706840d24100301d10b100800c00148a0f04c05a1020f22841e4024000c6001d558018007c00b541210395801540750f01c62 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 352605485 1250 352604235 352604281
    0xf05010603140711061914130c0902070b0a020c011508010516030615050c1207050c0f0d030801050f0103180b0a0b030a051203070908030a11160e060402210f01030b 72
    0x84d0b030343c50403075610320002c00c142d040645076560380548070000d02030480c840c4602c1541c0c01c414242380b603d0030700c512900360a40c0460411401045050b0000e140d407072007903400102161000d600d54014007001801341401c1038590080c1c5586000005001c481500442d008001c0c0c11520661000c03860011403d95000303004901800c40d42441a072020f070311520052107900c10312400d54040c101c80400502c5d0640c040b00081e107003a805504608104c1c60000d0b10900d81d81011038101d5002100f0380d40240105005100c1c0a1080c18000c032015240d900035000010327400420100d84074611040e00d0328a4064000f95840c4022074505111070489040c001050b580ca650031000a03d02c03040e07000000d42c602c1c1e000421050400450003800134200c0020000b8000301200e42e01d400d5080c525900c40545484100502d44e414000d003190b081144e02d940c00d694940000090b20050303903401c52681c402401103581261841d6070a4070720100b0180e4890559041d058034403891074821140c5881072824041c00d9010b403104 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 352606735 1250 352605485 352605493
    0x6030303110a050403112805030d0f0c060b0112111308030715090303061205010515031c050f070f050f0c0306040308011e030615080c0301090c15030f05010603140711 73
    0x8408550030340ca031401422030003418908040b801c4a80f00030200b1400d429415000a1f0204c24061440c040c802035542110502d851410004c0fa42c00042070305650013400740c42a0f50700c07454064240d00c51040c18403201041c038818482a519448240d40c1d5a0043d030040103121451440814000004030843d07031503580020101003c680c5a00805004111146003201816540d02d03000400b0b404003040e204a05d4010000002c040ca0068600c1c0508842c00c8000c51094200300c080c5055050314102282c01144a403411076107070f56980a2207282842801405003640c02151007100c1000f100007042107102c8074001c02d0b2481095184181507a9902c1070700c008021801d03020040c00131890086060180c213141702082026990303a500c40c6c030704a400c242c146d003090004400c01404091001c01910802010550080100c00440d45071640205414040d5202141c541c41801c14200c0c8290003c041380c801c03481c4200b03ea56511140a402801e28000c4160b45408580014840d94098400002d1101c0d140c0064 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 352607985 1250 352606735 352606739
    0x90606030a0e061905070f0206010b0a03020d05090a03110312010e07030b100201020309010606020307050a060c0c0606120c0518070e06122a03070e011404051306030303110a0504 78
    0x411103400007040d81101c02e65807039140560b05010801603005210000f040c41d41c400991041d02c0507910700030900c3c030500c01c0310784140000313541c00036515044442d141c0841c1d848200882c0b046020717102c1c045200c44114100402d2200b0703a900420031200443c829181c00d0794000303420b44000d8980c06195115001c1078600401040501c0803000c2903940680540703000606040640d0018410142002400c80182c0d404400c10a991509204110280c50140010b608100b510f65510390f4420a040300140141e07162000042d51900032200440b0140d40034009101082c1c48580d5030400715004101070f40e0b905100280003410f400c1150b03120b040c0101d51040344001380c0c2e038010b05541c410480b541c0160420020407000074010031043e03000e80181d44003680d40320705a508010010400154943c0000e041c441041030040d1349800c0395450f104034900307091001700706003101c858840034007442c0d0090b070300102c0c80544a0705a400503403021082c1c80c0300342ca04002c80042c4c07003100700c9940101415000420820002 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 352609235 1250 352607985 352607989
    0x9081209061b0d030e0705040b0f060c07120506190c0512041704030c0f090c051b0a0204050f0603120c0a0b04060605031507030b0102031912060f0605040f050a050906 73
    0x28402411140001000500701400b41c510300040c8a4081d0300180d9036511800c40b82c441408428000e0408036802c1c418009014001035604500d10300f100d114000014801d020301070305221110080c0800306121414200b80d0910350b843d040304848200503081410740c02031040d50b892240341324610055444608040e0704200d43d5940c0d08003d801070b52918034100f4041780b840010300080000c0c0d4826801e20329100e00e010400141180c0c50f40050504030306091072951402c0d13001c4103403841107003d1070304009804032859100d410540300900c0650040d04080810907010503d003035060046606504031101c90b210022240e169008504152706241c00507030315200824008240550041e004000c009800341c1d550000a1416103103584101c00a4040020021491380610408820713200070b002462034001e8030080c42c489603000041000900040ca6800200a2440d0740514050004401c1114000762100720107420350f00315100341d035030140205601107000d0810141035021950040d046440d542c0711901 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 352610485 1250 352609235 352609237
    0x3081e220c08010609090204050a1a060310091a09070e010f03200403050105040317010b07020904111018050103090507050f03150a02091201021801050d090f050606010908120906 78
    0x1020784400c60705990101d5041400e2158500030401d02c003000485003004e1042c481a5080204115031a42c6031400c00701d81c5400b80c00380a0681c90301180c4e0f0035980d58400340e40380f40001454028140c02454010311620100c87c0043c40c0300c0201c004c541c1903540b03940c0c4440c00c5030a25130545509000031100100540c8941c003e4018411061003008104544106516900040c1d0802ea1003075480741e4454090209040d041102040c0401035442d201d004c960401e4a00221407003020343c028010000440002c3c14002801d0201401c800014020403420325141d0b80202030f0b82015610703030b010001888001606600038480c080303006034003070050704815152200704001c2441800308103406004101c41c40c014115041c00d074074440c0a031031400603211924141400b40c04031300c1101c00e08280e0302c10860715003e08044026180d0014003481d2141d5550f04951034071021389603501c001080302c221451910204030021800512440081c2c0c0d58400d41c1c0d5a0306030309507850900f051a0416603004200c1200507003170580c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 352611735 1250 352610485 352610551
    0xf0a14040201120507020a0f0b070f080405120901091e140d050703060e0c1503010e0c04081b010e040905030717120c0c030f0d090c080d0207060c0f0f03081e 69
    0x170040e10440714658880066082400c4022566509d1003010444c80c241c000e49002459121440d100840e45040c0d5110340d514450a110300e41c18080204615071140c0c415000079003d03000210050308003041949420408034111b000700144001d00500d494118180301c40c40e1200a50440000c0049614603192280288175480d0310038540e00903900015240c1c1ca0301c407804c0c03a403c2c44c04400c00390780790314040c01040c00e42e4000d848180381501c1008100071008000410700300c414400350791300b052000214010794070664800c8406811904052420040c0b01000c03001d8007441e40030b10449042c0085044410a05100f07c01409600c217a8034808100440c8080000d043d038400c3c00800c4904e040c5000e440134800341c000d0003810010702d031200b40c0c00c010030148800b03020080040e13038014031200d130501102035220036490240e54100620f0060050601107250340c0203089641044001d8200e06c40303820004c2000200301d45200b81c0f10003d00b01082500c144c60102842242c083e04c15100d140c10821030503030811010 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 352612985 1250 352611735 352611737
    0x50d05090a080a0206010806071b0809031606090e01140a030311100f0b0f01080c0415030618060614030603031606090203120a140405090105190305060f0a14040201120507 75
    0x901c44500006008070000d21900e22140c0080440c5d42c03501014a00d04480101800108505201c1e1240d01c4944d4102c0703040d415621903803181e15035500002203803a007066181303504181d1509000c002159038108035209c090340d1020411201680e240c0e40c0c02040041c801a07159080031601c0400c00c0424881c0030f101c160a0a00c0c0241e843c1a14022030040c207503a40650922410f80e0344440301d440e03500e00752203014641c2c5002e080c414258640414045170301d004510405a0600c084102e60400c54801da001d03002408040e600400201d40c41c0340002c0080c840c5000d17440115060759990200401e0390340c10340344501c100074000d5142c040c81c9a11a0000c001014045504d180c6074203450006075414040711072188500101c030740e00d805410318014200c40700140ac0905803401004180196155002d001e810b5603000d941441842407000340100e0083c02503440684140140030511084401041c201030060150102c18007034807402d0401c08505c0c61055400074003242250080020441054210a42c02001 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 352614235 1250 352612985 352612993
    0x101b0c020307231201050f06040c090e1806100b0d09020a0e07020f060c0a0e0d020d080f030403090902030c0a110c06070821010305070b18122b050d0509 67
    0xa0b802110701c0f201043c90328011100c8540e15044640c3c103045030308a210065000c004c0c812400c1508040a111a0103007041e03000c0c5403140040d00f105402164544020414841c1c04880c1e480c1c000b000c1034290000424450140c012000810301e0f50407440c000c0f00503074010300c1d102c5142009800e1080c00524070031400f240c104810700c500060162078100d00b2032051400b0303000350804440c440405814036074003d10003003800d54144080003009038045904000004141c40d8520741404900010700c0c0c02844420041c5203510018007075107480d501c003003d0360107648a0385801441a86078803405050b07000c03ca1320050000c00038400249098880c0882c00b072a0710300c60003075500b0405000c000c03d8030741e80901400d60b21094000b0b592218644411508810040c000407003051550442c1e50f441d440b070840b032050000341c010108811682040a201030841810000c1040701e0005042c0b0400d80ca8103d020fa4800c110f002c05c51040c0c490a80002c0d542c2200302e0659513180c64115181c003001c0040001401600b02c6100b = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 352615485 1250 352614235 352614239
    0x7080a0203100906150e0405160c110405040c08190b0c09150f070b0609060102071e050307060926062202030a03111e1513050709020408101b0c020307 66
    0x2079104d184060b2a0110014000c1081c180c000f0b00395011040e401d0b40103901c1c0500b08242d592810350320320407403600d61405064118281c1094400300880080c2ca0b5440b5180105220400000c2ca0214040352007510564044600000541e129402ca444000c0c000d101c007071000540180c4d044000b0400400c004002d14144180f440111005800c17117003080706e9032000002c040092200c044d200690044003140c804c017661901000003074903540e0342d100700c0291800481c440c0341d02803c8002d1900141c0405021038410680c0c035040101702039454491100301144003091051f10403042400711514200c200c004001e591180d008200d05110a505a4425407444942c0040183e03814030440704914040d40c0c4040f481c19021020f64100052071407065880343c8100c2400440243c00f007880403410b268888040a00d64a00c541400e80041c440381c010a103005255004c92030842980c0a0025600311400b01c030240750042211008490b68484001711000300c03200e0522500d8451425114254800303000c1e101e0382c039 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 352616735 1250 352615485 352615499
    0x6070f020a12050c10020423220c0e1c0b07110f240103120c060605090403110c0103180605070201110c0d0f090620240402120607080a020310 62
    0x40c200001d1500090360016125003400ea08100d80fa041c2007401724110310f007034035145401c082290354442401203d1701441440050717944100289080017203241d42030319111007001c2a10010242090104003041d40d400c41219641460b14403070346040b01400c0c120f40c00c840a034561502440c0e000389640e04024a07410003140260092100d00111451403000327020046a8507042c02d01d00c5d42072804800b4106401d4010408640030844004685003107061404a10806041a10161004d5007040d5003012441051101b010f501c20100d58a00c800c000580d600316001d42c0045003510009070110201d06c0c12610488007140c40707580899080445400005200c9010303240400c80e03500721103803041c0e5540000303940c52041034010062120a0809240a015003405c050000c1c20201103c3d0845241c00c40311241081c1c900000c01c81010030100c00700d480300d03d0002c03410010b103c04d0340485d4124000c8a0300103031089030400001c1c60034000e00250301c6034110340e80c440034110001c1d00001c226414140803881c0c002000 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 352617985 1250 352616735 352616753
    0x3080901060902090d031409280515040b0d111818160806030a060c1e09121401060503030f090a0f0302030604032d030207110f10030b06040f0e10061106070f020a 71
    0x4403c981c0020850581100d0240007500c4c0f0394ae005038001e0441000c03459505110004480598000031060b944a1600e140100c00820050b01e0320004a040010407201c149400c0c0103280d01d9610032281c40c19010340706403010640e404103840020b46140704480d400034041c0940d0b82158040c90240c2124220303540364032050103488054a0440201e02c00702032003044040303a40a80c104c643c502e42000e820540c589880081c0c85142c1400203000d2004c92421080180701c01c0d000b0600420f401011282c64448004900b900caa0012450b10311072140000000b403074560f4114242c040f41e800501070265551152426078030031091865944071400420750503000c094494901d000e01046507500141c4540c25843c100040d80724501c1c60502c650300b007800c20901a0b6500e00d02180c035038102c0c40c0226850921201041f101d0249400c0340d22448213404002c6070600921428a20880c0ca859a1034941e640c0c03414169910240c88150076a1a0810300000f18840d00504c580c0f10440d4041c4101c0c0c908000d03c0c0c40d54015 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 352619235 1250 352617985 352618009
    0x2070b180301020a1e050c0601140d050714033715060303021b01020a0213020f091e0a120308060607030c020603130308011401021005090102040302030a03080901060902090d031409 79
    0x46010041221580580e814148490110317a04100307282545207840240e840e80140301d01c66000b80031140d41300c082d485004c0d4034405c9130303804000c03a0002c544a00381c150300b010104103014000e2280c0780ca03e03440000000c0340d48103940459441030340701d01d81e07044910242c02b05000065601020016081c500c5001d10303c03a00000394080d07406001c0305e4181103119011641c09605140c1190b0115038040d0140c4e40389043c4d0300c02d941015100580e038995420004816000b00b20500b0b510840700c41a140f4805680c51003400140801c4034031860243d200c001c0c4944081c4910300c05400a10882c00151560070080001c0a095010b8208a01280d01c1d5030700280701035008903050344c40200142802e104254001c10942d001d403030100c4800d40790301610703030000b5500c1100c01c8100c050b560326003001c504504004c0d4129400703140c021f07041d21481c0000341005802c0b0001568164802d42c82c2c0b02d0b002498030307024070982e061010000c022504100683d107040710203030360000b062000d186041090408544c0e500d0280b0781 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 352620485 1250 352619235 352619237
    0x3060903080a020304030e0d020a1a040e070203040e04080906070206040b0c07090e030d051b160b10030f0f0203100614090c09031c0c06090b010806070c020102070b180301020a 77
    0x94064010300e80203019210140500e0702141c014000e02001a0b0440c0c00c0601920041d20b004030540000c0c00000c926406950040300045119165008405520001402034074034883c1c1407d400e4031142000c80c0d5901c52031142d02c064007640d20106001605840c0281210fa0004280c0d90400205800080180c5e02603849210201000100d0b950b55241c14007040005040812040109001e8500059124441c2142100303a1594031000901280c181c1600b03000c2d880c00e0143c0c0a502c6036038900ca01160f1403121031055400f40722200000e0f05202d1682019001d4a0744110031421021160b500c526808511460407603050081100d251304210981c811500140803c01d01444241001c000b40000311001800c041c11041080240d154a61000203010f000d101813016444c0c920401c1210844035012a102c00400c19400d041c0b410040c090340d0300c801070507908040d068801c02d845041090f03030445042d21000b40560040e01040003030381d43c20743c042c1541c101101300d5194000c8007080000d08aa0042903020 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 352621735 1250 352620485 352620491
    0x17040305060621371104110f0703050703091a040902070503090d060b1201051308090a03050303070c03030501050906010f0807030b0d050a030311071a19020c07050306090d360306 78
    0x104014283c504154860741181040d82841215a2603500b44440c42000c1a40280c0d103030044041020030240031150026080c2340e1341500d07952186002042c9030b0041505034009180c0341800f1412000e40e82d50a5407800c901d041c41840d040c501034200c0041d40041c40c058445002c00d20500e203243d2942000880030340d11450000414460740d004001d00881603004040f0603a2511081001100f404003441807001e8000200c0d6840382042c7c8005400c1c095a60070040c19404003005000b0f9403a0007003000d2241034401e88040c0f180360780380c0301440180d000884859001130000b50310501c7c2c1ca03004403811a00f0112619003c01c40728420000b040c05448201c108070f030310341e02600509003071540c5485081000030803526800d107012500d44030328000c11444004070400c1401440802d458904e40104900c1005283c0b600f903440320100b00b00252100303000d00c0380a010340291000101c6204c004689003090005030384450b403249002c0d8100c00c1401d030180851f40380c0e100603030070020245000c17200ea2400079807003001e000c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 352622985 1250 352621735 352621783
    0x50a05100f020906072a0603090614090604062c0609010c02010c02030f0a2303060f01020c1c02060c0111250309120c0506030c040317040305060621 65
    0x500120791442044000c40c520500c02403480c0e949200031541c00c3e68000b89280036200c0d94115030104c04022602e1498200915900001e0340c54140d082140c0c00c070302030601000b00410040c0012242c0c1404c031044003a6421000004001802c145c0c0001c88048002c030200c030381c4c3d035a00c070314a551414030100303002c0e03540d0b0007003013013004030f40d401d029085480e03200d4070081c820306c1a0121702a40e0390081404145030400041604c114541c0728540e001480721071145407980010f0352200800d8aa0b009031030743780c051400c2c20000b17082d42d40000740c0600000d5000d01980e0000c0019400707a224185440d8089902c00390812040d410301d10709001c0c000b81904482c242559030b940c0f2094450114100d0002e40080d00803619080740032a070007130b03005002c890507030500c6100f803101d078646a4407038202d0b0f4004a034017090200034001c05843e5440a002580d20481d50310007150112210f028040c0503a01c8020088d500a41c00241c0d1424100091010b1554000c0c1d210004c1207180e082e541048614100b0500242c100159 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 352624235 1250 352622985 352623013
    0x20c0c151b07030305040b0708160c03060f050c030a0b01021903030507080f04020102071a07060c050301060921081b010c0e010e1002060f06010908060109020904050105100c030e0d050a05 82
    0x101c0c40070003807001000c0c01490f40d80c1c09000d601070741c8902070b983c0b50082104414030a08604489030b1950010083c651001d00d49840580c001c0c1d640410784800c1d05d00002007000c1c0c0c801c0d219841c001c50030b014080b411680c45007800005030110300714560450141000400c08088480c41840080c0e1282c0c0300400d9602c0c20140c0241200001880030350403013807403001d000150f6004076440064808419004040b49417441811b21903100d20b1400401075441c00005520690348032010354141d600682d90261501d40d074071401d40a11100242018400222141034030008055000034910724919071801446404c50390915821a9012008840410151400c1141030b691042c1141c14404046070040304507150f01c0c000035030340e10703000300003074005040382000c10100c0e80980c1d0340f0303001407101c10304031401036841d051000065000140c0340c500072804d0070000700d403074034280c0441e607070341c400613030710310303084103100c0d10200c90322404040b40039007120105155201084040c0a1004150700800041140c074210400b = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 352625485 1250 352624235 352624267
    0xe030d06090509070b12040f051005010315020f0412020109030c0b0c06070809030d1a060c070f0815070f05041a1c020901090506090613170c0d0c09020c0c15 69
    0x220443c030030381050500b44440880f100a03191a903540c441e1064031039485103030000301700c2e06409000d400c511541e0783c04e40c44203e80d80c0042d41601d2003800202240c441c01c2000728107a01034205110403800080c0300c00c0c44007040c144480d4894500515016400c00d9a90b2039804071144150041a041d0900159420700d1400401006030046098600322106141001d0443e881340580000060381c1500d030b442c420400840550440c031074410041c61a99902c405000c559940c42c4248515071085000740000074a803280450010030040c1c00020044103582c030041f084030410207120700d100a008007404081743d01403100e03005003409580e030743e403840d0350f40b240868040109039990104c0b040640100040c1310283da00400b200206c400a030346440d140c442c0b490004a0354028400850b842c414120740000b19414005190b03210940200107840904d01032005110440d040003074064407001c800801007000310210341c02403031102038180503140c00200e144001440305442030a501840c2e0000b290324207016007156 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 352626735 1250 352625485 352625491
    0xf08060c030408121314070914060a0623040e070e190909061d06041a0103031707120507081e06090f04080d060f030309082b02010e030d060905 63
    0x18101425442d1070340e42d5085511400000012841c850b0000c00d0098180d642e50b200c0c2c0310b502c0000c80d2003100d2207080c125030b202c0c00ca124800c00981081d03c000050b1611619560044001606550f112030624000f50740c0141d203488107400c2021280300070741c060840300018001500311215001414103282e400200340c00c00c440a094820403120800c11003c5d0a01003450741120300050020905c1c5c4c0707403800c00c140141f051100b142d101c10907101907500b21410110f8028840c078400c0100d002c0030101039081c05a00c90090100070049078030b240900d959800c400500302d41c0100103180c0301506d0941c2c4601082620001d43e404008580c03042e0500c03070752074090301400c036181404180c060410b1500301c000401303099020f080e155100d480100460b05102c4540300300c4a5242c915142801035a503240b4500c8400d108510040d00052140b0f01c01080c00000460030300014500f280c85d688030900e00840d50040e1070900021041950345c1ea81041c2645142400903180c0c070000e9040004080c1d01c0d205140d002d440c0b000f = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 352627985 1250 352626735 352626751
    0x3030c090e040b240307030303200316390c0b070c050a0b0a050414010e030a2001030203070806090a0219090311040e100203060d14060717060105040b0d0f060f0806 72
    0x11105510517100012240111b0782c00d46030111320840c02d5640e03810f1030001d1030300e2500707010000010030419640c00e001c030080b100c12035551144140305034070488440082c9042c10400c1c0e202469126140300045184030012103000e02c0090b00895030306c116644150307001900848000d0030858080116180a10700c0c90001c04c014005c43e454411a500024120f00c651701034400c0b0310184940343e071400d134410010107104050180c11102086d100c0d04146104041d000340703180e100d405809041c03215500c0b90084c0d0303003e10860f40380c04025803509000c02807902d40003825801034503402e0154400c20402e01651484110850315140d81560031424000c80a03000007a03007034002c41c201540d400c5c4086000a165589014600005131a52a46d000040114408110142a50015150007036084402213640c90041203191106002007108806281c9054402c0380e02502250341484100301c21038400c001000e104198080006000c000301c00d402e411505144c000c040c0411800070103114400c001c1040035005424 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 352629235 1250 352627985 352628041
    0x20103051b1b01020906041206060909020603040b1b031509010f080303010e04051002270307050a090b06041d0613050c0d090203010e06180705010c050a03030c090e040b 74
    0x4800c01c200010700c24040c0d201040b08800310b0400340107400b903050310241003008056039595555120440c0600101541c117a955524040c4000b0ba44c1c4068410323000155406030080d415a50740d502d50803190100108242d20b106541d10072002c5a18100000f103200d04440e01324003013900f03440c0d03081c0040b94a050304620a05a903000d803e00007070100000f9203044540940b0405c400e6903440c41c0640c14020007500342481513001040084d2058041b0003c4400d0710a4080c4042c01c14014604240c0d03180620700c240d0390442070700c900038003c0c165203401001e103051001d23200a10b40303503441e03083d001c90a2412012824151310b20082c040586401c9400d00201c0000034814081810040d50302c0c4c0d46d9100e01505500895560392110045480c00c0d000082000c0c40042658000d1030408440300c5040c5541e03141440031300405e40d01240e2580140228500107070044010840c0c1020f0f668140c00a10100c09280c0510143e0000080c05c2c54a48030144c1c0f00301d10800c001030302420b012032010022156203584a10201e0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 352630485 1250 352629235 352629271
    0x803010f09052502031e190c020f010e060c0615011e0e06132112050c0a17040312050d060e0f19020d020423060a05031308041205010902010305 63
    0x142481d884200382c5a440303200103440030501c10507841d51107072006c1007140c10041810340b03200340c610700082e103030300c0c0003000c00c01c40740d15000f01084942c000220002580105054141c5250307504c10740b0700001030342d400b6010364a402c40240780d5a242a07004c032000d500041903601c84004a5a00400e202ca180700b030504848440030526902034440503841d01018026600850480c2004260740382e0b18008200b1002da81da01c801e03103d80406c160004d0a4400c1e15400d2090b101d441209201d8421a03011000311806008203080716941c1009152450100a40c0c40308207000c040003182c4825020040e4496036122160340e60184060501036400c20b610404000c401030080080002d04c2202031648121403a1080c85482d22406280000740a40c2c5400069280f0100d40450824400b42c0c031008025599580011b0f90000d0008000007480391620b400300183c020f1021614030300c1c50000541c0700d00c0c40340604d5801c050310740c50030b05c0700300807201801e540d569103d00d64001907507014440c0e243c01030454000141046 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 352631735 1250 352630485 352630501
    0xb06030108070b0d15060e010f020303091905030705030c060a0506030703200d0c0b070506010806091908070b07030b120106031e06063602071703061c0803010f0905 72
    0x140709480740788800980010040c9241c03116174130281500c0d02d000c80e5040300a407521170051600011328110340c040b400c801c1d20004118000010ba9121700c0410000b0241d284415a40b48502400c250089849100512000000540c2840903110348203036080100454681311440e01d0680b14041c04460094110810910100d8a4103031840c103010030034405421544502c401040380c21040d802d0240075010b1500c3d021403c00000380045c265103000306c08407050347e40ca88003001c5d11030b0300548108072598032a402148450103401284440ca0b03000d10525400d00c400c42d05d851034540b01c2140e030030000075034401c8000441e103444400c4090607814030008018050869036400c0036540ca507881ca030300101c0c101039050204036003500f0204c06030032001130b001c030455911004001d40314005807407101e0154a002000d60604100e1090f6200682c202c1307031010740045c040100345000d40c006001150801400200130040000300760008800c1481000c00035520b614001033501e00056980003401c10f107052034140302d200 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 352632985 1250 352631735 352631743
    0x905211905060a050601050912010c1106240111010e010207060c0305040c14030a02040905010c08091609020f040503190c061803080d14070f0311030925051e040b06030108 75
    0x2c50001e00014644c1750074006070b8190103514403040d8071042980003040e5102c4190404100c0000720388aa00c4618910400c003600c900b0220f411045800001d5018100907a211868156007581070416109290b02d01f00344500351288110046010382d0000380b2001000446c0c1314010080003585810005424181d40380c80314a00c003440361003003900c4a2500350440c1e50302449841070b4158000c0c003c000e060041d24106020b007d04028a402085c40350b0700283d540100400c413503201c0c0c4039525607824601d0500804000940010f070a4070710307802052001042903203007005110b19586100c00003008007011460018405801c0b50043e2042210003164202c0410501c11110181d0354803001064a40d1005109070300240401c1c00f107101200d01001c248803e9940002083c0141304442da014001000d40120503845071100b900c9280c10303603015044052545400090100e820402d00d00d0003d60203a494000030403203e0340601d07608030002040c0141c1c516242c1071090724240b071700c159903480c190b6140044040d20b17 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 352634235 1250 352632985 352632991
    0x90f01141017090304150e0913080301030b040602120106020a020a060306050102030a0320070c15050a0c1509080a0201020a09050306090a02060a230d0c0305040b070f090521190506 79
    0x2c40711008000c110041002e2050343d018121885410790442c50401008000324842d0b10000d0140c94800041081c0c1034070980704405d042c3c1c010441d1440c5901e15076883d0b0000030000c01c01c2c2d480a909200d504800b10030b4442d058003c001c907030f00500700c500e014010000444510351029040c940341070070030001c90340c011065400742005030500050342c09200a2100616a140d8104500000d000401c001004880d060400075140d0051507110007400c10041a54917104140c0010b01051742c42c1040760004034204190604145004404140e0101941e00ca9000e034100c90f0303180c00943d4000c078000c000ca960101040004000807802091a4140074940b0390310754070029406400b0307881c00215019594026402510343d0030792200340141c0d1449600710411580c11602c4860542d90074400c1c4004027a207c2d00910380196003102284c40d2035240c3c8181602c805100c0d82c0c44c40c0c140600c40d00f00169650390201010280c40c04041980301c0c0c0e04468410506118a903e00310364051400716103400400c0000581c154 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 352635485 1250 352634235 352634267
    0x30b031903020102070501020d0e0f0d0c2a230307050a09020a02150c1206180a020a03060803070501050106030506060a02060406020f0c1c020d230306040b090f011410 73
    0x40c036612a818103d01a00c61088050702542c000107c2c1c0b040b00040d6880014a8001b075401d59410287c00840307030b034848000401042c009183c071161000419403000c0030070100000880502001c3d425205024030380a5140e010245c44642d01200a05802c6d4815002d51300300b604401400020381480300142e0890224016984034070f5003c1240e1500c1030003005400c0003684080c81c41243c503c0d094681740e030158002000300801d00b0f07803c3c01260103800c1004103240e004202080940e4165203805448000b900410400320400d40c0b24075002510000500044c07034601d004e00c00110b110340c1010005020342d2005800c41b40207034410060718025942c0410030603040395000c0800350b66585803011500450040d4490001c490040e06200c40c0c030401000080042c4012503000e50b2019003000d1000c1d00d6864400402003007240c8001207101c000383d800310046a01540081002861061000116002e100e040355450746488003100103000010890640c00e2203508212a00002d412140000070440c02c9240c1c078141c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 352636735 1250 352635485 352635523
    0x905040b060a17120714120408070b0306060d0b0102010b0a260304180902240706060602030406020703030c0501020d0e060108012405090405070e0705040501081509010e1e1003030f030b03 82
    0x1010440c2c100d40301410200c03240d040b1f9000401d0040c1a084580c842e10581001740b10700e020015441000f10240d174440c90005248508140a1000d0340c03000d00740001e552070455581d8140d95030203940c5c000e03201028143c6c1d4440300c1d610340340d80c1e940e14042c520400010411079000340400c0114002800c6030030700d4140e40300c0d0041030b2481d003440412014014420944101c900925510100c0d510250180c0394150064038240900c90399420181c0e00c1b803145004520050308403410a00110740601d0311600c0c0c01d4800c20005240401c40f134500011500800e401103040d801070401001001403d0181c0240e10010102c42113240c0c001d061090f800075803501c07859001d2810b01d4001800d00905004002c01070010000c0e540799440c0004c4001d00e507500c03d00074079001c103c01c180440d010110104850f00101c40c040c0400c1e05036420030142c5040c01c400146610b15031030700204203940703030561909903a00650660240701601410361801403d0895001c0c081c6042500d411070070082da9900280f581c0c1e003502505c840b0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 352637985 1250 352636735 352636747
    0x603060d0807020a030614150306071116030f02091e0406052e3003140f04080d0305070503041208180102031303020c010c0515100905040b060a1712 65
    0x5030740c560060810296224030703441000004e1101e140c0104480300d03214400707400343e9908c550079400c02c1e04043c0c0c43c2d84d415a1189001402c01030183d6001c00f04c1d04080360450f00400300600c0c080c5007050039600200d84c1d5402a00364402142014080c8640140740c0c0e03004c1101900c00fa1021491318100240041c000a4503880411f9208040054a07032061000271750941d132200c1d1600540c00009130074410491601501c00e5000c40303100c1510200d4007031a45100c8841020200b44c1c0b01180c04016103810788102c120100056080520b0030802400101204005045210009003026040740c0c00103201409106040080000180401110300c411400c0b40c10184141d8a0303402c07040c840d1040d80102d00300c04d50320020500c0180d4003d40c0002e40705900c664211034500e0a6040112000c2481c08030061440e4080c41c058080d6010962425901003100b4400c1d0344141e41d901c425106843d01528203a0740d01100f030080c4800d508201c0701c8038001d4180d200c240d6441880b1030036250f54948005507402c2c032414022440c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 352639235 1250 352637985 352637993
    0xa050337121410030b010603140a02130b040e040510050403020c0d0813230d020102100504020d0804090e0f010c0e150c0f030307030e01060617280f0e01050103020603060d 75
    0x30952440440d00d00b8a450300d40318640300e448050200340d0360203600070000900140b00b4002d01b002030f2250b4482a01586441413508042d4111144690107043c440501103813036103480c0054401492804042c440d1400d080c2001d03400d00400071820411b507400e01040102080e0009a15070f206502998034460700003190404040742d0040e994115002048590001580e5420700d40b02410340007003d640071800e50040c410408069005a4028050b8010507d00c0c81600d000d5403140c0c0d409800500001c00140e50b0350380301d481070761090b0055046030f50750f6402818042000c00040740700c105000005c0001140564014004ad912043c4e024480c00b011801d040d6440540c2d000e90381d070107000c501180c103205274000036a41c4a4000720755100000f0300e002189000030105000704400c9812580b919880c0c8180c020040d05003000003400d128842180b0310700c0681071181407184c4c8550310000d010001d101c1d50540700c884240c0b1030410101c003076681800c0c0140096075030300c03003141e801580031200a041d160807407038 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 352640485 1250 352639235 352639241
    0x1514060318010501060c14061b16021c1214180a170732010f112a0415050409030c05010504030801060314090601030b090f0a05033712 59
    0x3803030207a5080500001d1860740040f81c01203405e10448014900b842c02c07001c9a80e54400807140c07088034800d42e6400682c4100542c0040a001d8500e0381c480c07410f00d03a1768000c07450051040c07444c41200402c0150203004e00032604100c2c40b40ca4814500758030480070303103442c15070700c1e00540c2d130401d2600000790881e040d01d5461126040c000e05981c10240c20a0032603404d41c0c0d869882034400c001e1021204140380d003d0600203c058080c40f0840e444404446800900454a81c5400e040740307020f00c11a1041707118a800c081201032540c0602891440c06041040000050301917101c0445008a060001011516112544140c00c1e00c0301a140000c0c404041d060407100303c07040c144007400e203519150500003816071000040b8142c88480d2418484007042c0e500842c0f6503002160302241c80d40010300144002242c640c0c0c9280c00200d240102c034001c4190741171883c182050694111000d900000744411070000100c05c400208152110307030040d4460310342203c03d80945000611041144d400004002c11100c0e074 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 352641735 1250 352640485 352640521
    0x703051302091303081006020304060e04020d0504050105070e03010e030306092211032e0b0a0504020d02040509070305070804080703030615051b0706050405060319020c0a0615140603 80
    0x20410b90b0141000c2c03e060036541510102980003504150004542c171511071010740807101207900a51a2a103001d600302d0b41c01c0000c0804c0d6038016000c020f00c05100b1128050517000b107000748000207050428040c0644040780003100302d80607905003400d604020f4008010b5079400401940d800709075a80f103a00643d8400400d0166501c98455100c0002c10700c0200819130030507900603801c6504d0074075103148980ea0980c2404100b540c5a0205a09641191403a00940c2c11948007610711f00442c3d84410008090780c1042d148507080d543e020a0407c0145403c1d1304945d080511030400b0441c07400e0007800200400d90082c409048040d0000304001094465880000107180303141d408070046046840040040d4064410000c0c69010b06188030154070012504004541c0c035622000d00d454945400d100154100900820a03d140c10480d4002ea0b50540003d100483c0e5100140c00c0d050341501d840411a0954100306401d40d02c03c0c101402541010101d104503060121640b40e00d81d65500c0d44d1100007a401 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 352642985 1250 352641735 352641739
    0x4050906061309050c041e0e0705130c0306080d020a150902062b06090b09092a0105041a03060a0f050f04180c030308180105060d030c0c031703060a0e09060703051302 73
    0x810390711b6107526401fa01c0e80d040020141800c2c4411944006015943d11107401850351200e404a1104050349091b03010f6481081142408108503a41d0302c0e0351414698400900e00268100b0000c80d010001d0300e191100188014600800c1401d5a41d00850388501404680c0302c1420840100a02c00e1103058080d200c050030178420030321003292940c10380c00150400e010803502900502c03000c40e400d1341001c0307402103d8603035826200f0703002000480744031188030640760b556040c07100401c0080340580c3e24000c550040016010801e9990410328180001c0c9105680300d00941d03502e80005010954a2503240d112440080350046500e121808078924031a40655004221401c452030010801d03030800001c2d84240d41c0d240d4005a10000456440e01fa28011100940d0218100f513804000a0284c20b50304006401400303026072094884d40d4045082044243c140e2040c1c5021080040b680b0700794203802c001e040e401ca02c0e01500e0615005007950b8142c080d1250050540b250001101c0040d0030074104501500 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 352644235 1250 352642985 352642991
    0x12030f020304120e0307170102070605072c060412060509070807081f0609021c050c040e130503040e1306060f03241509050a1a0307031202100504060b04050906061309050c04 76
    0x101207c04ca000b91b20031001181e80909140010f0001270044480302e0090014040124030010071759030304519107051101c0958456000c1c40081a40f0700d00d10340d00e81d011403007231100150504150803054a0300106502003126a4440030301404100c1740810032100e240c048000464202d41c0403a0074101620f21070b002805003e01c08515050100c0c5101204000503c0815040005071a9104c20030303401e100b41c0c05164200c2c0c400f00c0200750812840d0110f0910b45004034140c80c00e16494448a901403541a80c1c84603d40048004100c1809518468540249071041209135000d146643c1c0300200307206021034024100071044c8040c03204441d500209840c481d440c50380d001080c2c80d00107000050009030740000b507180c90000070115400c0c4100c1101c50fa00401402070018902e142d540401c40b9210044100031801070480100d001c480d24025140214419480030a81050a20074441140c40c000c00030212980000c042c002c09841d04003184030b211082c01404035007060b43d82450b03407600031108030f1141c210389 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 352645485 1250 352644235 352644269
    0x6030a080a0c0201141303021512010305070303080c1c0e070e09010c030e1902090c130b1c052e0308040f1a190f020a050a12030f020304120e0307 64
    0x240c0700003800700c0b207407003602c0366540321102c100003070018000d4030800401e80e00c40035000e0001d80350200e00c00b04181e480b40d0101d0719104070b070510402c190701d0170ba000302c90940c070501051081580000800342c0c040405142e943c10114060210858800d40c600003030310041cdd07560f0413420032290500001d070241440340080010350910082c0d25000381100204040024508842d00c0081000850245884001d07640703211484941c1d03400300421340c0000703004080505020000d280006c407141d44030a004092a01c00f003902c1e0000c0064107080b40441400300c5441c90f152001300804d0104150302c003041250310040784101b2030b030a010303000400a0540c101900ca10000300d40012190008034079071056070803080c42e082040c08a000e400300d803401254080310300d4140040e110b1200603c540305a11740d080e01c034812035811102c40c2d164207040c082151420f507501e00001000f0f24130300b50540244c44107032541030021480c0d0310f403c1e01c450184500703c190020410414142141665500300036140280c000d4081d0307005050 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 352646735 1250 352645485 352645487
    0x2010f02030912101116030f09210b0717040b060402040b030907050411070305030604050406060e070c030801300c05090c0c0601150e040b0319050a05010b0a060f0806030a080a 77
    0x513000c6440c1500644c24254810b420481a0003a10b0398585a41030401c050141d40e0350507036644c80501d2002040048007840018118116210208050001050409051a242060b074500e4100034010f2003888914140401655281c80e03241d07a209070400610b070590303120718000030064070440d440b8000c800404014001c4005020600d038080b01c0b021282000507800301c00e844507442c029110003402041041c40003504a003000d4200b40e50040c410b003000038601d500e030201207503581402d551110015030a0030340b1900b015001132007a4050324041c1c4071217507031011848807000554845540c070102c7c102074010810802500300400c4011701340003018001c80303141c1389a030000d890300501c1d01041e040c400d1000010702c4a01c407009400001d402c943d5098612141c083c1803001602031051416054461b4801c0403d0000740c0d6071000513024413300190449c284607041c81429161401d4a0030310588a19208000ea96005400c080480c00c050500507816542c80000900b8420800400340441c00700182c0407001c5 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 352647985 1250 352646735 352646743
    0x111906080603150903040b0a1403041b050f060f1b2e060b0904091104110d0e0d0c0f0507081903080a0b06041a0f12040b09030f040302010f02030912 65
    0x1200c0640854880750342c01180c0b51040d48080d113001d01c440d00104014414600b40d00010410101141081005600030320400c0b100e0b5881103c043d81d551b030340c0017071400c503030122004030700000c240440d08814074000030b00c0003a110784150701c05185070040004400e040141c2706803415034040b0115040c8d5254a003400ca518814080c00c50030076944110390501c1d4a400b2407244519410355200781c908504010401c01400001d22440c00d055607950500d0040c0009682c4a0003a181c0c40100c2c06003068a41d1904107103401540d0321031502501f04d8111901c0c11a02607030003480d02d000346410401000d070400311824518289055500015564003030390400b40c07604004d0304400242c16100e0740d0394410943d120b6004a0490760b084240c564066000c002c200a285e011400b14902c03840d0312202035150010301012100700e50b00c406010300c14041c8500c100401e00034103107121588100300c03c000c1c614198540321074800e14850b03400002c0c10710101c3d64008003090720030070130744614220181c0741d1800701c180103a181c5ea031 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 352649235 1250 352647985 352647991
    0x20a09180804080a15020415050d0207050106080106060e030a080307050f0409050103050c0111060702060403080c040e0406152102040f020d050708180f0a080a030e03040906031a06030a11190608 85
    0x40e007014411a98070745091b0310071141150b060303110381044404090310865242d4040e840790101543c09010b40130101300d080c89240028102c4100000e00249001c0c80031740009450220700d4800c0d04442800d01c0410011070407030360b025660785002681c50406590790b1032a4015078128029152802001004100700000c550b60010340c2600c4410070048070140c407594039001100e54a005800403004100001d001e42600c5400007590100d43e41003644410561020000403241501c042e03480d45001e940ea02c0b00300007001e014086183c000d4080c401407820609132070442c3c8038002d0142e90749190195907440700c0d5058a580204c0c0342c0d0140154109504000c0441c0002e0310594040304100d89404c0090100141c4801c0201098000d0859425103494031400d5400505200c414552078180502107548140014006051182d400084c00d9041d810034407002c1605181c1c095140055106100c0d40d0743d00001c0400c911603005a050f400b202c2400003042c84103812140c0c007a0306007804480840c4298010f0078843c4 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 352650485 1250 352649235 352649243
    0x90303050a06030819020f0115050405010803130b0904060906170d02010203060d0f02030c09131406040305070f02040b041518180b0411090c0a0e0a03020a09180804080a 74
    0x10407a222103000d14110340c1c0501c40202400c008005a00c030340180f181c0b03642d007281c001d03005076101d03060801030346802e4a114583c06501c0740017240381448149003502c01c0902500b50107008609208010403071305a1642c8030702800000f4980482c41c191166180e1301310708083c0c1010002444880d07501d0b600d500c1d24001485500d601d6001d000680c500991052090368440d040c010404541c0b4a21a21001c80900351440184d03058010224840315503198100c2c114010340301e000c44150340f100141842d003103092034000c04d1181034015800384008680d0003000c1d6040707141c20a1000c0050701862000070000d0a201e01d01c40e80142c1021401c0d6095480103c2c0300e4102c50381c8803c01c00340e042e006590302007158444c9941d00d510010f100c2a0b400803514608169601a102d01d405940ca007000e6400203001020441c0c417640081c4000034409052035000d49610000442640c0f6099580d0845c0d001490602442c003400b03000503a01d036040c4a145061384411072160307030000051a40c035511144090303224001e2070401c0d1 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 352651735 1250 352650485 352650491
    0x60b0a120c030507200307050a142505120c1003290a0b030612060f06040e0a0b07050307020a200306010e090c0d14160312030c0e060a090315090303 65
    0x6a0307168001d010700f52040c00c01e9941d021500a41ca40c801403c008107400300700c03040c40180400e10024500f088686003c1d805090207420081c0c0c9082807529011009011907500c0501c995203890321081d104128040d10000c40701843d4000440521034503200d008c05e03800768400100c03100079584030741541c81040480c60510001d2000144007a01520b400f20380317100d41d500030380b00540c100804020746000d5a08600000c02841c80c0400152010780f5102081e42c04c1c0b0705408510f01404542e203891301c079100011100c507016001b130100b56250155420001000007003844400000100350910031b000140c1d55a620000f443d00c08024150b441d00104942006a4000e20800c0b0010030070009110328144164045c20050000c10700710340a010705403400c01012142c1321400c4100c07942e164801e00c1205080280140f034182624950b050000c613004012000d03409051134130750400c601c150b2015281403150303419640c0a9540140c18022920380d4900d40c8043c00313012030154500c4601940d41c1240b01d042e40656030074 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 352652985 1250 352651735 352651751
    0x60c011e0c090e0a090503070b0705030108010b0a140108040201030e0d020609060105090103121b020a0801050f0f0903070326010303050307030c05090a150314100302030f010c09031401060b0a12 85
    0x5075100c4109000c3c1c2801c081c0d0190019641100507008100064414810707a0700b440c2580d940c2c01d005110668120000c503102200601c400d0009108240f94440c01b201c0e00d8030032a02c0c0823130100300003a150068504000c0c10300c0000d8290b902942004410302504801c41e90b8400c00300c100251031b40d506403090700c01800364200000e03040c40e1141880341a0f90b00105078603441e0094040503a9050007240301c0b004000000281074000d40d8410301400300a25044001064a24103100c3c00041c0714002409900601d610300140012038a00000355202c05038035013407480c00d01d101116902554451038075100d21000311100003104159010000d10300418071920107001e4003040140540d058003900000c150030443c040820850380d0324007651b2060b01e0005060000341e00c214031030100848003044500d90a07110942c442001141400c0000c10f803460340d03046c0200110410414000d01c940304504c80908501c408000d4100002d400f940600d004043c170302480d65032280b807040050180701ca812514002c0703900d08200 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 352654235 1250 352652985 352652987
    0xc030a051e15040f0608060c0732190b01090908040b070f030809060112032a081804060f1205030f210c0a0f0503130c030809040605031218060c011e0c 66
    0x141c1050b86c2c030300c8002e0003a41c0e840e0600021240c1007880203903100c40c1d85103040003501c036540c4800e0607800c00c80b0030480c4030f50864000d01450042d509240710141020f25040901080b80700c3c246a05440e411000821002511300b0b000510f03018540041103590800503d207410004001b01400401c0d12a03201c8281564a086811340c40301000d20500601210f2a640f080000f4400c800c40d4801e47c54142d00071180610076043d004050000b0801103410740d000041010406500032141d0a124600326130600509042c031010300c00014103481004664941004c0c1c00c4104102403042d10092882c03003000984890300403c40100804032806010480c501440c0401c405414040448240c9079040c0c549000c40d0015120840e100d0b40000c0c1004c0301c1c01e4070840a000060940a00c0200440c01f60b95103d0300c40c4010801c00040b10400d600151090344141a899592401003040d9049850b941d481040c1c1c4101800100303546118054030072005501e0840e0180060348000f2200480801803034040040c0f049c0d03228 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 352655485 1250 352654235 352654241
    0x1050c0403050d0801060c1112030705010608060619090c1b060c03200a180906030605100503161206061502010203070e0306100e130b131203050c030a051e15040f 71
    0x510002034040804100070403230006610841e0803002e481c0c6e644802e000201681545c001080480d803036515203204100d0b51404114242e005402154110a08000b200c1d16903002200c1d441800c01c032030b448500c100007090165048681400007400410b0080329645409070081c2554403c00c004640750151200c013492a4180c0014045d00e04602c0e03e160450784002030310040501841087ca40705000c0003c00d2400f4030703000d420000d605c204004a21410f083c0545010303408250402400f0b0307030250480c6d600315908031581c2001c5030114292964068680d0030154082c000e41c1c0c0140000350280e0700c504005590550095200300196030b21701c0015101c140c1010b44584043d00c1c00300b80c0706e0303000e207044c4060410010059041210907581112004190399840000da00848200104090f5000c0c50300501c01a0a1074100c0502c8130b03d008c0100c0e1078100c000000c240000b400d860896550707040000d40a40790740308012010861640c030030007540740121b075000c008850046000d020314140a0101d01000e5140 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 352656735 1250 352655485 352655489
    0xf02220e07021204050f13020d0207060518150a15060e011d060d0b01020109020a0801090308072c0f09010801020307111207021c0b0705120c0a02071e030501050c0403050d0801 77
    0x1030103440c42d017440d020401c20600a00110329500403000b0080c140c0c01c00d524801402d12600100b800360326901030741005000c840340204400081c24155401074611400410b841c241442c840b121850303191521141d0a0050035200881e00c3c80840401c40800e0103500001ca164006200341d0344c0050104241c5007591402d1a880140768000a061240c142c008841ea0000360000780c061000049a02e195000650000c80503841034400340d540d0202a018194000b031002d84c01501420004008448480748101c41c4d081e10070f946070600c0d000c4d01d514400f965120942201c00e20f0082118405507106c0c10024000d52084d5040d401081e911030001041c03d034045200250307401e029135103d060100329020b1003841042900a00b00d600f103040030300c40001c0e01070258030340a840d01c2d60750030782c8844400d41450f81141000c0e0158140716000c1c8160840380c0d5000450000355182c800364602c5040c0c080c0c001010341e070959040200103509010420031082c1e14a0090800c40b4000c8084a8134003c0305101510a00b07428 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 352657985 1250 352656735 352656763
    0xd182c060d03140d0902040f06030317040f1106190f0e0109050d02130207050a0503121305060613021c0f3803070f0602060603060a0c050702040f02220e0702 69
    0x401006103640d403d0300c01500408a00000215220700b00380d000030b045540c0d00b2402040f07144c0d510303818820b042e03000c11804811400c00c0e054000301c5c2003c0c2c64551307400e042c0c031301c0041c43c010705948032102a40340da40550f2024840340c0000c0868017008000035145401d103080d1540000c0c4241d001031015882000102c04a4001030074180c4004281e80030b0104255080d500d18000d103408011403000107504101001d04640070320003560300c80131079507191040d4840c0540210003070202d248000c0042407000c00d11640002d000c4407114151401e084d40c0c003020703004082031086600300c46c0c24000d00c10002500180200c1116203020014420310310760441c1600c6020207407845c070100c0d800d140c4c2c140c0c000c03604c440110080f00030102c4088507031722081b4000440d0580c109800682188042c00002d0508010035a001402c46c5000c0c044d1524000c0001d00500034010040d101b0303a1030b200050140300e050750460300c07168078aa24111000d04000c03040c2c00741242500c00c2c0f80f0035600c2c81c000100c0491020500501d48088 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 352659235 1250 352657985 352657997
    0xd02090922080906040f030c08060a110322080d0e0c040204060e10021903030b13050f06130603020d0503070201090905070c061e05010f051306080d182c060d03 70
    0x41d54031110020b410403040345400480410001c02c0c40a2142c42d0003005611443c0c1e000a550309200c0814104600a4031300c0084a01344044035003c0c9110340300381e0380e10000344c50f0210990b810882e21000e180301845000b85c0b00d04030000c1c0140d041c0b0010341100b0362241c2d01c0c40440d04821b4013803003400704900ca51301c120000190529440d06042c03400018101540701207104850201c00004400003818044000413804250746d14a15111401c0900b0b000901080b01c1d0340c104000c1c40c120701c0c602c1d4240c00003444248074042400c011149600b403644603001031600505003034054805403800d04e40d66800400b060340030941100001950b90700718001c107403040d010f940d03804403a100c107962074801401c002c24020094140311054001b00280621425000b04400d00c0c5000c02c0c6890142840f0186008164045076242880c2041c40b0490703000816003114040c600e082000704500c04142c00140c0301a03001041074401001140e41085100304c81c4610050360b40d094884107464800800021200c2e8500060200306 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 352660485 1250 352659235 352659301
    0x60b0306060409110d06140916020705060904020f0c0102031f031101200f0a170a05040513060b0c010209030d0c03020a0b040c0812070620040905040c09020d020909 72
    0x9065006130300200d081034a910705256642e403101c0141c844541059054940c1000c0d20145860701003601c6401c04444c060201403010b40800013502d50400307000b8a4020000000c0d4500386032039540c11240c4034070004804540342c0c4050941140030303500a8440c3c0f000c00752401e050143c0c00180d010b81c002165401410500d282c440385005541c02111600e504628021040c0140500041805401400c408040250041c1d07200c0307160603e4801045600540c615a040c880c242c1c0c03060b08042220103584080740c005141c589042001e00207002960802c0454010200b00c1175100d85054024094242044040d500200318000046800300851500a4016031098a9039008900c00d04102c64106014142c070400d525280c050651034914011980321400800280c11300a11030f0611640224240003040454a1154022540c0b95405240910240b4940d600301080800c1f40074103041c8010040d22b007056440d031403a51030120094011384003081c001e00d40713840003941c440f029040a500c0502c80c81c0000c10810 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 352661735 1250 352660485 352660499
    0x302070c052205040515090d110d1b020303090d08070c05100804030f090503120406031406030a021e04050a05041505090303180a020603010306020c0d02010e071a071410060b03060604 80
    0x480f01400035151401081e00b80c84074080b4209a441c4190a5a0010080300808800040c494450007403400e0040e0007003034442c3c0050394050b07131303c2600817210442400c245100d03000107400d502c00c03920840e900c0300a030036a69040020410180100d280208500b41141d5651400c1c441e0340d070b810240120015401000040000380030354004041000740345070403450551a007000c0ba2600494428802c84a40081000c21280e035050064145105207005000c059042c1440481d948041024000b44a601c16881711000c00703e0085100f407001000030014420b60078514003540050805a40036100e984904008213000744a5008040c054208100210b286542c0e0020090851070b840440181c1030040302e105001590365403020358040e500a510041c3d840c03102c4d10b5914503000d00d645600c0d05590500d03e040c401c820300815250308494209204a0400300448100b01c654826104010301d241800343c0b0300428140d001031442040024650304029140d2121060906800102c8001e64001010030041c8501 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 352662985 1250 352661735 352661741
    0x616020f01060819081204113f160b09010909091a0604020f1206190f060c030504090e16141c060624170403080f060109080304060302070c0522 63
    0x105000e017203003c1c1044030003808011019000e81c0d0560380c91407003807202c580618003455407118102103c6120403000314158003002e0326040014001c0192402c0d884807400c072010504c80650442001c440d010440d6072951a225855048564003600003015040003180350f40e064840e1006064001030300c140e40201004c00d1650140c00208201e070026001e00480d07a9404000025000408402d240401c41e49010700c240804000401ca00d100b00d440d03002e000f04623a0030901441c03000e4541c18640090320000906003580d0500c00c80e801405074500d02624201140301c042280c0075000c0d000a010510f00350340f01010600100700c0c0c011550311400f030102c0c00f2060300e150100c2c844030710b1041901040300c42c7d6418003042841d0f40d00007610b000380c80c0b80d59002c007034940c0243c1e010645040e41107c180a07040a4500804d1a5801405800b00c40004030200c5d0b0660302544050b0b00814110048a941d15116a0300801030741041d841241c000c28100f10110f0280781508030200250513040010741121203121020003e = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 352664235 1250 352662985 352663033
    0x1410081b010519230702090a0207060902150304020111030a0e0d02040b0303030709090c231e0301080703140705062515020307110d121d0616020f010608 67
    0x5020b03003000300204100002031800c1ea504850b40b83c03842045903410845090708400b19000000c260100115001a6103100b0398507000081c5100041e120090b62a10600504240030040d5119920726003003e10000d00c500110720031031003a610840010700400da040c1d0350b030081c8102e05001c5103580d42980300c82e0811507400b01110707000030b2005c200b00300d6035001300342998000c2e80e03144002111040706100e051501c0c01003080d02c92135440c001d6440541c1c800e20000081c002304400c0c0386030200080e040e0001c40c2509132100b00211f1100d400b552175035a0410940d541c5c1c020701c412101100028403e0b4101040440c9250440387c2c0a40814070b88101d640c09120303001000c80341070418450307200300c20007c81d211a000c0103000045640059585c01c012402810101050001d081e01c0e81c0201c5228007825800240100a10000000404c1c040000c0c5080c0031250340f113003001503051052104111803e01c220a541d005140650262502500304000135401d0780c0e080d0290740c1e900d5001c42d101548010510a100b16 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 352665485 1250 352664235 352664237
    0x3030206012c0c04030311030c030d0f02131412010b090402061c150314010504020f10020a08120403080f070206041b080a0f020907050408100e030702060705011410081b01 75
    0x240070306480060040b90b040ea0b41c400360a0011600f44101070f0080000d414810380a0011401d1880740d4280e01ea4034428107107844122070711100144051700d0705030103032030025030a04941d0f440d00c1c0c0c55410701d00700c801d220881c542c400d820340c4045500c0c428062003a459401806003903800c160b40c0f90740910060f540906e2007209401003044044c0c2c034484507842034820516400700d680100c41e19504007202540807485000010742d14000078080184e440d0031030044200000d45445000440c01d900a030f08050201138040c0107030300005202245811180d4050f84105d200743c0b02e00702607443e00c00c0d1558021408556401c056442400850003043e0759003d89001c022481070f0941889440d003801900781208010111100c00364847c0c403001310310702a0410b0340d01007680d00d0118182442c240003603981d035035117500c2003c44c0f51351602c404980c00c00c103008030703041e079a00507003826030b110140d15001d8024001d841d00c0000c0b410a003000b0494007540100c0c24404c654452009012074140304208501d1101d40203d0b4038 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 352666735 1250 352665485 352665539
    0x2506050d151a1c0b0603040f0c090c0806091006051c090f05010e06070e10050c0a0c0308130603020307050304030f020f0f01150b04030309060503130501020f0703020d08010303020601 80
    0x14040c03120112440d500905048460f4a40d009183d2a00c440c1605070481d90b4541e0800400b0309944e114582641d40c05a04401c0ca01a00c44150800c480041841c0e089000403038107040c030a00c3c180e43c0140180e8000c03d0191001e045617504d04401a200180b02d02031140080d82c1082601540700d2a90800000250242070010720782c40c56940d40a20087d050008580d16511840500c048100c00c0c803100381d0040460802c0d0901140070b20004480082c003c8008050200226801036018410001c69140310ba0040c1e035001c20075201c1c109060b594102121960b44e0302403d03040407940ca031080c000d0781c3c0507481e151121401d6890315a02565484020401501140304600380b80b00f030298104407201ca6441c94a000103a5400c101071040c030000003607004410010130401003080001e0b48501482c08852861508907140d896131404110b45001d0388001411540c00443c0480c0140032040040440511940803100003401409069510640900c00540981c020b0b0004108100b5030001260600203000a54 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 352667985 1250 352666735 352666739
    0xb0a0809010f020304140f070f171f0b0306131109190903090501020d020c0d1103071208031509040b0103030f05090315061804120509010908010207052506050d15 71
    0x40490700116010b035409403018070040d5070004180b00e050f1070405c0120250804905107032692003003c8192107540810f8901001034003000c0340a00482e041c4080c604140c0d42c0409603940040040c02d910014ce070300c83c0c000c001c08140021901d4040e0b420342d0b64402088134160f0554020002144401802441080c002d6641d0342d41080a9100781000f0601c039890301100c1c1400d10b0002450300c0303483c800f002d06642c0400081d03001c0c2d54807002c1030842c0d95407014503000801140c002080c01e05a0540c4000710580ba4981c1c80d508100340c03040030398442c0d0303910300c00040c1880c14007040080d0901c094030040c00b01803050f001480841d120343c07018505828a400d0451a0510400102c4d01e015440c0c030449003001811000d0218519188000c0c1001ba80d4400140f56182001e40b0340c1c101840d221101032060103800940011307282d010760510340084c280a4000c40d1152082c2c100300341c943c607451a006106032030b4002e800810540d9140d10b1020b480c52a0b560605205100c54801c00402079000f14500c81c0e5644840 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 352669235 1250 352667985 352668011
    0x7061e09030b180105060a05030a060b220504110d151109150403060e03030c18010e0406080c1003060b0d0b0f120a050105060d0f02190b0a051b070b0a080901 69
    0xa000b00c01c81803c03080e2043d42c10000b142143c10103007515200342d240f03a00030441507900042c8070f03a100c0e401000004001d426080061011b1400001010214407401c000050002481d03001c3d52086008038042402d1601140400c1440d000601c00200241e45040b0518a07400b11030f8415a00f5103a0a2112807400013070000180b03a045a16000c601301e01000902442080740e0fa004005510f0350120056003141015075450446001e40b2020b6411801440c1e0014000c4e80700d4901c6801211019001b005a1915070706080e8a41802945040c05400c041d010311317000902c64402c80d07040717400d0340020710700300540341c018500a000d0303403890150701030403040c2c0e0710030180d4071443c41c0004094a28001c044083c0b1619216080d920020705152060b6402807588021138242c1c40c00482c0e05504a801402500c4503101c0c100d081c01c0c0341e81248a10b00703030203e5101101a00301c0028081d4500d1034210308030039020480c1d410360300e001741d01030b01541e40b1040c4024048140100c0081b90450218000815440301d131400c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 352670485 1250 352669235 352669253
    0xf040807060b03161e030b130c18022802070b090609100206040302060106090509040210121d070e01180b0303070605070c230a0308090115030b0f010807061e0903 71
    0x51021101e80040404c02903110801c0484000c50b176071822100209145031103404c80c403a001440070811070300307030f40e000410491461045e001914200400b0750030490103050100080d00310340881c0039403070348612540941807008204a11420090fa0040903e02d0500322064195000019075a420107001d0041d6105541c942080d0320014071154003d0200c0c5c58903043c000d18003441a0b01600610a0221007440300d621191841d603070140e0140c0d501680182420000c84220a80090f585112854003950880710020714801640c0d002e421000c1303504103900d0b0710b00d40031105420b20038040a40c2075410700109406164003d9a44140001d082da13040c00f81e0364960307030b041c4c40c400c4500d2000281701d80d03604e004000d281c0303402e4400c42c0c0c00b41d503004000b0110010f0b800d540b48600c08009d014070089074009041020709400c5007042c0c86000c2d0840f0f8880e5a03902d05200011016101c01c91012080720021030340720310005000f000c0300c1969944050b80c9019806c511404502d040c112020044a40720120108600300 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 352671735 1250 352670485 352670503
    0x60e130b271b3906190c0912060b060f1803010c0314010e090f070806070323040204050c1303150c0305061e061b0a060e0712060b0609030607021b090f040807060b03 72
    0x2051004600d1401d821700d5048038200761800e002d010846a042c04509002c036a0341c0740c5564800c07030005880f206080062081d002e20081400300c000000750b10703541d4400b1001940401c080a0300244105000c00b102682500c01400f650b48420140c0e07801004079040c81d21055800064500c240c4591820030902d5070f080c81440e420107246640510140300c0295410301c030741c9261501c0c00d045100150405c16084204100c0904042d00c16521400032840e02c410b2507080386c034070f60f4a80f440002603a80c1c070300d0101c0702e100a80200183c802d00e4540ca04200c1c900a0151506c100c100401082040d01e02100b0203c2066223005050340100e002e12100f00c0100c1c031441d00341d1904945000511028501d0302c3c0c104140e81800003112003541080200f0000780c012a901c2260080c0e0242000c82e0001c0d030400419024025003e05030303810300c54403091044803500450070032040c0c42c0216000000d522040107001c10000c06440303440209a03000d0001c2c000c00c13040005011103034451903010485151401c0040d20b040064 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 352672985 1250 352671735 352671751
    0xa021e0301060801080705060a05031b0a0c03020c1813030c050102030106030e0d09060504150c0605040323030105030303070309080903070803040f060e130b271b3906 73
    0x1880302d1500000118010b04508005058070b0703007000c02040c0390303004602070a0180500840828180745c5070409039401d10b501490703803580702c8845040050030414504025000760090111500305410100c24040c210108800c4c0110123464028185d220f6021091041d0100410528001e0000d01c003800158020272450382d01040b03040340d50150038144034084015505100b482c00f000c00c0100d41110a079030843d850145020625041c3e008140c452580c9000c0060132075240804100c1095006001c0c44403041c000c2c8100d00c0c61a100c0c03900d07130043c0c2c8028000c0d0790b13055105100103083d291294002074001032145014904040d00d14002c00d1500c1c030b490304180c0d0244c00110f0180540b070a02101c0100a28140c9444002040c9072070100e081c0080122013192003503200c0c0c0c66002e56480755030484400d000c1160302c40410085104000b030038940d060300c081c22214040c16000900c0c024010a90b070620f55036620202805500c20a21401d1005440389111000702c0030009840401781401200e204d28a1 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 352674235 1250 352672985 352672987
    0xc1b0315040f14370f081305030a0b060d0f140a031209170c010912020705030c0103110306010806040e070305031201050103050c040306050406060e0108010b0411210a021e 75
    0x800d1502c210302e4208489a80380e00e901495407006400d000b401e1551381d00c008400c0d1600300700004520b68442c6444400050010105104900c0412100c00024091040480b8948550548400815442c0c006250002e805240d0b0400819110700c0c042c0d441d1040640f0402c204681000150b4544580021803000e040303c0d074126103403110515030003001e58054101d2408003000070810300e47d45d80c2e000144680c403611001d400030a0061403071000f50710076010190045080b04004200050007540c4180d2030244900a000300c42c5811101d5002e4000c100008151b04c140ba825682c46400443e101d02005248a40c001c2c1ca89104412020003480040040c0d8004c0b8082d5598036020100e01441e003c0680c03101d41058500300070000c1d03401c203440540b0103613a44682c010860343ca40b030600c0c00103411150001c000c1440850000192280b056001c40d41c0401c0c1520140320001200403507400d1070043d2070400540c1c0c56098803620054880c040c030a9485117440100504007040150a201c04912130891030290000c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 352675485 1250 352674235 352674263
    0x30c030813090c0804030e01080c1206030f1614220f0b060a05210705070b0403020f0610170d1409060c01020a030b03071203050901050315030f071a0c1b031504 70
    0x140c002d0344c26000007405c0c00e15400d2810301101c8a82b0521031600460444642c14001c150305035810302c0544c1d035528824003100c02e521505080c02c04103046a111303004130700da0301c1484140c880c00c00e020b20340300c41d191510301580c00c0440d50507200050b0244c0400410742558502800040b82d9540025180504040e40c0d03040c2c9075481e101d4a40d000c40b0301d0b840c2e0111034070030080030410f034183e001d01210142548902082e11039140d0345000e914051031500f504543c6e0281004020340c850f59113240404944284108082074144140029180e0700c514602c000050380d40c44030f0407881c0110000408019001800480c509030480002c0790881c1c10148042c3c000a03283c02c0e0030301d80ba150400150001d4240840004040b03980d564004c0d01c0751180306c0810b4140000440065420207111100c003505910180940c0c00c2c005015007034980300da40700d0046076000103819100043c6090070301c3c1502c2c030411011000f424204964618040e5260350100c03601d5240c03047c0300c0c0e940f0030781c10340c00c0c6894001c6109035a1841406 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 352676735 1250 352675485 352675487
    0xc020612010821043611030f0a0c0f11070b04090b03010e06191802041d0d020c130f0605030d050717090609120c150d0510030c030813090c080403 64
    0x42550b540150f209010500142101e105010300301d04d580103031081080d200714403984107a082039180503040d5181044e00719014a070b02000f10f1041d0242c0c445842c50340d40340d00703046084804104003000000c050450300b20041d8000c1d800c04207086d030038400300d13501a592151050303619401500860405601c0e2000180142024054041000c030588064807841c0781c110102404c00305094030008020791100c09000413000380700031181c80103802400c03e0210031b99100c4584d904035000d03003c1c5401d83c4650703c03d1040081c40458811070200c40142050305841c111100fa202621084484201e181e50b03e00d0001910340e000c0010503104200758032840c2d2900302a00b82410521684c0300b0100b03000e12b04000340c051580e1420221900d500088464403641030b0700850b414641030f240c0f6081078011400e5040f03411801c0c2d400300030f00380c90041144140305d19030b202d140d1203006a00c141700c010310010071030b8030a00000b5880d202501d1915040b000202050f9941c84c075100540d00c000700c0c09c4d4046110081440241 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 352677985 1250 352676735 352676773
    0x11011802090c120a020f07060606020c01090503030906090f0a0503070303110601081204050409050f01060f03060e01110304022e03020406020c04060503030d020f1b0105100e060105030402010c0206120108 89
    0x1c2004144110f042c4000c91800140240c80204a940038503400076070810b401800c4c1d82900c82598100204120290319440d01039521000c03150b10754049000b68400050fa03290020440f44083c80242c50030f41000150b100344000c0b105040480c13a0701074441031010411f0b0320304204140003140a40d49450f0950900003420741403480c180c10500d5560001000200c206156004440499009441c000790504190814900f88031354000d1800c020350908200040040202540d141920b0042c2e004000c40c03a510340c02c0e9030895507a04645080350303800384001005860120540380f41c50003c9841c4600380030300c601d0605200aa43c502c81000b099000c10306010f071950401c05040ca00c030040d602000311a00780030000750303030340030741465040400d8001801302d08540101d03059412b4458030902c05c40801c0032602d00c480c081c01c81110000f05005440e00b000820b48850303040d01e800f408068568900d19191500116204001908140d070081d80070424414110401e40041d40200398460241121100719140c4201c1 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 352679235 1250 352677985 352677991
    0x70b0f180d2306071d040e151501030605091f030807060522171c0e070801320604020403080703020106050307060528210509010f06241101180209 64
    0x480d500c840100f0a10b242c110382a0310b020490031144c095003c6501d00080c0141c5407203c0608a503010f90312910003c0007561446500882c0c0c82740301d02c41d080b05500d0045080390010f2188941c4007a103030f00800c6040b04800700000d10a0010002e824040c0d03100c0d190040b09030f002500817503102e40d0301c0c42041061a142c0d20b500110407102400000140c19549420300c80100302d42d0b484650b00800200003000d81140c0d420383ea0211f00469092255203015071540d5142d141030b115002495003414942c2844131008400710b58407031241094540f03081c1c41301c280c894544400801c0c02d5001a420800840450801b0003c1e11000e4403e0b07001081c2203040400303060900349036620901c14481c0a1109005441c0190140c015181c0301d02c0740c003003818003042801c0728a0605840416110541d0120241088030729400c581e100320b440350000e01020903444c090704101c41e4a44204204070b802c0b095101030121808100d4402003001d440d100c0c9252a09a00483c00c45c1c002c09230201c1c1401425000b001141131605849034 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 352680485 1250 352679235 352679303
    0x110f120609060d0201080613180515070c060b0d15020309070b0f0906130b0f03070929070f06020d0b010e04020a02030415021009150e070b0f180d 64
    0x160030300001080c8281410f10000b41885064400100181c6503420340015a00d01d0380018446168201048481101e00c18420b89082c01002c0c90980140d09040a641c040c03c0141d582100b044e849469410013011154500c070382c0440e001100b4800320308100d0003540080d02c05180169a400d2440d40302d85005415402352142a50501c0611402c6120382e0540d101c8542c103441169aa250812000c0a1100203822480311840042011284030310048051489024141c840e425070980b607159175100410181240749002400361101c980500f80340c0040e042c864858840f000b07030030096503120303000d0380c05c896000c40c026991030b81d043d41150f91202c8100c11034102074400b18640120742c10020b4880c890313802030458482854440e0a50b880c401c010182000c410141300700b041d0b1046180041c0ca500051000c5440d43d030802d1080300216501180880803110392400980c6400e200c0340342174035503800c405804101007494443c007050b01d8a82c1c000c0107000e0303482050500d40b05d0505980002c44406900c203205 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 352681735 1250 352680485 352680499
    0x301050103241503030c050d021f1e0504060b0a0918060507050f0c010501060f05030f0a0c020c0a08010b031501140105030c09040903090305071508010509060301110f1206 75
    0x204620203500c9107070042c4070058449200d0b15110301c00c060445040e07a0744038031218001c0007007070650080485c40381510600650300d404401d000b04aa4032089080000e140070120503140c100000c045e40031020410183c083d20328200c1507440c8000032100304075800e0702c009880e611240034034600b840d012000307001d081c0340c204602421050424071052030164000c3c0542c0d030b680040f96086002d1803c2c1c0d4644110080d10550b134074a0760340b401d4040d00c000c2c411500440c0400c600710000c41d00500c1901c1c41244a5801088079540b040780c0a4003400a01d0981c02c19800ada54000080f40c640440700000740a10400208902c8000024503282141114a1104d0618030341c0052000016004410018441c00d02e81207841c2e4456003141c00d420312510404d83d50141c0381030b44400405030803800040860340108180c400d603e9403040e09070003206c41c4480040004007400014004c0b0b00d4040b07015608480e018000040f041110401c1d405c496200c2d1480c0e0040c200c01040001c884100140d100358060400d440c03003 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 352682985 1250 352681735 352681739
    0x140d060e06040f050618190804030807080405090c04060503070e04061503061d101202060906030a090302060106020313030204090c030203070308120705130902280f0e0415030206070f0614070e03010501 88
    0x1a600d0700c16100300b1442c0e9000c280e0347c1405001e5404140d4010b1078204200c15078492452501d10304a60243c42964002d00c8500c0c00038403466014415901100d0151b2685495541c4107a01140c0754108010382a27406940d036034003c200f03000307401c2c0c15840242c1a500e0004502d428403124a8040000c4000c6000020614080201c8845411484421034002280002c5114a51302c0015101d0140d010300301e80290300842004103205040e00000c403418082d400399005a6200d40e0121b07100d115003070f03042121030a4848100b00504055000c44441c50188003440c102d1030310ba60019050956170ba2050340d41200102d5a1350002032180c858a800104904200d454001618640303280f0f43c000d8842c0c080010743c045201500b541c243c24068090a071540c0d103e4210300304060000d0002260008900300044011102d405941045d00c20f4600c14021010f42c0c2c1c2501d840c590800c0b80990255104130740c1070312000454400104107024918a8410b201c60b1180245490100145034440902040348203078100001 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 352684235 1250 352682985 352683031
    0x60e0115030e011a120f10091b050a17030d020a050415050306030d2001090b09011109060f0c0f0a050a0b06060a0806090c040305030403060606030b0604140d060e06040f0506 76
    0xc0150744d0081501ca6004186800c1040340c1080982e4002c000c06004084484840c6017076680328102c0c00307100f600c10070300300012881e108141400c80c0c05110f4100c62000740c00e2011885044284030117280b0032007101e00c0d0a0800380410107a03007040c5441307030104074045030920201c01e500000081e1920203181a90640c078241d40040d41c0c3c3c0e8400503010b414484034101240d101350104811050405c18040203110856007487c0c02d80048000320b42003041035190010700d54809680004550090b0001880f141c1090300340310381c4c0c403034a81c0243e040b240c8910035014031000c180420300c00000640e0091000d004401c400c0e08045203a140010a010711800d020008080b400e5000105190802025500ca1007a035650245071f070720a21131a08082e1061202060020420980340c1040003594065901804506100030030300005000718064203c1200307100400d40070505003551400200e0f801020085040d00c2c0600c05241001010f903415207241d00002c5041007031000030040c80d90406030a1030012214190002 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 352685485 1250 352684235 352684271
    0x70f08010c0c050a0f0f05030313060515010903060f0b091911090d1226150d0807110105070c030b070e0303191404091104090c30060e0115030e01 64
    0x8004141005c01d0740c1203400d018000008000099200007103035a00c5c280416240340825480e5000c507030450074500003c011a00d41d003c8103803645410303190510320f1130940e0b603040043e007140e041c1c22034411303964581c014071a5074010070903000f025419203400c1c0031420314018906444000e901c64181490400255010392610000e5522158118808442d1400c08410491f80c441c41c504100b0840c501a01c03000f4894014205414042d0354150510700844a00a0500c69501213088000d00740c03140a02032000455200034400350030300c60502d0300324a07000d07541d9603131843c10180f90019100c1080d928100444182c2000100138080e604800030740c01c0900c412401b40c04255554440f01c01c220869a001321040e40848c15036000e080c0b0031000748402140c0580d10100354100b8804c140c400743c1004902e400d903500a07609031808036140310035150b113007044101c10550b50158110541c446a55000c0000b4600d04410603d0f0227003081a601c800400c612540060544200058010310340e40b402c83c0c0317a04038550004c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 352686735 1250 352685485 352685503
    0x6052a040315022a0c120d030608120f030a1107060903030510030503040909112809060e220b1504060b0f030f060d0b070e01080702031603050903030408070f08010c0c05 74
    0x3104004c50b0190124040e820301000c581c03600d40110309005030b0070701040041052000400750340d800f0890075a031642c0c4c9a60f038003904560426001340400401c50192020f200440d40710009442c081140107104501a4032503001d0541940d00310383c1c0d41d54920400d9858042c46400204440008000a06603151a500ca10442c8100701c00c1ca59121441d808000d02d268007081a480020464a41d0080346030f06000c504010300503408940301d080c9408a407022052241506075945140b140704130703681c0c0c21a1000c041104101301e50406d1418030440c0b000901415003c2c0c03107940a452010540200300741800151541604050131f40007090180c03d9448041c44150380d4490045001c47e035042d1123060104281c03031203494000d803492020b0000c001c3c0d030941040840c0ba001f0020790b80d07048196075000d02240c883c0903802403880e0b6007809101c03a001083c0700300c000e8403104100030b055918182e07841d0545441e00d03c0c02d41c0445102031b11403a04000ea02c02c2803282c101d0501c802e003461760a04103260b888507103420315a = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 352687985 1250 352686735 352686787
    0x91508190b0307090204080f0f0f03070219080d03150501030903020a02060a03020c300306031b01090b0d0506030f070501080c0d140a2903070306052a04031502 70
    0x600700610903581c04100040c02048038050440da550307210401c0ca40c0b5201e0701040108240301d4814030030410003000442b06120101c500246050030600d508011441244c010400b188071404140446c0f000810b21102450080540f0001002c9242005160550400e60711483c181440c00040c0000310760085a050324140d03044507851340d10512040294000d000b50018042c00c0d102d40340c00300301c001c401884091070030b090444030110007105903c0c0b0100144411a9116015008840d80484100c240040c070522805c3c1410110400d40e198801d200040c1c0082c80d8a4001d952240c081c0483d6007024001c2c0c2d8229000d01004e081428100000a0000742014015050700f240000c0e0a0305400070941c005034164120010b40f40f800d0038158072401c081d040c01c86102d40c1d0400f44840602c1808031100000307044810140c05000e2179844c50b1a0103005000007007949060f20220400c91200c01e031000208580d001c2d0b402076090300daa0441c10720349042010103412100310381c810801c0030010a0f0400300a4202d40c95 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 352689235 1250 352687985 352687991
    0xc03120a06030f030801082506031a1003060e0610020c010c150504030314060910050f01030e01141e060a0b09010309020a060905031020130e0709150819 67
    0x20003142200428040e88080d00744149031a803c420140e02000140c120349000c404c030341040484800800c07513500902c907041020300301c600c01040700c14000d07049010120106400885030009440100340380700000c0541d2000640d03952402e02081c0f00b4403807865003010059078450009504020007039512035a01800906010191440d0010031030804181d80c1c120071200700a02490620385400f0b006407a5a108550115810200141603070070241c2040307100d04200002054010f01d4041032011064009090300e04041e200c56000d130f103500c4d0034054124500d03400c1085200601e003940644288500d0240010b03420041481170001039500c1144807000d03100a00c040c59a2155402e006800514004c20300a411103000c4100054064008080108861040c4c0658605900280d080f000300c500c41852245982154658810300c50800b0002d0064807080181c4c4460719600d81c101102582c504644410000b44024401d010640b108595250b150300e807070a100021341840c401038907035030554450100c8980c4da = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 352690485 1250 352689235 352689241
    0x2202090a1e06081e010b0a080105070f020a1e15020a0203030115020d0806010f0302160b060102010e031207140c1b1009050105030103290f07200a020d08161103160e04150902130209010f02030c0312 86
    0xa01e17410d1142c0085101042159526401300d40651a604244a22026046002b504416803800440c10100c0c0e041d00350782c0d400c840d03501c00e001562080000e46150003099800e000050300450815608005a4000c46030034500b4034060000a0035070361a202100c1807500184003080140a15025080c0c00c0340290810316000662600c041c46507024641003104a4803e00c40c1d1228940038483e15450008010f41c2c82c282c0750703d481c84060707400c0503140c81820f0028104000402c082001c104d401400c031090032040d2410b0007510340d04103132040d00030360341001007545802c140300c1c5e00c50308940d5001d030050080391180959222209240d403104403028000c0d000d1f00c204c80b44281000345040444403000d05600030035030706607940e09090456000724482c10b4028422510104804070b10100843c00b00d0301d170600d4040e0349039119a02c4000700314603001605036079601c86d5020001669140c0d0341c04a0544c281380010f850f4140c0100050444000507100d40641d0000c0107142c0f004403012080322080000703000b91803020f403 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 352691735 1250 352690485 352690493
    0x22407111305070c0510020406020304090b04020d02030405071e0b19020a0c0b09090109060806011701060302060d020309011409062202090a1e06081e010b0a080105070f020a1e 77
    0x40c0700d914012211440d040400c15219080b030801260a401a0f0031110100c0485296000300d01c03e80c02410302680c424030042020140c0303a0400c8841081c082d01c0075041c00c401e00b61010a0341c0081d42c041b035a5801000c2e050004840381c016400c0c003110180407000c0c65030700e410050328651180c8510310881040303280c0e10300c113040d00810810042690242e40c011031240c0d154142e1002c0e8012101c064825061000001484000d81c018041a206080080c141302d13407a02c61000340002802c4002c040d01c1d5250200000036030788a601800c20303088800d074056503914000001d14212101941f0b000c609070329140a10501400009403641e008042059a01c100990f00382c450001620024000b540f00e6441d1040024140b100c0c2c10000c0047e1250100d00301d4116004200d40584681c0e01681c0b81c0780d0310501105c1c1d031614074868485540d0680030000030b22200508041200c82c0d080b508132649030380d126001e1260741ca51004000720a42d01502c0030700755030030b400c0e55600000d454403400b00d58000240103c20080c4 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 352692985 1250 352691735 352691749
    0x60409050403170a06150908120729100e0f010b1b0105040807060c020604080712050408010203130506070c03080f061f0804031409010503070f120204080a02240711 72
    0x283d0003045410b403044c54040800000703881c050007960b5203005621240c00e101d40c0034a4490b42581c800750b003d86040400f450b0100c2003034001a5042c1e0701120a20012a20192a100304001c00c005120f400c0e00c8528086403281c401c160181d1000c202c4a030b41804000649a40002041c103541e0500d00c0c403642c4503444005000640c0042e000f82c840c0e9440d00c001c1c001000440130041603958800e0400340407415001200303a84031002210b002e000e2100800800b400112030000500c0d07030410504103281400c0d20303500d8040c00c9030000c031b4881c840c1055100800060003c1001941c0d8000c0243c50a0156684580d40040150b84040c101407802c00014003c6613040e41c40c0c004d4044442068108101c204106c501f000300026000d0f1400c1c0e001c00c84c00140080c258840c4000c4640c40d64060310b4480c515115050700312401d40000c1e02044c1004603981d82083c0941850004100620250000304070307081081c0104003c2d642c82c500070b524a1035a0781840c0920400c0f88044c0c80240fa0000b050342544001c00700401d1072 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 352694235 1250 352692985 352693007
    0x924031a06190806100b281704050d110c061e0702090708180a1a06030a08030a06030b1311131413030f08101a040b12061e060409050403 60
    0x1002d026100421400c0c000504a03100321059080a1a13590760f61861590724410800c400d03c0c80c801907006000088980581c0012082da24130b00a42d01614204050044170b0090306c00300c0381c84d0400c00a0707540b260361004080301c52484200282c000d00e008100020482d01c0340c080060b84029108032415070f480159001d45208070303005004080d00386000030005000c40421609000312131304489100c010740d80d00180021803164040b03100c0d60340b260403000f10f110704e041c01442c0da0307418801d01c10b1541c00500700303201031030007240c0c400c40211300381d81103140030700700c030b00c0024800900c610a4854040102c0c20f4400b40004603801500d181e5000400085003801805402d80ac001d8500003d400380000209400d075032894141c0a40c0d80c3d400c0c09142e07400100e410350015100451865481c8005010082503064a10006132401b00e00901d001e0355002060a2a08218005200080c14900300701082c100351000502400040c000e496580700418009840d50085010341e0341c010341e60f40001010507000d041c2d5461 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 352695485 1250 352694235 352694269
    0x328020d3c020c07060504051503070e0d05030705010e03030a14040f141615030f0c0c06020906041a0c0f060f07030b01200a200f04090305070c0924031a06 68
    0x4c0b000d854403400380c030580c0325201e0305000d00c1d0302400c000045080b10042c0c0b4000c800320f5581e02a804201402c01103003003010b0702c094500780020444800040c0092041c86d803085d003880051504c80c07511122140403103199554408800c3c10743c0c810040043c0e481501d25101075030120b0765259025048031141d02d0006408030b42c0c00803c142100c040340903011002c80d0b0355000d0355580d0902c01d0180193b41c1000341c42100b0781800c0481c00c00c0041e2400640c403034002e00070710000074208070b007480e640f8030081c01841d6920511b80c4a41c2000666640c200000303003e1203008441d220003c0105080c20301c11a1b006180043c82403013010341c0e42030300c3c1c0303030321f078170804a01403040f010110840711241092a46611034080140440b0040d4080a581c14800700c8a101e21100c510300a288401000b1906c003808042d04843c60202c04000003007202c040016080290700000e00000741000410108407000c402c1d40c448444012000004002000c10014004914800c204000580d51100c503844200102e00d80800c2da100040d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 352696735 1250 352695485 352695493
    0x1170a020127030f030810060306081e03090607110405090102030105010c0803150d300905010c0512030c0711060f04090b0a0504052e1a0328020d3c020c 67
    0x30074164461b0029010390350001c0414500d9a490205808544c1c0c24840c5150681000c0442014442220401c04800e03043c2d2059034680a080d0000039201d500641045800d0855846e000e003160800c1d110700c0d948006000c00852442d41003000290103a1b15105005149201c0000015480e0f00d0038201c043c0c000c5030103040c141e00702080c1d10704220240c1501c07003400f801c400030380e44103103c50b0348041e100c140902458a0302d418403030402004644032a1403000a0b94188200c0c403980d842800507070011442000001d080079200c400c40c2c036084012403c1c02003030500c41c034400d115160080c095070f03044500303c0d6040c100000b1040c03180d1021a0504403254016540180384c82c08104068060320350b0403280600c4401d040a44000180020070000340c2c6000359151450014552010416003400441d004000d0002d09a51000c546d00800585180c109603124100e0700455009081d640c540548a01c0c1600004055405042d4181d410700755000c091032082d1642851141d0100b040c000d60482d84618082026a = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 352697841 1106 352696735 352696763
    0x31f15051c030e0d0302010b12010501050906040b0f04150815012414040b12070e0306040204320709050d120e010e041401170a02012703 60
    0x21800d0000510f007880b02c0c0c0d83c412039040d0880344139a001240007039440c405c1c49910420190003050582c10b11006200036030352038018039070160050708e0018040b40c14400007900c0c1001c0d5803c203500985040082c9850344c00c8042c01d403050341c403600103d441e0341503c510510100e0740248200c403204400700c1341114114850460b4800c02c41168a4007505280d01d0110719000c0d41c4c00780c0d2184101c0300c40050484554a1582ea550740d0091480c01d04403c9852000046501c0e80c130001e01c0240328503981c0d004a44910b08101d62640d910b507070520b00031b03412045120700000d0401d0a4a00402046164100041d58908040024002a4400d4012a0164094000713441c1880041c1003141400440c1001e001c00e52546e108107101c1c00640f50004e0756651503e5030360f040411a5064094180c5c03c104010f6025036044400c07a08280310010000c00741b00802031609419403065040100217031410320304 = true := by decide +kernel

theorem cover : BRFrame.Cov 352517985 352697841 := by
  have h0 := BRFrame.cov_init 352517985
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352517985 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352517985 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352517985 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352517985 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352517985 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352517985 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352517985 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352517985 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352517985 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352517985 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352517985 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352517985 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352517985 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352517985 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352517985 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352517985 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352517985 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352517985 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352517985 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352517985 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352517985 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352517985 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352517985 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352517985 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352517985 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352517985 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352517985 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352517985 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352517985 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352517985 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352517985 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352517985 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352517985 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352517985 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352517985 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352517985 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352517985 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352517985 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352517985 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352517985 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352517985 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352517985 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352517985 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352517985 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352517985 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352517985 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352517985 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352517985 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352517985 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352517985 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352517985 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352517985 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352517985 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352517985 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352517985 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352517985 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352517985 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352517985 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352517985 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352517985 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352517985 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352517985 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352517985 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352517985 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352517985 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352517985 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352517985 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352517985 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352517985 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352517985 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352517985 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352517985 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352517985 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352517985 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352517985 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352517985 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352517985 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352517985 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352517985 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352517985 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352517985 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352517985 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352517985 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352517985 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352517985 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352517985 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352517985 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352517985 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352517985 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352517985 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352517985 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352517985 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352517985 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352517985 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352517985 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352517985 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352517985 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352517985 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352517985 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352517985 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352517985 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352517985 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352517985 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352517985 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352517985 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352517985 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352517985 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352517985 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352517985 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352517985 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352517985 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352517985 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352517985 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352517985 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352517985 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352517985 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352517985 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352517985 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352517985 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352517985 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352517985 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352517985 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352517985 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352517985 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352517985 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352517985 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352517985 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352517985 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352517985 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352517985 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352517985 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352517985 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352517985 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352517985 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352517985 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352517985 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352517985 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352517985 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352517985 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352517985 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352517985 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352517985 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352517985 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352517985 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 352517985 ≤ n) (h2 : n < 352697841) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
