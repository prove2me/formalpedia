-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2751
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:38:18.279734+00:00
-- url     : https://prove2.me/submissions/ad765386-723a-40ab-a220-79ea8521583b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 494604316 ≤ n < 494784172 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 494605566 1250 494604316 494604329
    0x70510050a0c0305030c071a060a230105070f0614180a03080a110d0f1a06040e010e10031b0306201806070812011401090302010e012712110d03020304 66
    0x80c0c580d00d50440c04140347c0f103120300041c00c1880e00041001ea40d801001c0c102d100306400c03105004442d07680c8205c40703403078091a64640401d13038600132403d00c0e40d80640050080769003e106046031076100c81c0d491600310707005002c0390041034020004110100610038016459140c030070020706402c03c00c3d650050300803100a860803260540b140344000d501516641a9580e4805025080c49610200305100000300b401c11a10841d0b00d07480c1640c620b46080420880f0101c0306040c0c010300e010380ca030041804040310301401d00e41d002030000300004049003051001001d290700303096544009034690710340030080b2a46044aa5100040d407403809141c8404641503c1035030310301c044542804084400007075664070580100809501c004600c00340d82c0440b04804505031140205c80b900106140b80042d03c42e141c0071b210003800a200c0e007404800039445510701994001088650503600b94070000b5492030601a81c216480c2860f840100500f88030444110381c0100e4010740d50b501d205a22614029240d109901642 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 494606816 1250 494605566 494605577
    0x6040201030b1c0305120a0b130504080f0f0903010e011a060c0f30030c030114130608160f030b07080907090f090b0702070f0909050f010c02070510050a0c03 69
    0x5460b03480f69007100e1141d07003584450a007460401e24000d0210703001b41d0711401c0407410304400613110119900c140345410000500d640e0a101200c1058009442d00401c12030b04090300b84105c003180703003901c400362490745006038a00e600e90403144181800c454050708440e0440e070625480000c0f84014403e0301071200030985243d956040481d003043d141c05001c403020090362082c1c898a6024503602684071100c1d02c128094850001c18800a03a98140020703a035000b200103041004005480000030744c0c09c0c030803001a00310310401031000e48030012680789a1041c0c0c0300c1d030029140c5c204540103070044000036200381b8990380c49041c210340b2000d4142c2c00003482002804001e4000c148200420422940100f200700720520030814642c1614000d8451480f040f07480c0309002000c5114240042408801e5404c58081814002d103081c00313000103820303007950030b952074000c030000141c40385020f01a50f4491142c5400401c0407924280034010b00d9440c0855000400005001d20000103030b001d50b510500a4151406 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 494608066 1250 494606816 494606831
    0xa0506040b16080d05040c090e0c04090204090b0c0306041401181d0a081c020a1d0d0209010f030c050111151b03070314090c0f0d0302160b040302030c0f01020604020103 74
    0x1900e0401010320018008000c00710381201300c001d041d00480d12a520402c81091429552008441030f13a000486a00481c3c118080011403405c1a0b07005e900050300003480420b020b0502c1d100e00c014404145c0307104141035800010460306040038004d80381c007000480d04c1040c041d07140c20a030403200a07584a0300c3c0b4003140c5924601038455103010082c25800e1503001910412061407910382040e5202c8a28404c90381100c94440400c0390003442510800019900d52940c10313250401844610140210f00c40c1c0d01141c00b225910160b201c1000b6180a00b103010b0b1131a21460030b608181030642480d500c81410041200079480000300e01007810b8440c110740b00030440ca66100c80c00601c00030408040c1c00f0202d41c401004116503107034590800002403000d14440398040e1110119240c031640f100403c1034200da140d002e810411700700078080d009030501904c15074250b080f040d4400103001301d01e980030302600d80020500341309501c3c060141e4602483c4c1287e202030b01d0905c0c14000b230b488480080029040c56900d03502e = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 494609316 1250 494608066 494608087
    0x70c0807050d020a0b07170a050706180b0609060a17010209130501080312060a030f06020304060e2e0b0d050f160302090f090c1210050f0402090f07090f0b0a0e0a0506040b 75
    0x50001f00525a44200c980f00c01034580d0041207a000000d00342d880c18181481d1030b0b09298601c907401c0150b030f0030213168100c0c0d641c2e41d41400900f0001404641d00201c040307100142452a1a0070524003900d201c00151380ca102c40803c0055110b00e200703a6402076440c003001007180c10000011a608211a030302a0161642c078000050440724031580098a0184408000002c010b080d0740254030a91040208000021445440c141c1e00e000e0140d00042600c05414210b031511106083e19185241d411004982c8020f6400400c1700345011035012591a030050582c11075101080c01401d12442616000492092540d0000f4185010180502652803100c0002c05c829180a0103145688070028200000510b10300c8a442d50320b5407007469510b00d0364500404900420300f074264160181c0e400a14405264664010b082402200070f130199080c0301500d6000185014400d2090f4020504056816101c0f051104043c10f10710302498114800c011300f40c2d05010703e594502c00d0301e047d0f48030a2250740d00d80c0c05840 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 494610566 1250 494609316 494609333
    0x1509090102090913031803030e01050d0219020a020a08010b010c11030f15011401031a2b0302011a0f0a090b0409080c0601060311070b04060c090308070c0807050d020a0b07 75
    0x589990704000040c00b04408030a0190300b9204c028801e5448404030460280101d5040505010050014003000d180e07524640c0310324064111015400340041c5000c02d83c41c0b90b00d03c12060b800c0030358056008049401c0561418550500c01429008000d110b110030a800080c24640b104074014101c028816140301d458a040140b01c50300821b0800721031700300401d007403854004c280c2480b620000904a46030400d03a03512a000301c03800040d14440484010751208100081200500f20403d461304580d40082004100b0041c44140e05000b5000010394150308905a4001402005618016001c0b00b80c409055280c44500c03404440c80c0c4440002d01e03442d402e0001e00a071000110141880c0d40120f040010044003240c0f403270403581c658030100b0040111441d00035150154540150441040301d00040104a80e0340100c5d8402140b403410490054413a83d40131141d400110096411140d202c10034048864100080b130090041154408110f40080d40000c01340d645a0040204000c40820715404014850 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 494611816 1250 494610566 494610577
    0x1260a03080c1b100e030403020303030c09061c1a1c03121e0213050102121608040e04060f05060627040e030403031205010504110711120106060f080f1509090102 71
    0x21000c100354040c0f580c1d116920300159000c1e651a03440c201702c5001072030000044404503070340980698155601c04900e04116040f218850f070300540e0801550603100503001c160955032544880004404040003000b840f0b81c00e45050b41d90013a41c441d400d82c00c02d207246482d080700071585803a000019210f0b9080d008003414002e840084035817504172074514110030341c3d0003408640f111340110140d1030b03a48000480c0c0d0f45400c03035a0a44214820400000741d024180b50b8481218040c034842c500d02607035000c500101040858007078518030f075034250070080a0400d0103a950000d1044603c141009030561266100d9110086140300340a00300c9408402602d41741c2001100101c0e00d41965201d6030b4a06003d40501c4000fa425900d161401d0000f003032034a842e01c00d9150901c1e41007880d50904403e50340d0440302c00c0e90350f030304a82e0242c040c940b20351048400340150800707070505036a0071020701040300015011007000341a80121000500030021038155003080a0040c00e01102c10f88034030b031a20821f80e402071040 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 494613066 1250 494611816 494611837
    0x30c0b090a0b091509011107032007091a040516110109020306070206090d0516020907021009080c01062310050f03040302011a03010c020c011206051801260a03080c 72
    0x60b0100020418040b4103090070705080c0e611145259074149800f4200c448070303c0354192101051141c407010911409507002c00300400007080c003081407007951003440c0c240c00740d10202c0e059403680886011034220300d111102880e8103a405004a0801008007203091601381c0e034640410052500e101e007055000d400100311160041c055410300e04203d0b10094a0310340c01c403440142031003465840c1e00c01ca44500112041c41105034480f000d410b00580c2084840301c00a0071a80462041c4c800c0300c01c0310702c1e0b00d200c4d01000d14440d044090741d841032143c2050a588090340551411011b400d07051025079000c03400d00740075001c00c5403000c03c00c42e0f240c0c401b521a4020000030181c510400f000304000c05805500102c0d203880e80c0b0f205040520032000030142611171044d60800182c200703030f2144480307500030040c40c003000065840200300a85c0310300104007080481d1140c1e5007020000f00c01000b00b11144610f901030400c001c05000e0b03d0314400380c00996202c2010600900b0004004009202442c500e000c0d034000d440ca = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 494614316 1250 494613066 494613083
    0x5030916030809030c0910030f03030f020d0e160e0103020409050a150204050a141e011e0503010906090e120a0e0a1d24040b060d110a090909030c0b090a 67
    0x200c030b003440031154120410441c020701c00d08104015915100c48aa0701ca0054009003a180906541d1002a0030034000c40031008e150321040c0f640c201070780500251101407520700b8000f6442c001c800c442464030240d44441103802d20400d0041c8403014084102a043d2030b01650082013840c001d24180c1e290129016000d8880740e0032802c802030307238800c603002003089440848082d0310f03250b21110191894001145200d91059508585143d036400a20840800500506103915210301c4403120240018009000d00000345001005000702e407000c0c8116400741c0a507203010403400d40c0943c0c00556910b00003e40098900f00400d40c2214103100f10801d400300d03d000b8000580c2182d449034080750b084022100d480e62350103004000b503400404962402d44d14048070040521240241d07003400001c003040d04086400030001c002001104a0754014854220050148980e8480c03213544001c0c4030007441c0d00310021803400c001108001c82d6100d40040141d5030002d400e14003a8480349681442d10a805100410a10 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 494615566 1250 494614316 494614319
    0x6080723040207030918050118150b1309060f05150c0a1e03120b0303161e050c011202090a031101030f06030302011e1407050f041e050a0602011a0105030916 69
    0x10b50001c0101d0803603400700440c6c4141013507030b4445400e5400074040c00b440000040d11400d07401200d82c2103e008066007070342c2d000344140c84900d40c0e8043d9100107001c59854000703000401001d0803612661004040503600c144899080100141d1485000c02d6168810340c404640540c5034002031060f02d034401e600100564203403c90708140308494020400540c0400d494503e0513014407180c0c010b40110440080c0614541214000e0300502007040401c00e8422918101f12208002003008403264900d0003600200200c02c1c851b40014011417600c0c0d0764419071401401660700716100c0c10390110070f80b6449142d420711001c81c100102c0003080329400011149003030103400000d054041d8407420240d541d07101004103440d058a09503090340e050001c500503402c95107000072010ba01c281b024140300201004182d203441e503502000e1480d000c00340f8680004100400d81040549800c0841030024200c0740002c1c400740600c2074941b082c0300c004036425410311070000000b0b8030704401801040c00100c3c25002100903070703 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 494616816 1250 494615566 494615573
    0x91e01031109090d12180f1119030f11040e0331051804080708030124030c021506010e030109050c040b0d0f0816060612030207060306080723040207 65
    0x107080103451a0300480005022642c0b000022550000042d082d480f00c483c02c2c00c06400384402030007080d00c0d0800d01c0903081d00700c000007003c00d92110022402003002c4003480c4194420007501102045c0010070400148a041001400810401c0c0c2000d800c4200c500c030411101000c14040d1165200441c501d00000a4001500080000c1c1c02411500ca11800d40365a9582480c0c00b034506990140a0740104d0b03041006080d102b01d5030304503500c544144690b60800d10280c4d241802c0da0801e801400516009440d40d00400c06002d80004608070507241c01d00c0800c00c8500f010303483d0b10b28201e0030f040940c0d061000030030700c1e4010f21722240c800002600802048450f420860707103460101102c40c1c4524149002000c0303d1400401c1203201e541c0005095002d050b803036a075501154802d64155a6218081c144500403805c82c0c8100340c01826040c0395120144480e03d0001e080075200d8000c0000d0518201c1c2c14040c2240010303c0d00c083d24039410400716055021008410440c006107015a4090300008901040 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 494618066 1250 494616816 494616833
    0x609151909051602160b1e1603020c040b0d030c020f06031f0506070302060f0a110310081504230f0d0c15050f040206071505070f0f0305090606091e0103 67
    0x5900c1003503030800c0c42e941c400703004c98440000c1c005640340b41c5031390392043c03010016401c000d102c1d521450001401039040409006c04940200b4110082c0d0413102c1e4404040c56018082603d02020071601005502c0003140013a5242060178070180801031512044c40454581c0300403035030010700c008c000310340340d203400c006c044000f608082c0301d00b40b1618800070000301401c2c41d0003a03c49440e80358014000715502c22004e081032090042140424a0300c4400a03078003001c24600131405594003038803075990b0a04000c04a460550340c51180350410301000308200202d103032006802c202500810020607000f45080f4068588003101c7c81440303180c003501d905c0e01038403604080e02000c824440d039041041340c00f03812402801c448045501d0062131301e26000103401440c100d00100f03100d40c03003403052800304401c244a4100300c550881e0303900082865011303050201c681000d14103002c0c0762545812f01042c03078030f003104070f8441d40003800e80f40c05442540007080b0030014222001c114500250116126581d40c4e0405004 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 494619316 1250 494618066 494618071
    0xf0702040f0608150c0307050a050415050a0801120b070e010509090f040309150801090b01110f0d03180f1e14070603110c25050a090b040501050306060915190905 71
    0x505200d910030080445860071132403171280c0700c2d00307040c1800d42e95115416500f0394851100b00b000c0140402000c945080110400c0303924001542d18103840d020345010140182c4c9041e04840000b0009455110008124500f5030307a10035058075180710000041801a1424003c188946510454a00401c100301c070700c0c1702c80b8602c114026a01e10030729a5030f03017407001c001144189580c00080d04800c0180030f190116040f014001c4018074044d4411201c2003501424080080c05100d03841c0c122100c4546d06990500038108141032142e42c01450700f600d0b98441003516503a0200400100e1f01464a0800c84200010300c0c20803908000d0090798107a183c6200390726210b940c020080483c1c84e10100c0d50081455205440d00d0160800080540030f84641c2e10b1251216494100d40050a00c01e2021407a6118050804000c0c00c1d02040419060305482c00c020540e18149c205ea40641e200404002855488885041c2c0128140b00300080c840d0b45100847d000320512440040f01c0c9240e00000220a032980c3d200c5803 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 494620566 1250 494619316 494619329
    0x5041a03060c0a1d0a0504020415031508070e060a0306060b190216060c150c030b030c060705210408070b19020a11060a090f06181202010c080f0702040f06 68
    0x51282d41c0706120b0754410300890107101e00241c04044000018200a06480c43c0018000c107600705d915076446c002005e0380d002d07401c07203111180d00c415031031509600350040d156801d144031000142681003503541691103030180b00703544081e03140031b022410316120582c681d006140c001c40b0a00c64103480354044292580003410034004814401c4016902c10f201146000406820601d01402c0500e007401c00c0790101c1c009042610285010909070014030368500c41c0c102c002c2c00c035440100c0d800c0310000c02c040c20000d038190035900500d010002d120000e5030115000c090f08441c00b10b149103007104294260b019000d55007154903240300301c500102d18048400c0207010000ca030501801c042242c3d880c000c9884070404400100302c2c15141a070f403007451030860060283c07642c3c01d142840d503166903003654103202c04007a8450700c08566002d0481d0505510740030f05101800c8986944000c121160780000e140c409880006006620049040301d01045410100d40110341c0081040c0441c0c00380710701c4000107121602c07907030 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 494621816 1250 494620566 494620573
    0xa0b0a0815030604030c02011e020601050a06030905030301090507020a050709021209031c0506030f011e060602071a0f0d090c0509132a050d051605090112170405041a03 74
    0x742080c1c407103249042000c0e00c0540904081d80741d5540644028030410802c90500c004401c00310f400c058088023100e803510641c0d008100d55458101840181a2203030040002c050800e1a9400810000011070381100d4020700001050340c1c9050003241000001c003401000303401a8800040d41105075000340140798650110100b5513280e09940c140d0b40d1103003014000108640108402135003129500c550380c000c0c405010f5540c804505541d840c04c40e007078440c0c402d801d04261901845542c2040c40340c0b50241142d4002007030600d003000e581e440409484400e19042c0a00003a510701080149802d4a0b44a40ca0b0b41c010f01400a00f80340c4804401c00c03134054680120030150003d4640c0e00b074191002d211a07001a01400c913220303803a15156508203105980c0c041003507041c1000a5580b0344c0020720407814022405000d5040800c59041d4032414a58011361264003004014081c18030912000c1d1903695000640125105904c510700d0b070b00380520383c000c03940709140c0100a840c4000942c0d030741c420008124141d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 494623066 1250 494621816 494621821
    0x2010b090a0c020c040923030c0f2b030f0e1f050c16020406030b010305030a030501080109112701080a0b060a0e060909190804080d020606090a0f0b0a0b0a08 69
    0x71001181d01c0c802c01080140d101c20343c108954146a405007820900840700071108400c0801ca1035450303200104658030951001400001e0b6050601500b6a044000000b070150201c2da0704042000c640c1014800c050b88003484900b07010325001e03a00c40751817072010b414103108081038002d0300340d04c0f240814ae01d03071041610524a4024064a0b1103454801e1540c04c500504105141c0030381d4194074000081282c120307a4505010010415004903603000b5481000119903070500510018240e88069100b1344844e8100032995000900d840302000300844140e814000d440400c65000c00b0b81605c1951190a8812100000c030740c140000c5441e02d0381c90700035002c0810f151140c0040c0038011259105100a0b00d40500200300d00d846d1058a150b000113021080741c001c4403544001030f4048035040343c2103828410019040000100078850300d281a030f4180040c058034139041c408203005010080c842580240c0d11200f03480740541c0f65000003440c81003d40880e50560300c5040801c2e5a40c012507030381c004191807200 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 494624316 1250 494623066 494623081
    0xa031707020d08070e0f090a050612010513080c011812090b040807052403010605090a12030e0603070c050a080c06101d040816060c0818031605120a02010b09 69
    0x14000b41c1001075503a1508140d54100040710104100441150701244040b80100300e542c0d42d050076401000010380000e40b506050301004000490401d1100e00c99050004209181c50491601609649c00c8a10181d847d003411600600401c0014080864401600103079024402441d4550041384019198a1313543c540303032403100600303009901c40d441c4160300c444030a0055003050500e0644249105100030340b511040c520ba031050350403d07009034002a01c08140c9060318a02490401e00410511121074002c1446440080022212400c00c030300680380000030036a0b65100e403550044054002003070324081c42c010f1074440d01d10383c401c1c808180103109100c00300302c40c40005108142151600c23002c03c00010341082024440d42e20051040d42c4aa1040c46040100c071160380c44420214800e50001580000000000e003548002801c802e0607488049a0341c030300e10b03d0020440e8001d00a80d000341000011916106240c0301000d10800580d26000c900c50441e9030b0150802a90f03a1000c0741c00c480c0c030b503031402e0707 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 494625566 1250 494624316 494624323
    0x906190204030c17030c030a05130f05130e0304081f0b01031e0f02040b03010303030b03010f15030b0405030c01020f030a050c0306130228091a041401050a020c030a03170702 76
    0x42d080418051080011343c10211040d200c200380e103000d9900340b0140307014690031a00041078180211750b0024000008903210801c940c081e004065040111034141004900341070910404800d8065560488900502041040d24014400d030400c0b82d100d02d0501c21151010603c0b101044456400c0c41a240001c0d030080c000d8220810045142e0320000c4c02c0e41c01031001521440e00100d5043c0d6081101140c60751074800110b002e14020b460106103c501c0030103260071a0400c2079290302c02450540400f1506080c1c1d503c18086a40150f1003d000e80c456041c068203500c244101c0c503500758800944031400070784140155100310000c1604000c185d445c0c200c2c41810784012155142d02c4085100062503e104540c0581541082c0070118841c140f5695012840c03c201414010049104da42c010401c15848103456289904607030445818180303483d030300440303902d800700c00c86050010105d14a44600d2003001610345100000301114407101c2d4908000c0d2010705000310b04280e40f40c0d040009044c450002 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 494626816 1250 494625566 494625569
    0x108060708190603021c14060603061303050d0f2705060711010902120313060203070f12022a010f1722050708030c07050a0e15010309020402030906190204 68
    0x546850707406503958800310800c0d00505080c4a58140d8440010000d43c90700c1c6201c0700c03560000c80e50241d50000310300f401a40718400102c040c40c6a0300c02c038108440d5889c00308403141c200c41c1d0103054641001c220f240c2900c080c062018009521071030f209125450003519000488100c5a5000188035001002d600f00582c420412014180d035100f44003141d02644210f20005100030101c1c00003030480915800500540321030460340e41260300120300c0701d05800381381411000a02c010700080d450603883c0c0d52848a4400310407006000e01c92207040c1c803081c541c000c0c000014203031a001090840400c0c0d0272984004c03070310070156240c00990034408441c01c4500580e000b110046910f2148030082e559055900080010b421402c01202d40344000c2a00140c82003080c070002d40000c002458440d0303031300b00440e881d140e02075000c24813070b0f0040a01001901c0b8404d03481354000701c6840c04100032650260060300070b0942600e00a4100d440001005110f07a404507807140201140c11504949244055003e4141d0085 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 494628066 1250 494626816 494626831
    0xf090a0905100b0a1d0c070213090308090c01030c08010312201f0605060912100f050f090c0904060e01150b0a02100e1902030f0105100f050a030b060d0c0803031e010806 74
    0x105c0000c02c421201d1800a802000e1009041c2a5035015840c040b00a49401d10001c42c003058140017400001c2e03100344401048890700b0305cae04121440503070200414982d8188070280071028070480c420700440c815109083c41c5603040c803d080e810030b0a11800ca0707590200ea80c15440311080540f2500d07850203035014100849100600d900d003032a6040080011100c00c00340c1c01c5003284509060111058601d00484443d110b404030005503c0c83c1031000000e45010003460034201d074100007080300035955035801094005070804400111000002d00c00e6006081358541d4010490000d8030010305ca01e5110000d0904000e0395007074480d0510140101c0c000e0b903d11101003c40b617042440c803d46820390140400030000c1c001070441e4031400c4902d0525084a1054410078541c0c407441600384400800421070030010310003540c190460754038540b564920020701905103807040120a56071401c0c0640510208050501017096035907034108850310701030400781c8c241c0843c0c000e0140000000d9040011821501c185d05 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 494629316 1250 494628066 494628119
    0x50316030506061c09051b03010509190f1e060e37050109150b0901080d0203090108070215010609170a0503040311120304060c06050609060f090a0905100b0a 69
    0xc80c2ea5144c07107040f030713800d01c5645a0350700e45841002c07500c02c01200c0d82a00c0d41d0174090400120050605081d548001c044094543c01454114070030606070301c0d175101d1640c03c0101400d1888046c6440301c0100700784504101491070301c0813518144071443d40400700a10034141100c8810b400c007021100c0181c0f40c821101c0c40300780d46904490f040f102d8490743d00c01283c440c1c000003400c00410303541c0107105d090268100200d969100c061007541c1c201041c1041c05003c0c801700408000014100c002c0d40d0303216084105041101d0840403541c01c5000300031712501d012103e80d581d5465a103415008000c001e061113504820f402e017244c42c2c07041e000080b036207241032a08100903518050442d110120440780c0c8a0010740c0040c82008a10b5000100b40040c0015001c145d440405443d9581823010651300d0181c869071107415240301344101540c0d0601442003080068950214650ba9820210000d08400e50058581c0c001c1c0ca82c0b51801800300c0e840711802400403030340000741036100c603540b0034002403040da400002d16 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 494630566 1250 494629316 494629327
    0x1142205120c10020c010c02010e07140618090f0703061e0b0313020a0b0403120543110307080a03050d0906020f0c0a0218090304090e0304031205031603050606 70
    0x403510010004030050200f1643c0881520443d41c0480e484003c1c0c4200613551350041080160f428021062070044440060000e03074242360800391050b410406585c0700b00b02c0082d20081d0010041040701e4549401041c14040d4a0f0094014040040c100c88040010b4a080c8010407500c80100703a9650040c030404080400d603042030b8072a441c80c0d00242c01c6807500303050803003c0d1005a4034051418044d241d2091070070746540c035500c1c2011800d0400c1c6281014080c0601011001a4410300800010520201c030310707955200c45090805e04a001840324010804250603031418011144449641d0311810340484403c980d640c05255110104c03c94010000380082000e0340748042650041d620181c040e21005141c54004c2c0c1e4030000940c040d101651140d00064140e80548c03510300b100d1001903000da801001240307001510f0948a00c44c90058800080e501c0c52301c044082d0040082c3c401030341e030200b013034003100b070400d18054050b42003291400d140c000500380b0711003036522034046d007401403001078645800c11 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 494631816 1250 494630566 494630593
    0xa0608070f050d09140d030e06011a0d0b1201060f05030f071203020304050a03120e0f090a02160c09060e0a090b01060e03011b0e12011505010e0a030501142205 70
    0x40c2d0107408900481600e034503041c000f042008005c3c0c0300b02c0800c3c9005201c1c81803914005000c0e11480300d132500320303908400010000302902401220803a900500aa0740d81c4544059000041036107800880c1c200c02403042d40800b06a0540c03140058400040301c6c4074059680e4000c00d5915840071420081607004842e0800c00f00ca034114041400c144a401a80e0034582c9a2001c80c1e402091507100b41c1f15031011302080500300d604100c181c20101c0c0d003525400c8a03074420101080283c10040e205103602c2d40e0004011020f000c812084030300f0190710480c012186985e50030f158000d032080727001c0c010950b4803420108a4843c400d12642241680c800080c0e20280e1038205c003034a0a8205800d041c0d055501c51074500d4030741c1061544411041d84a4545628101313101c828042e403a00442d0081274030b03a140ca0a90210944008019001c136842440d28400080620012401c1c3c100c06600013002903013084a4513a40103500d40b05c840c4160041900e11041c032441c101040440b80c44d0250150464000e025a0142c8 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 494633066 1250 494631816 494631827
    0x816050f060d090c03060f020a110625050702040e0109170403050709021c0f0c02060604021e090103020708040609030303050f0402060318190f021e010504140f1305060a0608070f 78
    0x54000c2c100c44045507030381d88529065070300540080610039400101c010703449d074100380103400035625038006240301d1400ca900c440e90408009010f00b0360b01c03148044198824813a20031114401c1c0e02800074827810301490085030103400030300c0f81201c00e09107201002080300d0b055826501201e403c20300500d8081c5c50401014029441604030110500c00c091940804140500a4540c4a840e01c04001910610113400908181001c0e180d940304034010800c0c00c900051200c08696a101c801c8401076407034800030300507002881112401040c804011400040d250781000c0340d1404c69000703031403c3c8a0b80e5a108141e02480c031048070000e60003d002d1011038105d01e401d0207011814113480c003c640c086141490700601c2c0c005602c004544070003400380ca1604504120140d130a080d1100801800f40030001000a8050300883c02403030301d10081080822132503550898241e0101101404030340ba03401d507031140300c005003070708440c5d680c002c280c00031000a560f40302d09403071071007280140d441d6040750078070003c00c0341c0303 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 494634316 1250 494633066 494633081
    0x201091502010f052a0936010312020d050a09060e0a0e01180f020406090e2d180a0507061407140d092411010f060816050f060d 56
    0x2103650720703144015442c0f502e1042c5401520941c003102c0d20107000c03400d0b0721940c540d50041c840c240141485600c8241e00c640d440c42403009030454142003a0b1580c1d0403641c0602016110954000c0001030000042c080c845584c600084080e5081d20135212805100380c441c2e1061041100000f48160420032805100315000c4026000081140401a41e51516614906401e811004034003544500c04201c0d10420f100d1000991701d00d5a01b036080601d00b05025140d42c034648980f0302010380c0d40000810103501c0c812800030a000e51041c00202155000262210400844121802d0051412862804240051b00100c0c0031b0340040140300c0c480c140700003164040070a4071503d410440a01c6a03400080140b800100d20100c600024204400103240c020070010003948808031044084107c1138040108025075458007109080c10480100c410064500525120701001141c602d420000706120381c0103d1526100800e01900704c18941d140d0040000c2140c0c9401c0965000c24100704403003200203c0e03000501e = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 494635566 1250 494634316 494634359
    0x20307150e0312031509090a06020702010c050304030c181407050f040801060b0909100f030f150c08040210030b090402151204060603020a060f120b0301060b070b22020109 75
    0x4a150381d000c00b0a14120100181000500300402004451004e11071401102c80701110b00511908280040b5612100d0300900548025000031b460f1040d6400384040b40700030740d0310400302c0740e80301d0f56404e002c40c0e00a000d0043c48450840c950324030300b5250a0f8010352900c0d02c07401c000c1185544804005841c00d50040004803440310080c0703c0013400070307028414040100103820b4550381e05d03c026400c200c1015001403000c046140e54510078032120b65003200741426a540903180c41c070b1110b40e60902240d0340081180d90000507040c00b800c0a02540d00030030040c019442030303800d082d1405d283c1c007054040d40c40c2c041456401640302c00014016241100c84001044d40001c0000c0ca0451f90000c40060403000301c0c1e094400b2500c507402041181840241c000041429240044822400d080b0003021007004080c8103440380d072a811480803903a020b45c0200700814450a00e00d135245850b1414100d2031204840411040854a4180e01030100c0d10703c116184540c16510180c0c0c0c0ca040c03044200c00c00300981001c4 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 494636816 1250 494635566 494635577
    0x180302060708101802030105041512110103090c06020f060603010b030a02270720061315060b0301060c02040f0b0a0611011b1e180504020904021603050705060705030402030715 77
    0x2003542c0350001c04d8042c0b0000140259881d8184000c0c00291001c5903010000701c82204010840c0e940058a2500d00540c030240d000056401100101d001d000a400080c002d16245000010b141d5000101c020300c0003688c105030341d00c80d034070f910405003251001682c0d00d415400c25485e8000514048941c014014040c00490500400d83c1e44807110451044540c1404640b1309e900014080065006110520584500400141c41c0002d5218200800ca24000700b24914445207070741030f4051904148050105001c07203503160740c1e41d03440003064181c100030180d024500c2c01c008806e048030039019a02030910050011011640341500c1103a4040c11600d00943e030b95640d0141100310446107151108600742c0c1d40c1d401c000950080750259500c400000d0403018010513050301c2981e1140780755120108c2d4000c4800580f02c0f038032200418068450098207081c0e0b101c0c81c0c0c00c52001c254005010745941800f940172140b49035030781d410580c0c1d80d10058601a500d40d02140701000300911940e8030060111452914 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 494638066 1250 494636816 494636819
    0xb0a030c030f05070e0306090d050f072a0f1703070b041a10181401230310020c060c0f03040f0c0308031305160303140c030f18030118030206070810 65
    0x1030880c0e0f402e07a40c2c4800100c00102d01c0202d4541042102d41100442020380b01040f40c40c5030103003080c8a001e040c4091058081080001c0c0200001c03406195040c0c54a0f01070416542ea091114030415800f4240b01e040e0500004644041a1110110b090202c400214a054031310744a40305070b140c1c01007003199900c0341c60041c4800703840d0082d115800ba02c0e51140b4103290504200d00c10b44035409441030218954078040074400c213091407035000ba045031841400074508803000700d04c803041c030f07880e01c01c90316003500c204140032101c40c0c4a03500902111015a00b500c42c0341c1c5840311500010302c40c08030090700c506402d00109006ca000d610042c2059807007186c81c131000550b81d40e19042c10303400807aa2080300d040c00301c0140e02880414025410607592100a6068503411a03901900a11100700411006800864030f6911071108100310307800e0411f2020b8140e110751801400040211813054650b01075420442c070042d00c60248160740c98480d0b4190090080ba90b80c0010495a1800003801c1150703aa491820 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 494639316 1250 494638066 494638091
    0x1e0c02190f0b0309060a0b0d0b061302040b0c0705061303110f0405011205010f0b060406080406021303050a050f060f0606070321060314070b12090106050a0608040201020c0a0b0a030c03 81
    0x440002044001500343d02d0f40741002006040100042440c20600c0c02c004145407507681d180c81c01c18030541d20028900c059214000814042c20410741e060424610001e0046804900344018125440b035850441c0e01107507c030010300c0f8050090a020400b841c94891044c400903d510050650703040014100740c0c080400c010010b4241c070000e038000c2002d140b80f129104203011081c0520503480380203940c02c0c0552140200803d255120f02d01c6040204040d0300041000c0086640403a04407101d2030b0f0810000c1512400c2c803503200e0169440444241c8078039611548440070100385148140d01d116054801903035001c0c18004c05910110084003000780c0c40050b041c80c105414003070700101c00115400200c490851030590300000441400418a41c000402040084500c604440d0300b00c09900c1120125210030903150b000d0171040d00440e60041e0300b002d010542540c85403200d40300728000d9003100c5e2401c00c01c00c2030107100382441c05106450351040214045035402a00b01007188200c86c6000a5030509414 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 494640566 1250 494639316 494639339
    0x8040b031e13020906030c0306060d081605150f090d0c050c13060f090b0f10090e0c0711060304110103180602040807030b0f09062220011e0c0219 64
    0x9030002e00c0c1007030030a0004107500706220107a82c000026002445842d40410000e5520907004040c107100701482c1c0030f40d20400480c102950f45c0d05404480d49e030942107561401607100d41846c050030550003950b42c0018102094002c072180502503541c003500e03001d02c42d10012100144500e800769414411207900c0250354803001e2059144e8840c450700010090309202c0707484e042103030562000c03005a050000e82c1300150348a001d500c1c9090310445102014856421050716002c84507403010300020460302c2046110a00c0c0303402403420901c2501c17610980342e5a5020803203240410344001d0080110100f00f030300f03203502951085170301203507606204502c0401982c0384002e1703030320641151075540c00c6003000b001000342c91405650000541c20301c6c5d040c81c1c40c0141a941c0d58243c01010040740d012100be00c0c61744100540c071072040d03580d040f400d9100a0307640d85c445040c1001d16000c0250000d807460301005071841e2100d00d02c01c12070a02e5030b2450b0f1360b0f40c40f40d005c001c10f00b90f804400c011002c03941d04c800100c1e16443c0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 494641816 1250 494640566 494640571
    0x40219030e0d030902010503010e0615070602030609010f1d1b070303061e0b031f030212060601201b130606020d0224340207170a08040b031e 62
    0x2540c02048240380c01c0301e09814034008900b214145420103600701c0050380c008081d02d040d02c4601071014415a150320018070b206011100001c0f400c440002d1a02c00e100e440d4004511650040d181e041c62030340d94440a51400e0200c0c411802010b42403c2000002c42a411419030071081f035540c42d0002d10404045c8040c141c2c0219011070120f40e43d00020055109542040c0d94610703000100003015a14041005080d88002020060180ca030020035080d03065540c030340040910b402500c541405a000d0498982c0e480c82a030f802400308080484a0244039207030109400b0300000000a013480c56601210f025103c0040b2451a60080a00328a0480c400c000e200c0d5800a00099000b00390007466810068100149460b10301001d6500b80002c83c5000c0d10028040d80124075194400f0400e072803c1c00a000b240417203516004114400d4480c46443d650005401c4180c80d0f0010641e1100c0b40b0004080743e0790402e07840d004150b120103000802a02c039020000e1a441500d144840c0c490380c040001401030b00701d08 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 494643066 1250 494641816 494641867
    0x1150e01110d02101406090112031202030c2104111e030a0b0106090602060105030703030c0f0b0f090c030a0b0105100c051c08010603150306180609050109050c0319020f0402 76
    0x41411415521250140c0d5548005c95200203800b400e0100115403080414003442c902d907021142050101440741c590032181e080c02c40800c5441e03003415401c111040d80201420844440200f041003079140021480500495000d00f50240748203809040c010401741c03940c1103440c44040e543d40020303603072418442800854810284c001680d8100f07a07003d02071202d180c0042d81190702a000600590f03c0c00940c403001c1da501400c0002500502c1d00d4544c1000a074141c0003821300801d0b4042c00080d40c0000542070191400780c00b9030700403542110600d580e075644060f000c4d0640388940010403087c01c29105030240360380781e8a4018004c600caa164a4580710050307400c1d40c0030000304104d000046030300c082c206014201c90700c0c06200c40d0f00c03161032411a0000500001c1d1031999240c6c40c004583c810804401111130b88450b007400983c200c2c1c00e1030760082892107020744460042980000603840d0108501044103d84840008182c45580903c025003052079482c5e80c100d40c1c00c10444220703001540580808151 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 494644316 1250 494643066 494643073
    0x106030f140f030a2a03090510051606020307020a0209090c01031a09070e12010e0307051005040507170c040e06070f05041503050402150f0d060b0301150e01110d02 72
    0x22918191101c2020304401c0c0890b50801000300080050100440e509003403030b0b107030201c6a880443c24405c02c82080400b04002181a0004030b010160404c5035581280d00844a40e065100002c00542c3d1610540c54140004004122030100041c07066000c0d68004055104482c1c0c40b0342c182c2d010562881c801d550941590b8040201403d1540c0d0500031540306403080940c50030b0419444c008100f07000d601a1002c800c1c0f104400c0390b1020368544d601c80c0464a0441d6000b030100781c10041842e52268003403102941e060040c0070f95802110705c11f025181c0200e9000c402001c50700e1a04240c5041c1e6901c500103640306000c1c85981c1240d40e40d940c05000c03401418032014001d0703070501c6d92016140c5609803280c1406d100c4148400c100500304a805a500007400c0c0c00c011a03a580d8a20002300c400b03010403103607402040c0209203000303034502e1030020b04900341c0d40c0b840402c21281c41c1c45d40454180001d00c00d4003035000c000600c140741039111f11003600148406043c40041c80c24032840c0c003810003c100c814200180d1 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 494645566 1250 494644316 494644343
    0x70311030909041a07020703020f040216120306090e0a0503120a140a061d0c09040c021504060e060a061a1803060103050102090414011203050a09080f101b1d12010603 73
    0x1940203201300e0b00700955000903c3c034146150f022820700103206540c0c502ca00c0d070200c0e100c40440c490049480f44998852340e611f02142c1a900084c004003000e00850007c0b514060020f603900f24001004030400b9089001541482c0b00c80c0d200c1130100300002c0180d180b40c0e80740d080d9030f040c0c0018103101502404441402188281c00c010310350307040540403107082c0c4000c03405805020084240c50210b602d441c80540d004214030302031000591030481da0462030307514104004200000d028255110400340079024040c1d40f00d036280c2c110010291000c6003c0c6407841e21100c404800e413004540024031a50300c822a401c0b19080781d0f000003909103c800d0b4400d841607500001c90403010f14040c400e00c116407014800f40701e41541000c810a00715480c654004060150001d40942024040c00564005054a10441e0202d400158645407204146030380020401c0c14100d503010700f08e081c484000d800072030b6561002e07201403512019aa02903400210690490080a41d40c8901603081c02010b01035405a0b41c0d125500 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 494646816 1250 494645566 494645603
    0x70215040b030a090b16140d02070b1003170a0807080a11070c0603050c0705030d09030318030201090c060903110f0f031b0f06030c04060e0613060216060306060507031103090904 78
    0xd03000240340e0741406c16055661456039810500c07000010a1250701d250b00c4405c000f0140c0300a1041c540041e0996851000700100d60048001e51019288540d488200d071510307801c80034441c0e00034409a1004162948001540a44548506948580d07091400705089029420350f200e0b543c440c0e417007500c810007c00010300c01650103001b566045074210403150300d000c029455140c2c0380d01515601a0300c441d2200486014144240c004408420722000054031545031407402070300901d0301500880c1d00b5584004001a964001c03000715084030b800c1030401c002e0002c14410064031040e54800c1540c0304130a1a1007c03d140c50401c10422244003207410030007040341c2d1500304000350302c2400702240308110030002c00150b014040182c40469045013092060003d4030320000e10740d4040c9444844014506120000b403181d40090884c1e600351100100c02c80d82c031344480703040742503c02501034540818030412940b0002886544200540182075003901d050580d010006600c2d00e078162000d80d010f101015841e00f06 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 494648066 1250 494646816 494646833
    0x1603080309011104120605100302150403060c08040201052a0618060108031e0d061806090b01030c0f0f02070b0a080117010603030906030924020a090812070215040b030a09 75
    0xa4030000350740f58200b0349459003140751180407004c010441c2e03888402107940701e69080b0a207005140d0040c204a18404026214032880d0014030080d00c51500300940c8040300c41c0503042843c01aa0180e403164a070080c0003048202d40c0f4900c1020b07146140030742491201c0440140300b003901030303422191f0106120342d0540e1554900782c01a00070b1010b03034100700501407a910500aa001180c8404d03080c26882d0f00007400400e00409465008400709070b80000c0c4511128000d5224406079001601c0c1040b10412560045003151024040407010500e0140d40400442c011400445420a00c2c0f040300c495607103d5800e245603800c82164940482c95410052000000c544c080e100000c0c2908000c200661850324000c0000c58940700d40014990390704213000030300000c5050107076007100c0552100c41c1148080d0401d0000c1d0700004280e000070700c1d00107003c5000c0c2408a02900800b0f44d41d10b03680c0c00c04403960200261501040c00e001c5042c1c10411000400d1622000030314400ca1070401c00041200e51b50070321401 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 494649316 1250 494648066 494648081
    0x10507121e0909140c03150307031401050a05541c300204080d17060f06041406091809210d0c030b030709020c01060e010501021c02160308030901 64
    0x2010039407441084240030178142560307400b40400003d02106a00700000c2410610650809401c401c201c0c00c1079481140150821405203c108004105950b00c102e4541b140d441c2c40f05421203280d40402d00b00c0c580904003100010712020f4003590049801028500c45c0d140d0120b00c035803240b144c01c00c0300c2c0504040c00c800e550303185209090400c00d40194240c8403c1c0c0004103840840b2580c014003001303401c4c81411590503900902130007800c2b00e900d0065070303501405880101001c40812207282e00082ca550500160842d501e150182c00d00c1d040c5801c10501c10071140701010343c10b0300058280000402c6680c0c052258004c1c1103c4240b0484505221004d00e081260718210401c000e45004014250007041e082169900395031800e0020b8501c5074003100301c001d41401000603070315204011011520749503540c028202802c182e80200215a92185100c4801609106107070160304590b00c1034503031103c04408038150382603502c182d9081c2d6020f202c50722484139a030340042d01e90100100401c80c6da940240308003407 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 494650566 1250 494649316 494649341
    0x10801020306090106211a041b05040b0d0b22050903070c0302011116090e0708060c072402070303020a180e16020102090306131b05010507121e0909 65
    0x10710354502030010070406481803040004011003504401c4034042c0d5528912031410178040140a0301da010a070b83c11a6403088035446224070701d07040c50b0226900999100d142c40c000c00d45c03501400c0901e40f03e22242190049403100f000c2c66215102246c2c0ca50300c046940b000e09001c03100c42d18030030b4110904401120310050404541e41d20400841c07000c129a80400d001300c81d824a401c107410003840b4052030401e5452040180ca20103441408038960255800c160311603100c040441c1c007003039030b00d6003003590b03510040d80c0c01e4483e80360410803500819405004541240841a94405280300d103042c650200d034400f8030190006036020408075040c6520541149444801070382d110f00b46410421a001401400307482d0050b0002c0142581080034005c0d01030741c80004004080d51182c1c0350036080e48250180714070040b1190301120714580303100111b01150300150740c4103035a183e0801690760307106808040c0d245500700510448007490448210301c504c1e000ca000440340d680345600342c50a4076103802d8808000b00603 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 494651816 1250 494650566 494650571
    0x5010e0c04120803091014070210090b0609060d0516230315070309020d110a06050331020405042a0503030d0914061f050906061219020c070e010801 65
    0xc21401c00c101840d007559541000c0f10030303541c1e02c4084101d45000540340d44019900e080801e9010190103000c02c03140b062070f0580079150400c01c803040c031004035901d000005044203054804035200f401d0210f01c00e544800c0141601040b40025215540f03031500c41c004c1c2000034000241c0c24040d002d4112070b41c41700780c408a036100c143d4101d540c0c0041e0b181c0e85c505481040c1040302c01e00245903640709800000301c454010304045002100303410448a00340f208050305005410014000503003601c41e1044038030031540309904000c182d82034070441c1103200c078400401c4400b20f48048100050f0b43c07148546c50103544580ca0901d00c41e038140095102c01d07020007180c0f07500704c0b00c810b000b00103984010007180c41c50708502a000401c000c041c940300151241d407010103103580c4142001c01808000400c0e03038032200c00415591403001503541080002c01001251180c0d040705040c480354000c3d072445281540c01403c0400b4142d1515541c850b040100d80060710031418a50200f1005c000e000020303070905004d00202c40c0203 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 494653066 1250 494651816 494651819
    0x120603030507021003060f060302030103020405090d200307120309060e01050915130b0f04051c2f0f151012021e0d03050c0c0f03070603020c01110a0305010e0c04 71
    0x70740680516040a40240b40c48100c4002e0b2038844c3d40000c000d04503003800304a0311500c0340340084c003c0d0000d0000b28010351030000401c100200026065488807050340e200803420410300b0807155020141021060b16100a2183c200028240e02d80040e540402e5074000400c0c446504140c2c00f61400ba036450768499241800b407095030740c40403408002804003403850080c0c5450701d0f2018081c048036010042c0102d88aa404d02c6850004d001c4810b00660040044405070400301690307113090340c0c1d000803500124180c1075581a4000d5507030080340141c1c0600b0402c0c0ca02c40b4800117a1400c0001d05c0414601d150415502c004440c2131909803941c02180f12250b044071141410b00244c090000d100e0b029204405034a00b4030904503046484101c440340c0035110822440c03480c50003421f030313800c020a540c44502501d20b0641c4241031100c40c4041585000300100101860725009400a6112341070403c0d1554880000a200003c0070000b00a040c1c038540d00069558940b469034541094007400b0f420140700d04210 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 494654316 1250 494653066 494653073
    0x90d030512160e0d200a050d05150108030415030f02090307080319020705100e0604080d03061401110a120c0506010f060f0f090b0d1d0c100c020d120c08030c0901120603 74
    0x2d1001200c1140201c5e125040d240700c0001e12145050392010707601400c5220908200b000205800c40200001683d04200740d882d00741164230380c0258080c00c101e1024031904198103070722039007040f180e40c020880014506107610004c681098200e4000000c103a01c005030700481089034004950004940344040c0110f11b080800050140500c80812010404c1c0165400d4a5940d840c003110300400d010350481306900524900a4003400d010710640f1004800003001504070350051800d00480d0705014094207415a255031030314140514100103108004122040382c1c0041c004024a40c0a0700301361880e004107514040e0300a10405180e1400010082c0064143c1075091b0801c169200b5546150416034031003950715070160040080703038140301c290b8543e0620340c106103070042001f03e201354003613484000f070f80c040d800140e03010180354500030742100800e202a0082240c1404403900c660003403400801c5410b054603406a550000d42d128502d054002481805540e00314518546080346110280852440d544 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 494655566 1250 494654316 494654333
    0xa030c0e042103050109140f1311040908031909030c0b04110607061e020a092303011b110c01050307050d11040801060608010b070503090d030512160e0d 67
    0x1080e0511000d404000c903003000540c10001c0324100c40c000c084030391840300d0600180070700000e2060859440c0350184010810880030f03e00c522030102d42040500c0e98a45a0006240700b4a2280a40301c04983c40781042442d5100d004103411103005442c01500ca0418a400d10071703612a400c0c3c4000441c1c504942040040c2d0003036020401035030000070810f00c1390fa850a018030111310034101e407a4460070000d0310300100803565000c802114a1103c890800200341003043c022440b44554020102c0e109860801400d100c20108130b61040007071400c100ca030b5043c1404a42507a4034072403011404080c0caa80308028a9211100da04030950308001000c08040703410000c0d089103c050306010400c9400250031410a1841e000246c141d03004545155a0f660380c3c14156009182c24014a00090032040000800c00840410703a0308064102000d50301d0801e07400208031607801c001404400703026050168044500500203107504c142d07007900962407204031080b00188030410031000c1d0b074420419030010340e02140482 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 494656816 1250 494655566 494655569
    0x18070e010507050a05010c0c0b150a0510110d09170703030c080c0c0a030b0a1410120213020c0703020f060a020d0f120f02191e08060105360a030c 64
    0x2800e01ca42d82e030115007401403c11442000180c515801d00692105156000c2941a0024060821001c1545446110f80c030000485d1600c0ea50248140341d0a004526003207510351000c0006040c60360308105000e140a01344103918880c90045803000504024a0403940d0f405030900d251100a071543c0c40c2141e5025000c001180c202800110020403002d2501038104000c4112940007400e1080c425920300d446441100c04a8083c030895041c010305002901c0d1400c02c1e00c0c0142407007110b61204505201083d2481c40139120184e90180d00c0d46964501000c0901c01486e01001c240b0240000e1405c2d8010700003040c1020711441e009201c1004022805e990120349280c1940c03462420400000c50700c103046501d02d01c0310081f0300d1030502d00401c0610020450340245802d1091140400c101000c01e6010b94511140c0f003c00b400d200801008840b8a500c103415546d0300032014100941010720700b0300e554940c01000d0801c620342e03403403c403040703284030220324200000d4010071101c210045041d60386482106095 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 494658066 1250 494656816 494656819
    0x7030b090412140405120109050c0a0b03011707120c061b080702130f150504060e161209080c010c080604021303030503060607082a010603120819050109060518070e 72
    0xa0f00031018101c10540e0443c0c0082000501c1000c1081e48130561038002e001c9400215010700c10b8480c13542807805d10012200440c3c8802c5006d5085038038000803101c0480b032064000d401c60140c0c4402298810901303c0074081070380a5040030441c40c3c10310902801d070300c201840c822190b0804100400024440f0740450790781d154103032856210414414141d4029290721180002e446061581c0d0315204504401c1100440d03008a805008095481021070f03031240040d01d80703e6112400340d60052006014603400c001c10380c0c00c2c03000040c030241161900d5400c0d411032000414035075102e900c48150b40c1e0380840444e402c8241203404514140d1141c0c200a40b001c028403004007401700200c0050701c240c0c1c075a000c1d200000e4010880c6542c400c2c00300c5070038100491380007011010004020100344410310500c074400a03070fa0b2142c560329200740d000d0740c103550109000380b0501c094000f40100d00340403a1a0301401d802807214445c04102c1e07600300340030400f40f0300d40166074031154102c42003000181680580c003118000c00 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 494659316 1250 494658066 494658077
    0x206150d05150c0c0c0906060304080304111005031e0709050d060605090c0309070b0c06131407030302030c0d1d0d0309080f06190912050a0c1a07030b090412 69
    0xc0e2a02506001524007103000c101a0a01041141d03d4800001d1102072500030580702c1080010040101103002071b1030303440d0071220500001d00014000c00046401c140030b0804040a42c65000004042c40300a60901002410100502030b5803014502003859582031000c510f04540790840000300703030a0aa202d0b02e4030402045a00b0010302003194014000342102402c00c60f6589055100d03900b442d80b081c1c440f603c4610403403030000307605900b0005840001c16203501610441d02d5829010301c190390700a03426222810003071306005d1078100030050800154425009140c481e6000c240250600802140300802d1003482813004406483c0d000828003103220403103540a842d441818119403406403034010340d003544030b00c40c0044041c0c4c0001601070710900c4014440d0504a034203100c48802c0c2d6a0080b0001c10280740854a10341ca039001388058003c01040d440c0002407034515489000b00101e165200b00d500003400c5040c07000743d66140c080c80302501029074110640d408d26070f6030b40040c0d040d0421941c08012 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 494660566 1250 494659316 494659339
    0x2a030203100503032a070e010308090117090d1b02012a0206070606030204230a1a13061a1c050603070905010605030f010801060b122205030a0807020615 67
    0x841c2500c04005000e0150840f5103518080ca56040c0c0110340c100c0e003000e00c407071000d10700c2107600c0d0019880060b6183c00352008800c2e4a140e64002d0b040c4c02404040d81800903c905003c142e500301c000c40743c8569a25001400c5060480c6005441c0c0300c507840945801822101c1001b000d03036005443d1607809003d4103c00482d0916141c2045030002ca0300308000d522000000b01c1c40240318043d0009800e490089504001e0b14110f0285c40c42c210f0b1003030001d1844c62154000080e05007629034084002c3c0d1000b14509990404c60b44001054100018002c440199544074244103030b608a2241c3d030804901c48081c5403074201d500e9038000902c0c2e0311045811440d0b40f0344000034025201405203d00a20340070354140142d503103442d00640300340c104035558104540031600006058805018010483e503040e00303090718001e02e8400c00701d00480020140407003650010707590445541d40c000e001800c1c0340618040c0d0389850144200805840c80a0f2400045521407001d1200180c00301a01c070390f5041c0d08845084104 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 494661816 1250 494660566 494660581
    0xf1b0c06160609290106020703030e01030c0c140d170903070f05030c030d1a0301200a03140c0715050915060102011b02100f0e06041707060603152a030203 68
    0x402480100a000c005810035100c81d014034162403500c3c07200e1320722040c49941c2c0c840f5004c0360380c2e00f5184000f0340040e504282ca0b100c0395000e40d000d10300080803403508451024041d21901c6400d4103080200b042c550101c049541034913484400039085980c0805401d800d410000213083d40ea004401c00500700348961462002045000c000f215000d80748182684d4440c02000c2e0103000500b00d00c0e0b01c0e0200d00b00420400300301407506100720005042d41580c0c1e5806d8806c1a28140c019030045031010091582e51020000c1802c0094815403151007607803201c595400440c501120303010071860040003403d042c4028481d0811022176024114290500c98448a903245c100403805081a00d4400086800d1020307071965182d400314509030070b81261b41d42445500d44400b045400c498281d285c0d0001508100c0c0480c0c00203143e22010b265214404030918104100c540300e00003158010307401166440101c3c4425803622001c2e0152142c0340b98442c08240080029041ca20350f00070381900d038102050750020000341c0c2d1 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 494663066 1250 494661816 494661821
    0x807080903150c031806090d03020c010204080a0503040302101403010621021201080f0a050309060304050c15070b0109021c0b1306120219060519030906020f1b0c061606 74
    0x4030540000680e040d080940002d51594002e1742c4055424500d603485400d0b0340341c00504a0f00609070316004002c0c03140c0c100c1040b0000e4010070900641e6540800c00021544c5040003001003481c0141d010b1980c840c69071040004c40782c0100105010300424a2400d40c0a4040b041a00e045601a06000401c40c4000e4014201400d0038043c1118040c800f0520013424a005001d49040c1c4240d4421903400010f80000c4a07030794241c1c007800070580d5208111405540c14050051608203124200710380811b03a520b800100402c109500000324180080f55600c240300d203d000140c010b2000c03d200f140707058061036002e00d0892004102c50181c980364070301039030103884c0c0301c00a2554805c440c80c2008016254040c0340c1c0440c010352401d900c00c0c558620b003d08082c0308400d07000b049401c281c85051800301c1e00c00c95100c040e213803451460103055681c0007400c04540d040c0001c1280d0760884810641e154803809440044070503a01d5280050fa10075401c80360203072141d004807807000d2070030030790120b0145080c03402602 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 494664316 1250 494663066 494663083
    0x20109030b0103120e0f03102408060a0b061e0901200a02090a06060c0b04030201020f12070f020109030509040e19080a0f030b0d060f0f090c05010311070807080903 72
    0x1d0348801c00000070301c048070b002c41e201c40c2c40550320722192481040800a00081c0d0025213a416041b0444041003000c1d60340c8501c0030704904000702030391b0300c103008024030f4041c2c0240d011841300e400c40001c01007041d50b60710850345826403c603600c60415103400341002c5030000742070801d4000e080c00180d40f842a0702409610900402c415254401207040c0150740c0d407a0504210100d0103a10b42002080c41d90b02240104000c0e14940c4d92000c0c50040d01b074955011101000c1d100303a066560801100d001801440d00416070b04006039508811070401c2030008018085402c0440216490f0080c0c9000280c0c3c424112080300f8000c031400314a1080d54034074a410007480303001700d100c4031502d00414020003802c500a0240f45040380c440700e501d03086082c1c0039400e9031207400d019944a01c01504000020700107510020005000b40c40020301c501540010340101c511582c01981d52810040c4200182d40c1d01d80600c00d0062125101d5909100c02070351004690b0060100080181c01d000c42d407125941c40400440d013 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 494665566 1250 494664316 494664323
    0x180307170904180f03081f030501090c0e041104020c010b0306010e070306050a0e0a0f0b101e020106080316020d081804110a1d120312190507170402010903 68
    0x20304590505441409650041c14000d0140781841c2081c0c00c9450300082c2d42401c00d82004110140142a680c110368001d00145a04441584255115410b04924411801841c414000014941c9860601d07140484003903010100c901c201504100c0000c213461000e641c4160156005600d40d40c1c010301040c090000e2200194141c03007402d0001500e0440c04845501070f01e19500c1c100000f80e1510f051201d190918000d100020170008040303501d51000d903104034140c110403e0300103001d5407100002800c8445803074a080c002001c440801c0380e4402095450000c1c400240020840c05141189054036401941c1900c55140c454000410664a0301c141d603c00f032541c80003900d0f0f6124411100110301d08019400310740100d1402c207055a25011600c2100e0100d1190784445d005e104a00c0300d0741c20300135259800300ba00003190510011218000704040c0c014012503c0c6016803515041d00f00e40a0442070310f202020301c034181400e0000c00d5030080303516204100c645140d0842d41e940c40c001681c036150350382e0006 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 494666816 1250 494665566 494665583
    0x61b0c040c1d01031503080a090f0806040302060703060503250806090307110f0a050402090409050f032203080403020d1b060509090603010b0f06070c0b031611060906180307 76
    0x311903440d40010680741e0009503031404102e040406004500300c40c0f40131041d44043c01d644009001144402000d81030300a5280f074400174840d2160028101603c10340c4c80995560b10070000c0c402010307018401f503684152345107002c0003214607000011707940b42c441c2258102e21070020b9a9000030a03101201c2c410151410200310380490403c0c5260030369aa01c00f0006880d80d6602034114202440d00d802c0030420014004e201c420b00b03501300b0f41080020340c040c4540395803255032800c01900284050100c4208414010081c2d030300c84041c1c804501c41c68801c000c5e4802003078081001440060a9141034905030f1f0340558404501003014902244040e501101c114103044c3c0010000034402d9028004040b210000da4414899403a040c050500b81c0e0382c449903051740a4142040817406062080c0503060031030180400b01030b000ea0711040f6400300d81c010b072040c3c10032940e103441030410581c00030f003070402d8044460300510052804094180d2241c00103004259809850b84003400086030401c03d5540544e003112a0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 494668066 1250 494666816 494666831
    0x140c0d0b04090b070915140406030b0112050703020307031404020604060f1205090d1d03210d02070b06040b060412030e0d150603120203040b04030609081b0705010201050c0702061b0c04 81
    0x1303001700c69203111311100301010000080317100303228000501c80d40e084a0701d00c5081c00d00b0148154050010b00f461181040918101c2e81c1d1540341c680a40c0340102002e8600603900e007402d250080565001c41031b402e886d00e554105000051710341600b19801c03a802c62600d094406411b000840d64601520f910300349241c01d2000340001c011000c6044030000310b03241c0700c00801c0000d40da201029016540701483d415000104c03a69096462060764845081110550714503099084008800b01d030020b0300282c510718608030401c141c46c1002d120700012120200c80b200d040c04d20f0018003611000024000804000b11910610301d607449a00200464070342c404030444e0207175100d4072144010286444180d0703606000f01c8020344028008822602542e580381d65291516080d500d402d00500104002192000720822080e00c1030004030551406542c1c3c101d0150a9052400000a00b940c90180000c0b0b000c0008010300c00059036594115400c0c030302c90b1b4004140701c401281345282018400e803140d58101d800c00d800c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 494669316 1250 494668066 494668081
    0x1803030a05072607122306120609030703030e030d020d0902040609050c0a0c0510050108100c022a13020d14090f12030c0702100c0303140c0d0b04090b 66
    0x82e10034070965941c4110072981a0320742000e40780d070000241002000c400800c01d0300344035a140c50000b80c040f04000c0307050f0300d03e8213503401a40032016188081075818018170072240340500d40081d048494a008008900300500c00540707900c80c1d841c00406065860a00100c450310920580c0c0350561802c20454903040c0b825007107000790080c11002c9200e146410404101f1021034030800e0301807080b2091f00f90410030810802c2c4e0314612610010307203561003007101d181c0e20414a8001d16000c0c022006c0a010f00c103500c4c4264074144d482621141003550491204010894030454111042d541d1400c050032449182c0c40c0442d440701041a90880d9042c0001003005d2881c00c0786d0028043e601d01d000c6140b01640d901589541c80e00240303d4005141d07007180101500f164101d20195800c44d6071044068a0800390b9070004201d05440b0b032a400110720610844002d044d054865411103101d091741c46042840e22503602041442000740348010150340740e0b418103268030340b41d211248103540039210507041e00701500c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 494670566 1250 494669316 494669321
    0x207082b06030c0914070e01122c072702090d2f0108010b030c09190f0311010e010e011805060f042c071d101809020f0904051803030a 59
    0x9400f203007504100900310304100001c106482003c00d0342d42c071003401f90b142c0c00440c3c411000f50350340c0d2209178482d1301960803240f0300d141221144020071f035442041c030340d405c8889044c104103504c801c012402200700314800d12007030300b8646540c0140319030069480603c400011040404804054000c00c0c0c0d00780c032103070303e810303500603070103000b4103403000089003005110044403541001d009048890340103101007035610072407501a2141030b10051501c21034090801c10101071450075407001c600c035400010b04009000825904c85444042031801c04042c034070000c000385c06501c81e248141c1c104409a00c686c04d16407007846400380138010007032031980e0b03510054100780000e4015015603401c0e980c40d0600c60001c031440101d110422030400e18980e0030340c1ea40c0341058404a0680410b45039442d100a20604035644500c200b20002003551198124580501d41ca0300c00e018803070300092146407042280713902006421060341c2e03140c10304460100e825942c9034070b40d00c0e20701071203c07148640b4480030091114400b8240c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 494671816 1250 494670566 494670569
    0x613081f0b06040f091107080304050c0915010215040309050a090204090b01080402150702011707120606022109030a020d150b0405010302090a0c020c1905030705040207082b06030c 79
    0x805220080c0a201001020f00c100c0c0710300021480030003000c21025010390092911024065051400d00c8010b445158103a403084400719800d800c404000c035494034208109507000804da004c00304669080ca00041d60304d044001c1d049500c1c24070100005c0425118a0039400901806440e8040c0165610041d130060341081c042c5038046401e0800344038840d4410140b0038800d640040034840c0e00c40c0450640701e80c03580454010780c104002080107008510501d51242d000c0d11086d41d4070108002229000c10031280c2e00e4001004641190303850241e2400c1003409100884010400643d03981030500010345030151502c8001c0d00700c1e11405141050001c03030b510301c0720004101c8000b446000d002d03604001c1141c0c02404020761015900002c83c0c42c2005503405400001540d00482c1c0342c00c4440301c0001d088400b0903009490000791000c06016908060046600078907058400354100182035880318214000c4824600d0120301e10030b038900c00c024000c1e1104102001c1c1d481e0402481d9100d04000280f044207 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 494673066 1250 494671816 494671873
    0xc120a060e062e050603010608090d0c053304030206010f06030605010203180d0c09270c05010c17040f09062102010818010f02090f1c02061308 63
    0x2808180c003444400031842c64030032034110f001c98510540d10f40e64028640c0e10880c55072070f200c00c550404690303900c0d00f4009601070445902ea11100340b500b1150185410100c10145003000110190003001550014520b15403441064802401030f0012606450390002202010b000400c88001c1c00113164010480c14180ca0481d132942060075154170065054851512465006a00c1042400845040911880703030303d000050900400500c50f0b2904200700c445034108415141c0e0707030705000100b449c5101c00003046031081e488c5c5131090351258a640c0303000d0310644140303418842e40205880800142101080701c103840c070340c800c1d900c881d100c0c10f9150351410356001e60b0062900e80140490313a40b26a101e04142d140340300e203043d03800d100c1640c011513030510701921015030b503480e00c084082004c400303000c2c2644039403440d000103845074003520411964140c10040c0c180034011a07204144071141190241d080e00b901a91329540d643c00032003045c0880c0800e83e028803041e000b089009060008800115042c8024 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 494674316 1250 494673066 494673071
    0x603060402071a0f060d0c05061b060a0e0f0a08091215090a0309050a0305030d0f060f1e0e0402030616140a0e1f0509010813120503010f090b0a060507050c120a06 71
    0x2c07000107001b0240c200d050064401e010101c02040607140000041040c90340c00da1502001249060340d0303919046054a841c0341031034030754027541d0414204210400d8050403040003880d040116403500c85d024480c0c0c0b1102c5000e07400a56280304558001c01c02c4560b000b00310141c0810514001c3e03001c40d00c0750010f65017100054807000c0001014949103d0314000d03241c002014620b040001e42c0d00b08006c2002d83c45101d070f0152075100014030740040e0020000144105100748a00028149041c40140c0ca40d400411080c1c5804c1c081c0005070710300045050344080060240011000f600b103040c1c1d103801038030030f50900d1094001600c1e85841da0080000d03091200c00c0c5c926036a0200c04400344080701e141c80c001c2c000058418880a4441d42c404d040407030b0003e58501400c100c900c1180c0301c121501380d445202c4408a400007004012050034044c0501c003c1801c11400c2110480d9000000c1e0303400890305c908001c220001c0741c0001030142c00d22001051b42e800400c1c1c3c480f41000c018200703841c0c9186480c01d990031031 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 494675566 1250 494674316 494674321
    0x120c1505030c1b0a0c0b0a02250e04240b0f0108070f030b0a1a030f0a02040f23120705040e300705030f03181b0603060402071a0f 57
    0x340200180c0740106140c07200b85061002c00c203040031001c8003612460030710703101d558210400300382c100c105032014020100840d5503900400d280a480d0000507003074100c03c44004003940071700c81c2480c445101a940c11401c64032440c0c85e6410030003404a07542c05e0420207000380d010a030f12130001d964032a04010000740d408400f510f41940042d200b00318125041ca0101312480d0060900368807a901000c840800104001100da44a220844072143c02d1048504614000403e2081c000c1004414950080c0c400c00c040d0314090500e4580c4100c18144e201c0c6203004003201c40d444500c1c0070b01e45a1125a81405011051500300d80d0900958444040c030940740902e10380f503000541a01e012803010806500d40842d01400c8a6094040c503114841035050781c10000140480300000e4005c1c00140070101e19036805a449003000040c01200c0c0c0700c860001800b540c40708041100c60000c0002e07250004004440d4691030b9511b100105029105006004060480c1c04041401c211100301c0d00d58080c800482c0b6500855 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 494676816 1250 494675566 494675609
    0x30c04050718080d320a021005090606090610021506010c02120a110f06030c07030c050f07061701060e040b010201021e0d0b030601320405090f1b0a0302011404120c 72
    0x1c00c5c1c0750340003620003000b400f0403a4501e1000c5d80104498142c03841161420045514210121002510b10381c03240c0d08440207000043c43c10b5001240c01070800c888602c0080e5260f90060368030b17025512168120064a070000c1c0d2036a004000c802d00d00e0f500502411400325101041d01d40340c07240e0720f0b82101d61100d800480d400301d00301000f00311985100506030518644442e07512040ca0b41000300c00314100a000400d020019100b070201f95840d000810050003042d01740f1002411481000c00155882004031004200560380480480d580c10410340d03001a4181407200101e01a2180307004194144441d00b420381c009042e440d00a001c3c880d1182c07820056810010201a101c080030301c80e002c220314034452100b0348458400c450400a00c0c1818400003004603060210f02900c0f801c4030000c0c80d603041120041911001407104515821074141060010f480e060001050361150b80006810003c0c04e600710070003490a00100d902a00c690304640f80c038950680384c0401c60700c116014000a8400030060013990 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 494678066 1250 494676816 494676857
    0x31101050f060609040209062119110403060510030b09031b070f03032106030c1404060f150203040305060c0316031802010809390a05030c04050718080d 67
    0x38000040c0310070302c0e00144c101080040d400c0001030b141d20500c02c0000c0b0b65258007100c0c0450022941c1c0099104900d441080d4114105034884801002400e201e01d5402c00301d0f12204503000d407540820f000603951a000d484070304180c0b0a800007000c280204d428400c200328000054108408e94095414420764018505600d03420a841101603003401c1041c00d000003402079003456180c8440d02104007a034000303044010282c40c3c0c00d6109650260103420244040b4180d0a03100c2401501560180a02490204081444045c5100b501c44a14411403c41c48061080c002c0710300858104044403041e09140d41c510340d25500c00c1e0360034010b020740c449014862502902500c201c1c2c2c10a40310101c0d800d4510b0300191a62000181191114022045c0c4281104540d03c0c504904041d001072a585420000107007424101805410500c1440012401c203e281c0e00020030712503400080e40c000c41e040d114030b903082d5032400007440c0b021607140f0043c3c00030658507800241107110540035078804a654030800ca2419a = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 494679316 1250 494678066 494678071
    0x7050102030c0a030e01050d09030c030e01030b0306150102030906030907140a0b0d0f02040e0406050403030605040e03030a0213030218040221031b0705030109060207050c1f0309031803031101050f 86
    0x225074120400103c0428011810000c1020040c14107074034041c0b06850100c101d44a0302e1013140800d500100002c141039220a0f000d980540130f08041140340300c0040000c0e901c00300104150b0242d5040308007900580d01c00d00a4503208880504560b84034100034801c00c3e00d80c8454090705121245414041e809890000c029408803980c1c0c521680c41d1035814440940544014144180840d03020000001d081c03071041e0b600761007603029035800101400e1600d0b0080035a8001d50010b4410f90401c0d610400c6004040102c80e0003801c0c80800581c0c40480c1c1d00042c03102006540083d5000850314004540500b4200170706108510883d180f03082013050500c110a0b0103403014201c00385030b00a005031020300d900000d10400e00310490b0125012665540c0020b82900d001c07040445505401050a004001d42000081415141200c0c036800c1d0029400e54654040d5050780603004154a880d004418140501540108407038009801d1410685a04020f0a000004600b256440d86840001000120035561a50 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 494680566 1250 494679316 494679337
    0x203091227060912012f04060c060b04020a0c121b080702010908120903010b0604060206060d06200909061807030e010e011a01140a0e040c0302190306080705010203 72
    0x2075070704a803611840180040d801160001801c010340c2c01103035900f003111041600840000300d280e00507506002e80c4406140d9000b08010401008009103400e110241c4090311704514200083c04118140365002e8480601c0b243c0d002840001c02036080340e481420b40d500740780100840c0b448001e0a1008444040d500140708245401010700c1c0e80c0000d8140f401000741078014903203580b000d610382d261941080800222500d0f800000076541445007400c1c0180d00001400b12402424186002806505c42500918580c81507a40c00c039504104004d540c000c00310a00c020350910070781016060946500e40c000e0211510494000000601c41d14104510340c00318000c0d4005201c17103442e00e200c02d5014154210a80302503548400c0f841400020901c58402e02c901c80c06541e41401d2162400540043c3c02003500507007800040044085a580183d90718140c0f6405890016084a090900f180240030340030303250001580d00303075500415a500d0742209082d00c1480d41915981a5144016603807442260182e0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 494681816 1250 494680566 494680597
    0x171207050604060e03070605010807050f0904080306010309150f150e0907030b2a0a030c021207030c02061c05060405130f0b1f0807060206010f030f240603050102030912 74
    0x40000d10f041c1c11410002d515074003181d00f07141d01980c4031001d848090304540160703400480c042140b40341040c460341d00c1200a40b16520176040c19140c01440f4400280300c14141502c40341c0d0001006004c014203100054400420800c0202d0b0f8950003010b0200041311142030b000c2c1440206900414120a41c004d601100003899500d18581c1d83d0108050000c02607140c9107050400490301015a0078a1102060880d5243d40e842100c240c0103000c0b90300c3c621101085601210889103100d24810072908440c0d054100310507071202c0b81c4000380c01d900c40c5119000c0680d1188045d900060381d242c100c0780c001c41086800384103071756036908208120fa2181c0c001910314072903171100340c0c04038a01381c200680080c070310308410b110000301d4414a01c6100c00f6612000c401e500905082101f1681401214050030340301c0fa02c20700c00c0703140d51509a1500011000589480c4d041c81041900d4501103004a580140c98142401210340e603080081c001d400031030301d01d0100d00521004150b03442c4000220754042444200e207 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 494683066 1250 494681816 494681821
    0x906140a030b0f03030409051e0403020604030c020a0b0a02160e060307050f12010501080f0d08072114102103171e161d011d03030906041712070506 65
    0x4801815801c02900e8104403c0051000079480c1400280050500d03903c0100b0740c1e042101c0c2c1304541000c04d503200c44607041c110051200003079021a0b403a0b0070a070549003c00220000e8000140481544d520000d4503840020b031000580d42c001c034150303030032105c500441e480a030350300c007100c021800f01100e6590b03040e042114203201a260074041c0c1441e00f03902502701b02800041100072030031514281c01900c4164480e64400c14071310070410040c0d40100582c03074040a00d040c00d0b0b8025001c200c070015201030305000041d000700b10445950011040d00311081954111307051440c5a040d1808807030184014040030311892035010758141d800000f450340c1c180d488603544280c0440c41d040103c00038000440c0d890f04140a2004001d44800d02406443e0707401404503403c0841c88090000d00038841116000d1548660451036a038102c07450052440c90081d45120f5801c000d0000b0b41103100b40780e0b0041e480315000c03502003080e0500320650704810b40a0011240494514100c0a40c01e01807000c009003241d029000 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 494684316 1250 494683066 494683087
    0x13030213060b0f0f040e072a0b040605070c050706090906170721081c0c030b01020c13091e060b1207120305092206051c11031203040605010501090614 66
    0x284a0800140100b5045c6511005105c80d40d0380291031460000304c0c4040d01940c000359040700340305011701508103100102610350b03841d0750075034008001404499548d000110041c3c09240c0d0a003800340c0c040117840f5040c0d11540007401c2d412441c000c29801d14a416004604003440f00781804e80841c080005180b00d40c40c10707120201e00000080f9070740c103642c001e003c80c00002c3c8001c00a000d02c01c2080c500840e281c2c168021740c0f001c42d600080b10350101030900d122409240d8000c05c81030180081a200c10650812000301c0501400ba11200100188100210a02c2d00c1c41480c0c080c8010030303c141c6c030034480d004d18803081102e200e500121100894003c182c007007042100b031200660308681b190808038181002e500008031700d92038542d504880000541c0000702c4c0aea80912401002c3c002c2102c220300482c6403c1c840100a4111100c000d00120700e100386080b656604003c4e100040583c0c13440c01e0b5503480d06140c802c000c0c003828840d01d404146005070100365540114890a410b0240f403032454184102c560 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 494685566 1250 494684316 494684347
    0xe180c030d0c12021c05070215040521010e0f060406060801090b07080405070506040b0a020609071208181011060c0a0507150f0e0f100b0d0b091213030213060b 70
    0x5090720250b1285c0c2020b04071441240c0c4250000c84016218591160368034018080074000c5946804040d040c10002441346548000c1105004e0154109074044140d1060342035004116843c48041c09100d075000030000d0000000307080c1e00c5540715042c14010950b9807001c15080c2d5010b85801030400c0710200004207424403403c0c00039805801442204c1c141603481c0d0215410f603000381c1100300c28000001d0b4904440f501000340507080329001d4014650140350441001d500c408844005100032130025241c050351407440204140080c00815092801c0c0d0119805007030f00305207031070b610307214010340000480c1c10381e1200c166140c4e4801c64481790b1415079103a6404a03241d028030b0003070b084541e4918242e00c040003d4822003681d120603000034500380c54000200c03450300e012040724070b0406050070420181c988942602e04c0c5e240e03a100312484c0042e140c0b092124142907480c000035a4828011908014208103881024200d07130003500d031068200c180d01520341c1914414020031088600800c0980c21400015 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 494686816 1250 494685566 494685593
    0x1803050a050703020102250210140f0d020d0212010e09030909060d1a04050f0106140f09070516050109030f0203030708041101110a0b0108060c130e04020a0e180c030d0c 74
    0x13440018540b1000c540b504203841d00e420110358001518508443c2181060b80d0702c80c19402d214200b42c1c40e21303100c0801001c20b9100300481001c4000c0c01041c1d403200184079805441400210440a54561130655100c8091020911407034281e12810388c00300d092180084200d03102440003078050542a0f5a01040c40f644122030103044401020729400a10b032560701c0000315020b144150050508044051505429510f190b0048507081031040c90b02e0105a85d00e802c03c1e200030710162100c00190340d494000303643c5805a4032030003601c0c080b03054107001000010350004107001e10075103445644aa144034101c1c3c0c0c90204840603400f00d581c94011601143c80d0032840281058140751800c1404042c8100d181007451003003040b1210008180180704000302448440d601490148000381440101c0b04120b00c5c00041d44500d0361000c0020000c0360a5456510805002d024003900701807030390510f24a400050380103034464038618001c0e1681010507140104100d0031800301036448003013020541d1120396124a14 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 494688066 1250 494686816 494686823
    0xd06090c02011104081213170109050c1504030b0421170106080f13080c0a080301051005070305040e060418110102102f161b06081905151c02041803050a0507 69
    0x1901d5000915403231203141025900c2a0301c001250001852030041e1801710080c209501c1307030020094207280c10100c24240d908603500901002e1103503d990501544076060040000010701130f01099920b160782048800142080c2000c1e21549a0380c1d503801150a500140d6481208041c502e020801c1d107a18450301040e1507000707110062602c141d0440c803034508241124100c4e11031030084010041860644068503000405050151902a0503580100341c4e220b1707400307401691180300001c64034a8a40b54001400c01503444004400c0c0300590418080030350158040300c1c0107228460044a0f42c042a0162030105086080516480d20148004412401c2035a4080c0c00d2031000b40f144140c0c03001240c0881140d540036111107013405400c1040440741c166590803400c14040b5410511041107220000b1034054401c6500c0091551140110340700e00c10004400c042d0b112601c111005019030500c4101002d0f617208030340420032078044d81410340014001103409001315006015010380640240e0003040c40303900c0f = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 494689316 1250 494688066 494688097
    0x612050708061908061513050405032d031008010b010c11010509040b060d05011d04030c0b070e030d051903090804061808060a06030611070b1b0d06090c020111040812 73
    0x104c950b022032405104880e0382c03c002e000c820903640305040400904c610ba511400702071219192945034595a1b20070b0740114410200f181103100c148111440b41a500400f41c154010398070304240b10702c00e408987c9405072142035442d0045071200c56000741d0b1084461a404603040300b0742881c100040d01c5503000320500c0783c3c001c4c3d21811aa00c0f540e40b25001030100b903070000c03000507803541000954a094003807009600340741c501003002c2c0300c007003600000d170546800c3c0d00c6a0703104003035624070004032101075602e010785c1c0c0c151103000240c1c000d01307800101400841e0b214800b51028001c411400700c4c01d4401042c0c2c0541160b00800c03003400030714800d4100b031340c181b41051074904003650390b55165031400b1400c031050607443e5626a0144104086400348000c00b103581b00320582485c1d03e9803241e10301c2e070380c0240c0065180030102050070148210348080c0e81102d151101c04000284d80c1d848080068079004400b50015440c01d910780f40700c1000d000503241a030707042200030543d41c141c805086042d54007100749007503101c4 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 494690566 1250 494689316 494689319
    0x2150c031905010f0305060924060d2f0303040303050f0a02012003040b060a1805150d060917130902030405010906020403061a0a060c2a0f06120507080619 68
    0xc0350150ba8002c0004606118885180d414a03508141e0041d107201c031030f0b4000e22102c5030b81c0b20000d1440c40c501d040008001c82c0d01e44901c00014901440907400800b0741d03540e82c2100d070005903079400c0860070309162100d41c89400b40700f0b010951684500d010080100c0c4c0203114149007964494050410001680000119144000707400d0403080307055202003c4800000007044100519001500d0300124152070107070300346042220010b107441c000b50084c0c1c0090750f284000f5500c2174006440955640010b400c02c000c0b00c0c4a800d120018004001050750348019049200182030701d5a81100c0b4950045180024441e08180c980c802a60018205139229900d5150303540101d94140f0003000254881d40740010459420b540000c0000c00c0300d01c03080c1c0318182c6914100003580d08450b02070b4280d680440584000c86c9000f20f5005081241c591320341e90200c14020204900c01030101440a8030304a440d007601007140c440071002030710f90484002001a40a901240007420328070640c1c0e0440d900d14610180c640e = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 494691816 1250 494690566 494690611
    0x60d0902042003070909091101050a1215030c05030f060612101505100306080d0e0a03081801180f060f020a050d030b010908120f1c0203010801021902150c03 69
    0x15524502e5040340c54001080c08042030304445400700500350824144010b0000e912050641410180e440b81032000004085034502d1155114005203600c240041014800c5070f481e50680494a010071070340101c1d2007101050915000560460b00441807008244640c0c80d0010700c0040001640b02c44094401c0044c07581041050740210041150380401560140b0f25010030040d101198035100800d02d880c108050101440104901450500c103003441d41400442c940460580c0109900c041c103180340c0419030418403104034a807050b10b0482684c0310568402342010064407000a4803c0c100140e402e02c40070032849000311160749607805640141d94450005440d42e909001860020400007a51840e458400f582c00201c0d00c400b4215600050101032180700c620051031043c99100c8160a03400304440094156824070b01c680150702410940d22541d440442602175040246c050b5039481e050300d480b0300c0061001030000751103103122042c07200d0364076a0169070b03040d90300150070394007030311101500700084 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 494693066 1250 494691816 494691851
    0x100f3207032a0605060d030804060209060d020d021908090d081503060a050f01080d02070b030a1503030f350403030f0603151104120611090d03030509011505060d090204 74
    0x4441c04010307500d42c00d030781841c180342102c0e0000c0460307106400e242c00440100f584440060781c0151f000c1c0c0c00503a162150400030320640a8440c80c10070250002840e000900c0c61398000e400002030b4848a02e80c0308400610039100000c2c03c907405c07080d580c441a4900320f00340c400c0b08140d13040750407030001901c8218003801081c00d0001c11030f03103d6049a210030901c40d22003004808540180b541c0405081c20f01e41040000703443c1c0d18944038021700d0400120100b010308000d0350069500031044100c502a0701d59a10f4003510540182038400c0202d0800039101004407845d01d2003e41d205d00c0301414050166610700015486500640300f581010369580e480504003900d0310490340a140030b000220901a40341518109542200d60654003404091104004072000d0894641059034054001b0400b0100d817941e100c402d02402050907441031040070741500b0305805510850049503264000d0007010b0840014100c0c00041d441180c0d0005410060b1041011a0368400b4000700e02c028000b10b1802010f0070700108 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 494694316 1250 494693066 494693117
    0x5120601053702010b010509011110140702010b0301110d091103011503020f0301020a0801063006090e010b03100e03120424051005040e0c100f320703 66
    0xc08050502d41c08100240060001c09003100520080c000d0200b1000001c2250144100850600840391014400060305010b40c0d0315151003c0020003008441d45e4100c00005000e850000255203041c0d051303c0c03241018000c0c0600705409031007040c50301c070700c040300c0400520384032034251081000c45881c80c21a5800f8068214030340180340300c6164250441c0100261494001d650500c41c2e0710402c07080c503c2030b801901060445440d814500c0081b99a0000d5200303c070900d4400c40250f10030054042c1f020012035220710152a440c1e4000c02a0410f02c20070315082f200048800341c1d05601c01c03002c544500c106500000001784400065030309288030080305011014054500721a10440da000b2044450201c090200e00000103880600681c00c00b51170740d4880c02550b02555002e140c480b45030039004801040302410404024060801c5800b41e00402172021890f090340740c001401d00c204c07007210308006a00c0e6101c2c1d800954126603a001c041c1360044100c0c1e101c800110248052400b0441380d04480501d500e0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 494695566 1250 494694316 494694367
    0x50a1e05040504150f050607080f04060201140606121801020706140f16120207020105070f0c030512130b070201140a050301051c0b060f150c011409030403030512060105 74
    0x540712401d01081009072544021200d4590780e0a16040050038004c02812003203401c203440040d5121200d003841c444a102d00f4490864003040050000391440d13055010801b0300c18001c000009a440740c0b02001681d10030f61000c44081c81400004c80c046010005e01c1281e2405c44000051030009180c1e10001900e50441a09140c0003559007000f03800a4000e034482e901803640d030050b0307040e65018036001c5d250401d1008041e40b42c59010070b01a0859000703808440340c2c40d40192010b9401d21481c600700001e042280812920f600496582d481410700510540305400740c07041c0480c01c1d076414940440c00d02d8101000c16030420200201c460070540000004043c0004503a4030b807552076045c5010303c4a04c0c01290400c0300010218080c0401040e0704190309500300404507910318941d11100c00150044e102120394143d24074000654010b0520f0540c0701003000c080c1c0280405095035410100c030303141c1c01103210140206074200080c0f68101c81c10186190b11079414107109041c43c02000d21003648903d8000500c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 494696816 1250 494695566 494695577
    0x201030527160803040b030403050f0921101a010810030b011502160b12060433170604021003110d1e15090b010e040e0303010e010e0403080106050a1e 66
    0x140a802d00b064200c0094141240290b140c1440c1c11000d0009210040c4040d04100d40031891041c12050720085610412000707180e0b40c0100316043c4068810020003021030002e1080710344003c20b1020324000c2581a910071410214280031110041d600d071078000302242c406c80c0a201d80400019421000c85000c2c2c070400201c0700c0e81103282c0d44041d14100540246001e80c00318050100301c041481e80845452050000f0000300603203031103010030080c000c190fa01c0e16103c80050f40c0f80601c41c0c124000882800b025585c2d0118681d0345540e0303a00c0d80031501c4505510368103d0302c00074003d42800700b40105081110700d07000449141ea55031540b000d4000c0c0f400c444040b41c540c001da1011858040b40c041c402c0000c0a01081225801c0d41c54107800d420034850391206d0390701c070040c40240da0701a02c0c4116074554003610902070007150800158a944c002d0150440c0240e0020020844c10504458a8403499054075a040140d003070540c05d41320781d0800031a603810800710340200118041020a807040310b40b800c1d01d88 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 494698066 1250 494696816 494696833
    0x14061c0b07030b030f03281e02061b0f0d05100e0c07030908150402040b060706360807080d060b13060206010618030210090302090f0402012006040201030527 69
    0x1050300300724481c0c0b04803840d1b9006002520342c1a03005030aa08819550b42c1d1980141d0b0100c48066440d0b10001c4803001496107950340b4800301a4010a0103880760f9102d800c0860785803c00c00c4043c181e270080c003e140401c540d003881201e6504800354400c80c1c00845410a4180482e17460307190448040381110030105001c40801e0781410180c200b8828800390100c02e000c4c000d200721495041e2000340700104080d11640d16000911081c2e2509011500036030b030031207401e00a51561400d0000850302c5d081c108410010b202070030403a50701130402040051680101054500b10260715007580f640c1095400280099603000005034202c2d03154020242290034044040296280180107814244142e000005014103c0350826060401410301030549070f0465207100340c0d52000100b00c071211055040290003000c2d075401d0041841152558500c118400d9950707442c4410612184420640d41c03150084996000e4008100198007980065a0001000b80c640c440b510703458810128210f52814070400b11b070400404d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 494699316 1250 494698066 494698069
    0xc030406020102090316080a030f09181a060705070306110f0d0e101b051e030702071403190605070e060f0702031209010206070815040f050f070314061c0b07030b 71
    0x80410480c04406d40d182800f031800304060780700c150203131000b81004035680c0c041e04814096034184000e4405004000e603c40c03061070300b0305c1c01044204102d031110003064030a0445461f02c082141c2c51107078094060921185503959407005428040c0c0e64407031801c000d104c221000200c000141801c0d001c0a04007142c000d0100140c1802d00102c685203501140c2807004500c0049500481e0510034061841c24517918031003040852070801e8003d01e8008140c1d00081030200c059400643c8509807900320a6485000012404059503011005072101d420818010907001080059000030392045007814500358218070440004c0b8150302407030100c1a0a10041074202c00e500b030400400030440540030070135141030802c40010399200d02c014203034000c200b51200016400d18039541c61002c0039001400030300001010300c080070040c000482c1c0002540d030004001541c210302c071b17008040e009000d030b0007110312075142c900a00c1880001c030304d04078040b0100d442c810030000300d010540310320800407694000342c0410341030b0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 494700566 1250 494699316 494699323
    0x15090a05030307031a04060b09010e040f0509070e091f021b06010611120c1c1806030504110301020a0e04021e0c0601031a041a042108010e0c12010308030c0c0304060201020903 77
    0x1760101d0045140c0807043c0807a00a0100b250801402400d281c41a04040c2d000900940942c0018000582c20203045c001c60100001d4400d0503030340c0b16240d44030a9540ca0502039a5400343c14001c80108075082028040401c0c1540100718084030b1201d03030502b40c5940207900f0b15010080e849503000501d00082000d4159041c4441e02c0000407910b04285004100c0c103540360740e044d120328010250724110b00300c60310450140c41203100c0b09a00c100c04c280c9441d60363b00050010801250103481803640814044868501842160b4220013143c640d4030380c02898000707210094000d601c4690f000c010181c1c180452084036400b41c11140c08000040140d5811458201714001d80c40d1940201d0342c40c0c5c6401d105c000354500050b034110f4410881000900e9450342003029808007030038159100c00d5000d5040f1035500c2da1014500e41a5250321134180708a03110032684401034810844928011007000005000182c145002075410045043e00c0302e042801882c405801c0d94030030390080c800750b0750024803030519003401d1 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 494701816 1250 494700566 494700611
    0x50114040e090c010f030c0905090901060f1d06123004081f0203040803011e150e0a081c142104060b011d012313061803030215090a0503030703 63
    0x80c86c082c00503050408010b0101081405054401c01045000548001013507105400404490284d5038006548801c190400d019080310411443d080c140001d8607401c2c00481e5075000c000180040c01c1030040080141e1051070044842201d44483c13030316981c0d04803201405400604400d81c0548850a0800d00c2c425040c0c0b40e462052442900510030040400c03650001ea0741111507000040c00700c0071100b41000301d800768942101c480c002c4070034512100e1660000003035062030b40550f52029001d0301c0d0751101c0e07511110034103e48040d004490444842134890741d0701d000c1400f065a001810000403041d2042809141f15200d035420310f10342c0400c001c0c080c0e1405000c104510a08000c8001e82d40c6030812908200c213101c941c1d06100000c0c40201880201065150b65003004003200c1d500d413a107050b910001e41c000e51181c58002046444154034034071030200c003001260340c590000d02c0c0701c504040c030a152000c0001c04040c00b40c098062143c0100d0b100b4001144103403003a54001540441c00d0083d81285440b1b03 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 494703066 1250 494701816 494701847
    0x50405090a0b09180c030102041202031608030d0b0a120807031b020109050f190306050a06080102090a171509010203070906020d020706030b060d0e01020d1103040309050114040e090c01 81
    0x81c8a0030b80034580b00c28040d650840e108000c500400b0380c050610f5890202c000f813280d0740561001038005901400403981c0d4482510880c00e590100b0207050011884101902803001c4c117800c20002c5400c0b000a96001024051001d080044000d0341c030784507581c0e4a512a8000d41d07400c840002d5080400d030f0b1200492258003415094100392444980000304428240e001c2c4a009881201400e50b00c0d80d202002d40d01e02040b03100c01c0c003802941b20b14200010b0a801e0302c1c16044c08d4200700c0e0100307003050b040c02680c0c2184400703403003800f50a243c924184d0510f82c1c0d40107001d9581c003d86418800d81708032200f095205501000001d40e4034103104000410728071456010300215009048400011940480d00a044405a16000c80c001451038001452440f072140c4482106162180c3d1075880b601c11340250180940a6404112407543c0d109803101c1c6100c1194010001104440c050201c0c1d03000e08030092021001740660b6003802c1d20f60a02d0740c41c2c140203440b041d80e103070300c0324441074003a40e130042c0552014001d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 494704316 1250 494703066 494703071
    0xe04151221021504031106041203050127090201050403021201230702030a180b0c010504050705151e070803010611060106230705010b041514180c070f02030d050405090a 74
    0x14605802500c071555207010745500600100132409052040c1020304100c16200d0a4074184c0c2410315000120108990012000c00c1c1060000581c0030401564003260500c20620021840840912000100b1110404905012080c030011025031a5401203c070f125100e50000074110b100400d00c0e40c01503500005040d00c900c4810100a00e41c2d82c0401611242c08807402c0c81103015400c4101070410746625000305040460115000f0040e050541001d070103180035000b5076440e0707038032041804011481e02604a031002c0c400c12101c003e4258014203084050681c0400504120b1079684504250344203a102070001050101c0394003010070180040e600500f241c0c10100000783c1c504406142080100d004100079500100301a01406001e420000030030000520800807800004580d81a120a40c00781b41075003004103000e04610309120701c0441601100030410980d59980001d0400782d40c2c02401c1c222a003d01c01000c000058a003008003505004051b29440c2d00e81e8107110600c05526001080401000e0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 494705566 1250 494704316 494704373
    0x504110d1e0609050103030c02010f110d030c080a0b030a030503070315030f050c0315160504030507080303090d0201060311060a030902090115030b010512060603040201020f071410050702010e010e041512 89
    0x240c000d507040d00000d9080c240300030bc68480e0701090b0340d03400500c0050045806100d51000005138540d1145050b81c0454403154101e403100d0010344100ca0365401c6e00c541550001c5043c40109000c9c00103141d00c0f14a80c81e02082703592904104814240c42d81e40300701c1d00c0f038501440c61405c20400380524219401c0c103800038424100e002c102620655401760280c0840101d8507040c400141c8078400300c40185810108030307807045540e120010380d42d50080390400683c0c084e0144003079a4501c10300600c01200d03007214000c10020103080411180d031340b1070000e03241410b41d80c00b800e10058860700615402042d0018122040894881016042e03c140142e241d04100302003001503440c08008000e03681000d8180c0e5500d46941d560b1005030314024010014003001d00c50b05100180001c2030690440c01924252404511040c0f80742003552a4001c0e41c034003e001c1015546001c2c0340f0f51040c50701107880e0000410105802c01c1c006c2600105000c00d070804003042c0c07003011214040c0043e84402c030000c469402001c04411 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 494706816 1250 494705566 494705573
    0x15030c0e0403081803090402030f04030219080d050c0d09060605040f02070510020f0702120703170a0f110c10021b060403020112050a0603140610080708070504110d1e0609050103 78
    0xf05000b031062141c034201d0941d0310200d03e000c0003920b040001c0500110350328103040041289000c3c0c1107030110010301c55034150500c66003045c10840002035200c1034060805c5610028840a040003c01c207050b08032062010040c6016940544120140180da001070100e082600f4032085d9040c40a900b01c406004103c1c400004100283c0d0a464801103940141c40301210300b40c40c00b20348a502c0b00a5806807564804e0001e0801c086003400c1201d2040600e0b1001c02500c0b414400280900d50055011903603500400b041310780603c1c1030b6110684c2060a40e6030000f05400010b13010003040d0070388030042c1d000d1081402e113403111880b55040da94040701d040e420b007461540020144610f80000b01c41030364a900119030030078400e4100c0d40296501801484007034030136100030307990f0315402c4a1400c0381801c0780a000640d900f01140300010780311410050700255040401380b002070480307040301c0b0704040030410141c0c241620f244140f80301f0004c40d0303103002c2c030051205011324159001604180d00242c0b4110041000 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 494708066 1250 494706816 494706827
    0x30807020f07060e041d0d0306080606130c021e07090f0204030f031812031e0f0206013b06101b02130b0a0e09010609051009110d15030c0e0403 63
    0x84601c207107008400a02c1050204010f0450b06d00c22490300d4500350300300382c4880c2c408694003040c2107440d5410000180c5d50083d49954000c140d5010f9004a05040c0c03040f4458115080b1030b42015040c01203840d81010f190f80d54818035100208032907990081c0d48207100c585c00b00c0c0030b15101c481141c1030640c100390440e2035020812601b00c20040c103011000300014941e5809404d0403000700314110b99a0541c3d6883e00340908110008040244034000000f0080040c0380a003044400c1c5081c00d90003003484c0c0c0e00b080c100c601c0841c40d458400c8841a8400ca0961041383d00d040144104108051058564107041041c400d4502c0007010030320511820888140c0003501c1c2c591031a82c1940c0440c1d580b00c0c024160b2035084002c104040340719410080100d00422945c99801181e809266041c1c000c120b880e03600c1650800315a01903a030340c5107141801c1c008010f003a01c0c641110045d21002003c517481d0407d02540320084070840d022056103103800580401c140710300e1041c60801010150b00707003166413405540040c00e = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 494709316 1250 494708066 494708069
    0x3240f0f0506030f1017070e0106080f010308030901110408010b030f0a030e10030603140604020909030a0c08090a0815040c0e270304090204060c0b071704030507020d080412030807020f07 82
    0x7903220000031481401e940e003500040c1015900704094424840200e41c40d560f56010340c075948000140000341c04bd00c03803c00342c0e104815040d8503c0b030076400c5548100103940042c008400541d289c1005031500300d1600000c0c801031503503100020701101c19400f40b6003040f649407004110350f04a02c000002207a00008442d0070717a441150402c1150a1507403042d001840e00d42c20183ca19182c0180e01401100001407060085000b19144c01a07680c0300040303c0d039031348901c0d46200d0004100e030b2560000114040d0142420910003403c800845890b100c00920341880103000c001c00b200f20005210603c07001489800241609424118407450546181d00704c91102525001528a54221546540c3c1050090740c0c050005560300b95540c03503640100a14216102d8001d5071941c0415022171002c0d406103801d038a140c0082541c0840c155559202580c01e07030402402a030b0082d400384003500008200c8001070014001030784000d02480100d04004000300030040600c1c0c295400f58050380c4143d03000003000340 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 494710566 1250 494709316 494709331
    0x3070f0c09140604060f1a2d0301030b0a09020108072d020c0f0414070c050a020d060207050c0a060e130f0e0106030209070e011e03240f0f050603 64
    0x4501255494a100001a19440014080e00c0d1001020b000108210660f00503442150103102864071080c0f04008240a4840c980841c01c1250545c045d4915202c043c2410381c444605807010245c0c40640390340022a510b1000d184c52170300200500c10844030141040c0c0200003007104028101c1150700103440b4401c09001707141400301e500ca444000401e219442c1500751200100c1c4014240700e9413019503034405031480d16204016600781503246080030f114501010240c942035202c0c40d194004203482071142c9500990700c0c0d0051000c13900268a0754419003e00c40c0c401c4400687d1101c0a044c00340c2480c041c0d06003188200c0d40d0340e80400030254443d0b4002410300c8112401120f01aa2900b50401090f1980000310240e0410000c41d5048078194450310480c0d009030340041300b40d600c14a04449a00c000c1412030302003840f900c4c5010700e80e44000814192580039086c0000c00141036a0446000f1102070b071500c0601c148100c090000000c1d8444003402405a10440b43c0b01070b0500d00000c115000040008 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 494711816 1250 494710566 494710583
    0x1602040902030c3f070515040801020406020a030306050301020a0e0f01021e0d090b040e04150209130603020a060f0203030406051302090106030504050c060703022a1e0307090c020307 80
    0xc096607020300035140100001003d02440d07000380c9044c07500031403400101d1001401c0c00e1030714088016a542011091190500c0074248150921081100d06042e1040d040020581403201140b220001d20040000d410141c00a210301c440f0f80c6030090903500140c021701d0090b40140014580c1c50b40103d07904511584c115010707082042d070040100e2804200c4100251140c188103200e0221a00200341b40c0d01541955950a980980f00c140740e581521503841144496030741e50700010040362036001c60b400041010310000d0b10700604940003510781030401760b4a40d1000d40e964410001c40c54021328010040c241414a405036503881403019440b40001003000d80781c01d86590015000302030f415a018045540100041c04958403000c0c001e0040c01c1c1210202c89074441c1c3c0113080602c3c500841581e07101607055009010400c510b00e0418152000d20300c0e030100454019014843c07665692545c0c0f1905030904400d00008c0001500b00b524007043d56001c212094503100c80e04031429030101c112041107030040c118 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 494713066 1250 494711816 494711831
    0x9010605031021022e1d011e0c050106090c0809071e0b0c1606080a05070318153e2d0f0f030103050f060c1e13080a030212160204 57
    0x762920f00d40149100781e080c00e50045800d13041608491b81c074200002d45946404c042503280019211400a20080e0b1400910880c100000b280704003900316800348140d0001c201103070b54816800a8640421001380072407030100811008003800c04c110300c01080303918070b030006120490360300205e41c0442c3c1c000c00204000000e00602820f40030894940d9000301c847c00400003a0750745600901c4a40140d41d9112200d01703200100e0780c071501c80c2c081d0b00c03240704c070540e1003500102c2d807030742c070254401820301c4a1103100e52101540b88031001070120903004407002d034031001c0e0200045180c0305000c2607110503140203100180403007501089144010101c5010702c0030001505106032086002e580248080340c0c1c0300301c00010718200c1d010040006981241e00c120102c8070040c0740b4200694660b541210803442c1d110301440380107a0494148990050f00742d818030b2030f0385081c5a2407100c00802e44507400198455100418a00c00c243d410451889645216440c02d41003143d083e510726004488a00042e2061b600e4095 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 494714316 1250 494713066 494713099
    0xd080105060a05070f110118061d0118030b06040e06010e0a0b011701230607020d11040603080c0f0606030a05070501030c1709060f0601030c020705041a0901060503102102 75
    0x21506a90b8001c036011140510314079001b1824203044244034002403100c42a0811020828a07075000e4980341d0716410b400c04201c9403140307200e43e80b24071403604001c204d65144d810020b603001c001010f907015200520482c42d00c030083c001604c401403900303044c95100200400140361031600403078000302c20140121b89084d1160048a44020140c40c940a00e0030f000000030f1f011300b10001165202000400107080b4020140400c003840c024450301a411900348405031000444514440018500041c000100e0750340b240c9036000fa44d0820585000c042d0702100614811007401c21250340d100d0401c070010980c90050f9a60192036400170311840b070615482d90b01494299014045120141c80b41e100742e1031551030543e80c4540d4603607050700c400614038110400700f01c01d035110340540c80040c91541c000b0902c1d949044103110041004070082802500c000360140c2050303480e0038500d402020160348183c0c0380d0802c081040d801801e117a200d1000804090902c00c0700e505000d451503074640d0112640c40c0f4401c071550 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 494715566 1250 494714316 494714327
    0x101e0e011e0230040f050117041e062d0e0f0715050d0f020d0c1b110a0302120303090105012112020708030d09050c12191704170d020d080105060a 64
    0x1800207901c03d0001c01d022881c2c00c0000454801c0300e209a80c0c0341d01d401141081005c8241d13084c1c4001c1c14010f68110140c2c02c0030909010491008c2c46100c0000e060108940450404040f164045024044a0784142207152080c010b92169842c0203020300907160148403426035903038061091b184004a5081600c1c01a406241035910b00000c1c602c0510056500c10203020007580411030f1450401d20f060700101129209100550522881000d0300e041100c0b95103996000c2040d260070305034401ca250001000584030442d100c1c0d01311055500454032070800b42071071400d407613050b0800b600c0c071502d0030304005070301c26015a00b017582c41d0840707910b1084040a2030304a00b081c1325500041142c0c4400195500b880f400f50788a0042a4058411b40b01c1c104610030412485103051282c0508584c414000c1010f40031045407284441c5220384075144d600204810400d45642055002c0b90031409050a50040b2550a0010401e56451b9201500c2e512400301070241c01e102040c015140900b03004201641d125001d81e = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 494716816 1250 494715566 494715643
    0xf1c11121b03070f08090102060a060b0906090310060902040314010b010507021309021801091512080a02151e0c0307020601030b180609010b19060905101e0e011e02 72
    0x48036020341c2d015805c0c41c42d0f09903c090b95050040c400c0313000142d0481654030500c015100340d04202031401042004108042d00304072001e0b0340c14090700d5141414055907100300401003030501e00240e140e9145060003031555404881c511481c0c3d04006101010b40ea000e003c071000d00341e04440c10341c2040c000391401c400900d4541002500600421a685200280c0d040c0c0e40f4101c0c0c82e40c010034003481c0700c82c0306521f9501e8410310a0764482c19018812000195034036018188a440c07501c1114407550480501180c405415120021091907424504d51034114040845a011040140c41c528605102074029501e100510024284181d00d10200d0400d14000d040030031090100c100304da5490400040003402002888a081c1c812008062200540d81c0c500e40e40c07100300d4150b519000c6034945800c05000100c2c221410101c104818440c00701c4d29030194071001e5151103220b0f5a01c0c013810202d000054140c3c0300355070f513002004440c2030844240d02e0b0700040402e99800d5101e941d1102440e48400d40c03000c40040c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 494718066 1250 494716816 494716823
    0x507050613231e0406080d0504090207080c0d030903080109061404090c09021b071403100c020a020a08010203040c29070f02060c0616210b01020f1c11121b0307 70
    0x3100382802d0340805000e103800c00f2240c211000c1042907502c0c1581640d0b5140c01c4000c0002c0f490074801000303800c1c0d40da4050468140140d80c21450f00b0208125181403290003500032010a5556040406155004003128013400d03a405003040180d09200d408100e00115a2a0902c1161038980840c104055041a500180285003040d501d911400d00030004e8504126060180341c41240c0b800a06101c01c10303500041c450018000d02a080041104038000d004000c0c040800c0d40701e081403030401611061035030300042111000043e200d003800c0c07800c154076004591042c490300b200c500c6a200c80920f003009201000700c200d403020b507843e00a451303d018941d00c00b5001940c81480400d0001c4500c1c1d0110b50300740300304980c1401e2038504081100a0300c19601c088100000030044000784154074190398044084214140106e13004030007100ca00302e140491544600007840600030741400d019804c240c108070032175016000381c824080009044590fa02032030204030f8100c050780ca0b4218540d4010300031116101e81 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 494719316 1250 494718066 494718079
    0x80a0b190906050411030601080c0a0207050607030f030515011d0a09110406090b12061509030610060210020705060406090c1d01030201080a14040201110f01020412050705061323 78
    0x150794507420300600300c0e803103010b0186007415484111300101c00110791082c6070503110000e007a200c10807407503019045a00e605e410f501c110340b0003285a80d141005001c00354401d640701e091004066a0050658001038406c207180070001515450300d071780143c07001581150b04034420006202880025001c0b01c0c050707010b100190715021085c5c01043c9400700500c2030310840d4403201d40540c0c0c1c80c01264040e118400c1c48140444001e07010610511300030000220448825544900300318481000a082007001e071030301c1800000a4070708000040c0c0500c9040c180070040c010846c1040c07a0364883c1d9466100003040244102d0391280e10740c040000345407803030003c0c0509040c801d251144143c040d01c070668080c04260b000c40d814000180205455008411a000240801c461251201d03801940c000c0560303038140784580030303101190355103e00c24405080203050f90119a150303040603040003800c00740740d41c0000c0d0040d40100200d604840001c0c102c0d404450049900000504105040d0700d4126280409540d0210 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 494720566 1250 494719316 494719319
    0x8010e070b0f1201030606080609160b090f1801061e2715020102040305070f080c09060111100603150c05030f061c1a010b0c12090a03061e060602010c080a0b19 70
    0x6c459000300c09858080044a1850310381c012125500c540c85410a1002c800a0b20144485002c100203481118000303170500c01008503920000d60f5048514105507030035023542c0300402030541e0000c00452880000d8016410740040403d00820010742e0103c1c401d1400424121401c500c80b001d40c12100038003580028a103100590b16009010758414482900c0701c0c480c486001c905214010403080444044100034840034885105005c2501401807016043c051032580b40341101800380003d641901c40c0800c006030305421480e044404035690303025038040a1904c520724032902e40007000c41c2c0c3c0100800840c5281030351808001211410b500c1c88116a5440d1590950700f00a10000140b00e00d15540c1d8105078107a0702c51502650a00903000443c155504c005007a80f41c5c0490394000b4001d204000c3c01076000a42c80303440d4001550103040f2203611516622040c1510000b0030711a0360003074002d0303100078465207840041c000c01c0e000f009081200c1943d42d42c0903000e25540e40400e61106e14014414112800b03 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 494721816 1250 494720566 494720573
    0x9150a110d02190b0411220f020c0c01080417120601321b07030f03080c0c15190501090c0e0d080708030405160e1008010e070b0f120103 60
    0x4110039240d5240520a03800e11601c0503001050401c621031201d15101c1c2522596252190b00c6403001d007060340e8000ca040e80c95905078842a000d00d10303001c200b0307060104540712010b0280c12160700038400500684107001600708070a0100d51600c114609203000c101d9503c230b80c04c01d680c8040d6804615002c4031400501217807400a0303003080500c110700980b5014001024140380c440c0c09a0b4040307003e241d5041d81a60075103042c00d11400342c54021070310040c07900c401c407104043c20329140c00c50b08165520300740705102c5000c040c2d001100c2940030510060103403c113130500a0007a40c0d500103c0855030b4002441e00050000607161101980000e41d07810148400c3d6501c031220b00c000c0100c80c0b922400285100300c010368a084c40c110b07a841040d030000701c4918010307560304c41301800d410280081303c05000d085070140810a401404a0140004a5040d807150500411541c1504001c1d80551180c3e414501510140900800c01d481150510b5800540e10350740040c0c1c40800d4410440c10042c655045030010090 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 494723066 1250 494721816 494721827
    0x120509190f0902211b0a1e020a020108012105010e031e0f090d140109030c0b011505030a020912030301090209041406090403030b06130b030f07020325060f09080711010305150609150a 80
    0x43d051310400d41c4507d124100b20407a2180720b804006808a0940d800410a00d100d07003170040b0014440381d40d01504110301d6502c050a44441da1080c03140e40d400802c0c0c250088091b0440c1190318580554954500388051149107840d0085d01c2c4010300c82c11311038a010080c0968028001c4018407000020050700545207006000001918019101d100040c400411864690304a500c0c3c00b4420f41c82d620300315620000040043c2d4406001d540d0002c000ea414443d40c4403040000c1c5028242440015840d0540f01e01030104030b845242c10140940301d0001800110f4540e0800035400541518003c186000554041000c3d40b051404d000c1051052441c00101c880040d03000d03600a00c004500b102075620703a0041280c2e203004810300300c00b40e1182101d0f00c07408002c3c5200d64510041c4240804101d0319980041c203000c03a0066007051340c2c11400041c1c150208020480780100000e024201001a0709140d0951002c03442010702e01d038054400003803801d00710b6462040d14000359404070b00c0f8580d40d0b958804010700 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 494724316 1250 494723066 494723087
    0x10f0204030609150203271009080c12090a062609010c030b030304062f100e100c020303060f030a060501170607080c07120509190f0902211b0a 63
    0x40320928130034151482c13981c50007240c1c00f8004c3c011655030000100441c48030918000000100c2030b101e10107040a03280954014200ba05019240c41c6072101c8074203d0340c504280130304100c100c01c00740c10003080c02166540c0412100396a0b0624150682000b020307000d1902941d010105032a420b030040400024080540000204d16515035007440a40c1e030b00418141d40340918041c1c8004030351100800300b100840036607050803003881c1a100701c80d20403101d40100d04011566841489460711201a480004007c02c81c0720400b201c07000303041040142a0900039100c1c04080c24080c4070b110f898803080580d5030f0402c07410ba110b40e00440100469695242e401c545503841c00007000e6507000d0040044d0340c0c1130040c01d4545c030038640081c1c01072800d6000d503030300001e1081a00f0b0140c28410148040015510340030340c182100302da8151b241d4011818440f51601e10300043d8404030110340100003444000b001c0c4011135a4041010000303680742d440e0300d1002c40300d5185120b000011b6000114003101a40d90040c81c4c2d1b20b = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 494725566 1250 494724316 494724323
    0x9060917010e120a0e0103020c0604170d0903090e010e091f020c06162304030f08070b0712051501020c1003110a0503061504030b070e0424030506101511010f0204030609 74
    0x1203851700c50041d000d9000b16001d000081d04100b0010300450320b040080000c0580c00c0e5001c0d40303440301a201c04d4040710802c0d030007030b00020225981846050429100c5e08d01400b60358082c52020f181289020350344008000728110f540e500500703416091b00198040d1101040f030002900d555240540f141d0781c50075000b203069000a090790342c0a045071803104c194141400100c10500c0d20385030031038491041ca003200c0d00013111855000c00c1b0302004181d0114000b80100d01a589881c415510700c00e054040c3d9102402000071741085c141a1941a03800080020400d0410b071181801e030248180250000d00340380041c0060b254001850043c09907110004612031481114501030f19445552100e03414000c40c000189a802e5103004a100280a1402c3c20b080d0765006001013219040300703a117640114200352040080010300c400900070402c041c070031640d0241126404010345854100400c000744070000d80d180521602503864009c02e1003e4101d0001c14802400565442d980e03032810b0b6001b8070b600017056 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 494726816 1250 494725566 494725577
    0x50a060e040f06051e131406010f05032a0c01050907081605281a0a110f0c13020405151b0109231014070f09060917010e120a 55
    0x40c0c07284094030070a070a0b58805001c4800c40060380f0442582c6405c0c064105501904400701011003c03401d0150f2880d200607242050010704044001524946072542c40000340941842000062004843d40545094220dc003200c0341c03000c0c419044900b88a910a6501d855081a0400500d000005084d400716016401105c00800d1007046141e501020b0b409030315030001c0307181d00501c00001c3c1034441d45200c8040c0c01c4459076290b62401220b00485000702070b907d08800100c4c40c4054581c00551a440080701a00600060b821902c40f164407101d44d006528882c0807900568945c2d04041d60595000e440064912031061040040011054103da0142010340ca80304010420b0350310180511486a80d11120784418452110b02c3c018210f80c0b00d5000b41540d12a50400c036482e0b06513030060170591844003201c01018100301c40014141590940d000d020700c42012802c205070b6512500c0d600446141c0c3c40d6402605d10316000c1907025151000410f90030388252203004a46c0003040c0002c045100e4103482d503 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 494728066 1250 494726816 494726831
    0x12051008070e0103030801060809010216050d0e06030907060c03090e040807061109030c060c120313051e1b0a0b0a02160f03020d06020a17010b0903011a1e0109050a060e04 75
    0x1900da24402c00d020040014080d0790041000340d000300c889581140486001600b802d295881c0c11071012000a0250740542c84481a4105140c00252021341480240c4025155141003904142d40340e1440c821103003004070f80341501052500c20400c04000d0240342140d2141c50805080400c46500840b6003541c038145429801000403500404072001004040c0140059490355402c01c461500481901c0d101c0b400b40644e00600221080c0041d48224212150038003118080d092083c41d01440785460f9900310713800c0c1011007a159002414146030840200c1000010013464081080180b81d588602c42107007002c240408010303000f040b412920a540700340c140b10740b5541c60010045900c0ca1201940141350118550081001e81c2c006081c42078280c00d2441c0100310159088062500036400403180c444041402b1a15142c203000e007100c0d08030410301440d501c0c0c0401c00020483c03241004603041034210220a03c00d10790180c521280104002030502c0d140551395040034141100405c03078244202d180061 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 494729316 1250 494728066 494728079
    0x10020616031406090403031d060a0605030102040506042d080a05060a0507050a03050c040e01060216060201050f0f130b0a090506010b0307020a080f04080a1208070905130c1205100807 80
    0x30740240d03802d036041e80c40b1031030300d6200500c21444030142082e010035458161024110740080940c1e12103003003440c0100040c2c80d000340b8482c11100260041c600c07070790040004018940d0b0f203205940580b0742c0700e100c04552201c2245c0b003880040311854008215040b48200140001002c81d040c03015600602c02ea0782681d0b0b40d0f00001c0110781c0e044400b48046502404022400e40c426403040f0760010700403403000d1915481e0580048544026030021005920500c81c01c0d10403101109410000c4c00d80d4002800035080280c281c3c042003d0083c501d0698142540004080740c903030407a400e107a140c01c192051041d040041244018000d854010b690911503440005225080c070002c0b0b91046003281d0150000c3c1c0c00f959240e440d16403103882006803242051001243c9244240720100c61144910040c0c00c41e0329012801905162008081c2414007000b0b4204000c9138540e00b40c0c116030114003030000503c51003410700035503550801174003041c6040d00d0701081080c8041c9460700c00040d0756502c01180c071117595030311 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 494730566 1250 494729316 494729321
    0x70e07052119090305070b010f0501090801060614180409062c060c03041a0901051501083934111e12011d07050d0f030507021002061603 60
    0x4030200514922182c045201d4100b80e40280303c514820300e8640e1900701c6e191112841841d00f83c1140c03000411450040150307682002d0f0f124020f03d813042c0280b00451821001600c3c10803a4a070500d080600024500902c41c61440607580ca1386d4000c0007002006020300b4484020072004284030030984407450620044003600700c0d42aa03c640580040144c0d07628068580003613000030b4000c44480c0300e005030b01880075000c0306808d4895291800002420716005c80004008903000c0c800724180030700d0380240000004200007030000c03241386109075000414000c0003240000c0505000d1f200c00840415280350403d4482111400c2100604081454800412100c2612200540e000b800d04032120414282428880c40c0480010341e01003881c00d5815040e80030450400b90b10840700703101d941d510703200151040ca408003030100441304002040000e06000100e030340108201d0303024000b05000200c2400b0103100d0f1046500641e0301130039a0000943c0c000c0301030b54074501503078155102203940d8949410750348640b = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 494731816 1250 494730566 494730571
    0x804090e01201201350c0906040902010507030c03050f0703110c0a060804060b0307091e150f0611030d0216060c140a0302280c03020c240c070e070521 66
    0xa510380c410b030740b0f0035100704201417030104c20304121011207001075116100c9004d410351080c80400602910300304102004842c64005064910592401304508050307607001003a91010795240c10700b41c00001003030600351040d0140705982c0e1004400007608800b01a0310413120000304047c10200c2d554a094035040000c0c494043c090503001070488000140403e00030b4108a1815501134140c50980740c45624142c1a83c041c06801103182080500306034401c240b0340702e83c04420410b08100701c01d00b400c296414060040500c60102040041041d200c2c25150500440d840b1501c20340007195108403062281c00241030780007058070306500c2d2800d0450b07607501400f408030725048910f60452030b048036401c007030f4001e410410341000f020f92010003101e4480c0c42804940f070020602d071141c803804040351030b00a2401402411150041102c0070081da00304000700321690802d2850b9131031030f450700000b000840c83c0c0303002e552001d960306e0182ca003884510382d0040028000c06043c3d0400c0051400c01484110405c0f006 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 494733066 1250 494731816 494731837
    0x7031a01140d08090405010b03011d0105010816090b0a0305010303081f120f0f060614010302090307060e18070305070f0f090b090a12151b0903020603040804090e0120 73
    0x141c031007014561078000c898018a0b48940a002d04105401000c14200d42d0300340c110340c09008000005002c052080c0e088880c0054540c6100e0711658103000c002080c05030050042c1c400c8074030030403241c2205805107483e0806000000c1c4210344542c0810001400b80400b88819008202a034021030040c01c410304075042000329041410001600e096a05425944c205400384c840c88151461480000d410f142400303c2c542c051310001c10301c94203115a007040540991345182c141441000300490a403000300703d00d01110380c1410040d007009460360105424841c9000040c4030f200c041400c2000c0c1e03903055805140142c0c0c83c2d9850706d9401c02c0190060b07501c5000c3d0a60040400c44440b010481c800345580105035021015102000c2c036a40c07801c21302c62400803490203c44420780301d25100001100340c4142c504220a0b0150058013000c1c055000e4450515408081e010701c0300040010207000b0f050044170010208030300100700b008400d002030342c001e20381c1002328950542005400d01e101c01114081d12802220b = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 494734316 1250 494733066 494733089
    0x8010e071704141e010605010504030201081302042a030c080f0f1b070f05100203010f360902031c020c0409060b06030903120109110901030f061707031a01 68
    0xd0300030350300707048000100100c030f0002d510240112405028001103901d280048102118034100350b80b443e00351084e6801080c10003006000400142c0c0e03200d41c0d031039004280c0f1580300815241c01c0c000700380549000d00c0c6440701144404003400c05101d100d082104084000c0d175080003030b0318610390f04955907442030f600480c0003035614010580c0300740c503125481e4000e4105100550740c443d030421403040e0ba801800c1c0903188004401e0900003480020300c15a884500c818804600d15030412440400704c8842e4001c12001110705c0344241b40da60340b0004840c82c014411104051400056003190018002070300c42280203024440c0b02e1311134043d0148081407140031907005085810103050500c0300400800b42c094820036140c00b1202915140c010096020b030452034003135941d982d40c400014a000106900c04403116180007061824106007406072070491a09190101d0707400382c85000d80e0701400c02500002e00e00c6104c0001c1442c1c11f00005044070480b03100c0c46c0c0c94a4801c5100d084511010424070070241e280f00c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 494735566 1250 494734316 494734337
    0x5071d0105031e070504030b010e1003080309010209040f06052805010f1413060801060c0302060a020f0903010e010209011704112806030203040c08030c0d050d0f0207050d08010e07 79
    0x103014101569000c401002442007000e0300010103440e0036401da55460201d0340006c0d06006000307507180c040b80900000c840752602c03030405103140b54500c8002d1001603c44040440800c001a8084d0101c550a0074001c1091241c0c00d00d003212900240380c14403402d44200514094160400500d11b203860307034116a41d410303181c2c040c1b6140064546e40280800d2604101064220111200440010b4071201c008106030040090130207102070502041a0064001e002c003e9140c40002a0f000403071541c0712900c030700007507240e9400c182c903100c0c40e02541e2641ea85c154207100320058400380545c054440108240e950f410b0745000c5040b45901882d0568003e80210368108002d15142006440c1c14903107604400c0f900e049500c191443c0d0718501e050303041900002c1e000410b02040c0030080003050301074a9803101840c50711100d246015910991400c101003407080100d88514085866400100800206103083d5542c19451501f5a01c443c2e88a9403003011420401c0003203a0380f4100741c066407041689840d0100583c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 494736816 1250 494735566 494735569
    0x10e060307020a0f21050328092a050d0c14010c02030a050c091e07180f120b01080f191b03050a050d080c07081c050f0a05071d 56
    0x560005040070103501c20620100300042e02910310445440c0108030188030f011611004600700b501808020301002400d1090110780f03c0242c140d151600400c4c20754520b171465110010025180705200604002e1003e0442d200603045d2a04420004800e0490700d15601e445204000e00420048000741c88001d02d4201406a540c016080d0f00c444601418440d03084000d42c0d000a24200118108640035041300080c24000d080c0364030405d80001c60340390000e1a40c17800035031b210032601006200c01d0030020789141c0c8001545603070103440b000d09181b5040c0100c0c613884000d00c560714544081c048443c284400000034480c203000c51181e115294281c0544945020310303455407005d5085d0744040d140408000300428040000d402060020b600c524050700740083d09051a504040704040c0319000d0204008c1080700ec1003099044407101c1c0c1e0700a081c940c45401c1d040200150b280313440707075419440e4685024059101c20161016200da40b03808803c2c0001d039283c40007201c503001c0b1070f6680940c46a0b900c030081000d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 494738066 1250 494736816 494736829
    0x506100821090607210219031704030c0b070504081b010c150209040c1115010311120f0706231606020f090d080310080a1511040906081e0606010e 64
    0x9034002c1649041c224680c0b19040504103170544c441100b40c1981c07080d0945a01404000c410201d07402210162082c1074402410031814111640c1200c0c207940300107420075014440b9119240c0c5c0009003920246410040500960b01900540d1181c2c8115108840d40040e182c580d40d103901d1069660070390140741d070703514101f0342d0700308510004647d80c082c01901c03040d898a10900c0e00400d01d0365150700d00426251a0340c0d0030130849407074221400c03103504018008181c000e40c40703503446281501d541c100d9803007020f4202c1c00c24458001002d06809074900000d10642c0c04509513010701c018216009840c0a200030450040c030821441042041c05d2000c9030300420340c07690280c040c04426000c40392400c2030b0680001d810042100040740c2140d8003100b80800d210140702c1101c080c040840084c88130f104181c8403100d0004600540800c0320f5118101244016003460a030b4005001e145818094951203a0440d5110f0050700034100d0078264aa080b00c0300d001b000282ca0340942410b84840740804480002e0146 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 494739316 1250 494738066 494738077
    0x714030a050102071101030c030218061c06030c03030f0206010f0e04080d020307020106181808091c0b0601172a04050a0b0309010507020703030f031a0d0506100821 72
    0x18180039204511012950070300050001c2c03842040b414403050032940002d0b08591a5000c544100b610501c00c22544005001700c0c00d082210447e45542c03274500e880c04584011a0955911506034241000001000b8642c2e4aa00c01e0f40c0c0f00c0d84a0f002122001c41040380d9a01c4244104e241d20b400714641000496402288983c100340030b03000c00c0340740c5202e041d4001c09983c400d80d003c0c2e0041c0e5550104120022400900d0303000b0ba10050b02c01c2c410300314541c4040482d4800300c0006010038000054610032603540d60178119001c005107450102440090900d5803a40d02d04540e070341c2c040345500e6041804000144070580c41040c007881c18061603000381000c8091404024904ea04808c0308002c0401c0c1d554420351040d00078007100c10383c90f0b0350380b81c5038110600351900507217a0015507105840900000740c0242d000189440320f843c00244c170f80c40e410f1304080a40c1030740d007030340b50058030000c099020b01402040040c8600e010518881c4507070755584c0456520600c0e4840e6644940114607a0007220903e40c00820 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 494740566 1250 494739316 494739319
    0x1006080403020a060c0e030705041806020d060305010e071403150c160506011707080601030812040602090d0b09160807052101150305070e06010903060203040302010e37050714 77
    0x344540f0051391104210b51502400e100496a6582c94848070701e0100005009080c050740c051103964141002c1e141103940044006240c3c94010803180c1620100764071220045402000034000c1c5e50003c814140c80348000d0060b6a409039400241e280e4a0400060104029400099079a203070b940b100070100107500b0204690303000e6400c1d0060310f00800c200b00941406000c55800180488034018640d600d020420f6002c8015500030f04c004001048141d02914007000c0d6001e43e2700301e295a13074a0000f009106403115158021080800304052024414080d07202d02001c6045604c0ea8294280b41c10204007a481400c9441d0701c1721750700f071041d801c0c4108401c0068000300b001c41c182d0081c0e04102420b4610102d195002902905410814480100035030300003010560708044607402e110b00000c0c080e040341c0c08041d026a0b000008101010700c01d50000f0242c0004c5001c2e034152001c0f06c5000801c1c001e0440c440105401134051041050f94082d5581035070a078050000c020142c94804000c03c032001004a09 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 494741816 1250 494740566 494740573
    0xc090d03080a0b09070201060609050102070b0f0c0a080403030207050a050d0b04060c050d11130605120c0a0509030a1b0611031c06080d0c03020d082e0b070605090c040203100608040302 81
    0xb0410f030701c41310800c5000b002c42d0f1700041201410200e00901c1c020780740e1300044c119440000d0400401e114a001c860301503842d54119170b234602c0040754031b80c40c00c00e44802c002c000b0040010000241540070680d0829a90102c43d100c0d03207141d6450400540408405000d00104032000126001503000c2d0b004a9076024141403981c01c082126001200300c0b030398510a41d8400c100043e0744101c00c10280807c00140410307040603401e040c030200440000e0300004003000409800099480541805541a60302408004040310a61070f660b1620110180502054002000f00b888010450b103020303000d15002c03000004000c50410241e1607800b1000c03002c00e140b0b040504c2da2100e0104c1d00580900400c80b118034141c543c1880c0c03008626000b443c144403041d0f004104409001800100c84013440c50030402c00c0e00e03500900c41080005582001d2103416440551b1048000503c2010050303160481071040c0614015074100308044824801070348401c98603440c15080d80c1109103c0107004d054039a030400d00a204a = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 494743066 1250 494741816 494741831
    0xb09030d03050a241a0c0a1118130311010506100c020a0f060f08150a06050307110f0a0302010f180f08040810090209100602100b030309030a080306090c090d03080a 72
    0x9200100c59a06002441d07072200b101c144080c030980111104901c9890045c41e1400521007101078686200000060196440e2000c5554913551517601d44000d04001010341018103040080c1d170080c03800c2d2002100880e21807080c45980360810310442d4401c1101420035480a4034000c0c0071501c88035241c50890303000001c100302284e034012003036810000e032032162140070b40c3c0c2041000c080d119400041c40d0b107125000302c08041c0761a849aa1084084800382e040003907d0b9100c084069981440c0600d4a02c69846000001440b05000080e070701e203d64085e8000b086044c1c1c2501c0c1e500252502e054003d0200b91074007408400140c2030504040800303015483c024146038031108014180b103541148500701c80d40310b601c0301096140084510ba0030074400f03d0119040c61a00c1d4002c0c0d1988215070484d20940c0d0b070781d885020300c2c0c1c405204440a0400042c291286a003091400c00091340055680500540300b003000207483c07041481c00c440b86031030000c2175510f0b0b4440540d0101c2d60b12070700400b5801080c1d05d5405 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 494744316 1250 494743066 494743091
    0x60906010807090c1e020a14030703021203092410081c0f0203040305070915050301020c0d120b03120703180f0e071710090b01050918040516150206010b09030d03050a 73
    0x35140e00651244c6d01900d896900c82c2000e814800080200c010680c004003d0100060780009408034101807034540940c89a07039901c07426050251050400142401d08100503420140420031103100d04403c142c8032441d16191880981d40303216881b40c06030340400364031031288032600400e28904001d110744120b915184d2a6510bc6091902c1c41c3c2c406a050303600d036412070144024071001d6034041d1000364001c504224108507034940d113591103c4c0540a001c065544018004400e0f0070480c040342024080700d0400c80d6145800344954804a0141c001038580b020030030b0780410011241c0102c903180c1c040e10f00318504020030510540310103094801800419070039010300d030a4100200c2d200b01c5800c0e001305800d502d400101000c1e54085040070b810050104000d40c50703940c8111100c0000c00003200d04c00341c0c41e95103140c40c51600089010302040b031004000001503540184442000102155003900c0d101d03681c90000c04803902550045540c1904280031411910744240d000580c800c80e2802c000c503215039a0007 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 494745566 1250 494744316 494744357
    0x6070224180f0a02040b040b100804023d0309030c06111c020901020c040501050d410706080609040605070e06130e0c070f0f050c0303160203060906010807090c 70
    0x70b0154250810800b50b0154642440380c5002c1400582d018800911040c0c00105044801d20a68007481200000700c2c00b551129000c1082040341104280001000d80c15039050303071002c0e002941c06020f0110b004600040c4030740039100403242d040e1500c003040340c540c0e0340d2a0041c181080306203440c401c0a0040d080c0c103000914680498030808203005903101c645c0000213091050b0039100c1d034007442c10000104078517110405820b07619a0003001215818070214001c1d282d1010000341d08181d03401c0948024203116050084d000c1d80102071080302c800f03690f215000d070340b4440221641c80d8410242e00004022450300d811081d40b11a280c03501c49841d0074000005400c640249030301e017a454020780e81c00c1c006660080c840b160000c142c095420300341071240c0c1c0c600c50380782031009008003022215902101000020040e003c11480014243ca840c0d50b90340340f50116505918905038440d104000c0891000d00000c44c2450590b0480c0d0041d2081f581001042c50183c0b6514580204004408032a444000f07441c0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 494746816 1250 494745566 494745583
    0x1b1e3006040c030201030e0105010806070e030f0307030806100311120703140f070207080309060d110f040e0402090c0a0f1d090405030901082d070c06020c01050403020607022418 78
    0x10102d0441c05030960000404035074900d283e05030168540760051102c00d80018a00703500c9285031402c00c0910385007501080c20a1680c1d50190b80c9440003043e0a810035800103c034a100e00c2090310320001e2482e6204040703007a0346c2e0744880a01424400c2008081407000c640c06140e100c0200c4c1000b20f68013503030780e20310300340881c0440b44c54035200c1d14442407080d200d07810b000e00d03802001c5160041d401d00100b040050020300c04c001e4010f9031642c0d1031100051610030803047c0c620b0000440119910b46684d22240c00c0c80c0c2c182294203d03c87c1840500207007948020b5002d8460310552542c840304660349209056030100c00d100b0007804800700c2c212040e003141e500c50502d980300f0b030310074806075440300c411000141c54148040e04504203010003003002980709030411203400740c040d0200c02c0c4040e1a11500820b13604850b07400c0d0040c1c83c050000a40084440054000e180100c5c882d508544641d40c40744405c0740c480c80c402010501d0112102d4502d40350b604000442d580020700401c181c0010b000e14001c003071920342d04 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 494748066 1250 494746816 494746823
    0x40f08030a091a0702010513050c10030608030a3209040e010f0e03090f01080106050d0f0f06080d121104230402041e09020301030c05040f06081b1e300604 68
    0x143c02003000c1150b080c09280d42041c0c046100a800c0e0781c0d47c4d9252916440071718007090050038621128403900c1d11980000001f0441901941c2c0d075204007001c02455a00d03205040c0030354040181049401c07881501840380d07805000480c0500708040351040002420344400361440e40d40d00c865186481d2040d5106e01c0198100d504c000f5a0f48485410034000c9a81c0f5490342d00c2d05101440004007d0240c00c542100c0e00107803140000101d50b1090190700c0002d0030300301b095644440c0740c000089800c41000580f01d08118494546091201801e002841990301c4610303081d4078118240010840039031540342402042c144000d01c03000c010003840104049030010380c441c1d1041c0d03843c0c0003605000ca603850302038000381c244018203600c1c1d581941c880c0b1440500764819940150755446258288280c00e40c40440941114000d41b83e400040c5140160410020400d080c80349100e04203c66001011030b4580c40d44080242000761007141081d00c4a2181d00000e1070135085021a140140304d080c020301241e44900d10 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 494749316 1250 494748066 494748113
    0x4012062f0409060b280219030c030206060f060a0c11130603140a0203030315060d09031e1d0613080a0f0b0a090f02121e010b011106040f08030a09 64
    0x2d0320000740191a41a030104060510812403040100075645d280d030710941030b000c0c6101c2d0301070340007030200d1034200c0c10803202500d41d00c0a0400010145e020310b41031900d0f40241e08880d100e458141c00c001c4206000001a035201008025005105000e1100c403007040d805401441e080042e032402145800c00440c0191040c01d03610079090041003e180d401c3c19040f044180140402111a23020a0303513888040c0c040d070f9640c0e0006106a225a948000311403001184400c2401500c00b6442c0280104002000320741142c1d080c920410f0f10103110f2010504150742017482c01342c2035a042d00c144180d42d03003d65030724010384900c2500400c0c400c10811140882c1c84c4600c001180781d140608008145520251141c410107040241d50b0303004ca001443d0342004c070b0360120b40b001020111030800500e000c80380c000c3c6103107102c25112034080c01c01d410350240d002c220086c2c0f506030025010b40401c503160007046800500803529600800b02050001e0041c691058005400207402006030300c43c005005d10042c1d04502d0200c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 494750566 1250 494749316 494749319
    0xc06160b01120816080c0d020a0606080c090c030901020c0a0b09070605091806130c030509060c0a05180a120b1807060c020f03034012062f04 62
    0x100d41a055004200340101040302d00c07081d9036041e80d40c2c03003108081c001003524a500074041c422140c040b98881c41d018000c40760181e42c4185d0283d141c0c0c4000005489403480d128001900c86004124441a014014007400d031036034400300b02d400c940e00094500213440d035090102000c001001c0010800c0e03503015602c92112403810210181ca07140300d940100d001c000080c0f1011000e9150310200812003501d04919412aa13951000720b4041c0c2151032251046a0400b50312190054241d48a6409218a6019221180c1d2001e9041c44581308038058035000800c100900c1ea05d40e603117004110441400206030f001d0003a44c8626440000850f45403e540c00d401100a0081420b5900002681400141e01901000c0c2c50550040c0c041d00da0701a003e400303054610a041000d40d070a00803150070f1026094039921a05e481c8002103043c1d40c1c48042d228800c0c04800f01c000b00701d075090440c402100c0701c03441440e146580980c1c40f40040c2c000381c0410000000c00a40d0300c1e1781000881030003403800e0080c000e200e0f01c96 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 494751816 1250 494750566 494750573
    0x1030c17010605100c0201121a01140c0c0d0309090903050a030b10090506070c0506120121020904080f12010b03060a0506032707030503030a0c030e010b130c020c0616 73
    0x40340c4541050503894008104902d4031140c05510840c940c07400e10500c010840d00050342e4030340c600b040c190074043ca01a0441c00c0501c0c241c40c081c0e601e280a0340d510300c10101a141c511010300c07071b041e00040b05600c60000800c080c5003000029aa151107071620824043e074480702c1d00207444803d04c00b10049840821620507603585440342c190b06120417140d00a0302e1f41202000303420800980141c40c05400006030540c24002802c0c001e0000700b001800041d521a80c12414040d1080280101a40c000c40c0d006110380030300011001c0481282c00400500484d03c0e591b91340e652540c0541c842c0c0c0c05c100d900784040554401c15143da980200b02003686940c7e00d00d420b1042003c3e0010701c0d0041841002e0510500003010210b020000d005149120110021071007808041e280003039a40c00240301d813200000300b1880043c20780003050a0b14040d00c050112146108505013a80c05101d4010f80100301e9000c82c003c030b0b00d0683c210f01014001741c01035801446080c03001c10125446001000044040c2444000c00c1 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 494753066 1250 494751816 494751839
    0xa050103140a0215130b0408061f03050613110d11150c0c0f0f090709090f0b010e10030204081509061b071104020d0c1e05031e100b0301030c 62
    0x104448200a080c02d5000c0d6800030b4036900c420300d070b600c4541002042d0807034a07546000c0c008001c2c0103448155030b00c45540f00082660b54408455882c00760903a04551115a0510030008044c4c0b98850040c0c60150355000d00340e0800d0384c0d0040180c8480540d10000b505940322a5203550101d0301034480000742d445094203000f100200c00505566500e01008005a503000100d800c00042da01180c0b105130791210f890020300f00c030401e07034081907100320054180260306800c400350b401202c041c50400d0101880207161030084074980d9003120301040b25480c003410180303404002d244101343c0700c0c240141070a0316820440c0c03401500701c0d80c000082a405081c8900824204800745e800f10380d50303280303444038410000c0501c024050010002d08110b00c610040100782d58640696910310403a1204101012006c08010001950f11208240c0f4607203c204210b01c2600c110200e81c800d1070403171000301c00c1c0c49201101010980c0000c10903451003100c0d80001c182e41c075060300158000c7d4050840c03810040d0401194665 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 494754316 1250 494753066 494753093
    0x50409050a1d031c0506150c0303090c010504030c05060702190b071b0501140a0519030603020f01110d050c010207050102160209070201051302220e01060f05030a110402210a050103 79
    0xb0b107544140510740b2042c810b11410800310000110120b0706440307138008509803112090020b60080b40109040c20007030800009144204c0180301100d4102e4040001515288581c1c0005070901144800c1070000b42841070080c400d851001e032284000f080d50148110004019400c4003003e268005280c0080c000700c18241d2b503140e405012000480d44ca854000f03880485002d80394080074101103905d24806001d2410707528000503540038003080c4010494014020401c5003c101d1003440d00c281c22000b203510070140000041c4100d8002c24045a024005031400e8000340c403121060b6400f00048800294203001030032141921a11480c0e40c40240d20400000000c000c242c1021a850441081890100c00600055154040e41d58560148100e0749406030b40010030108462181003101010103c40154031000840e1040e40c0e170701c1505903c400c00c0603161812450050401402092001c00c1841e040d40141543c4c020000411140315603a240844c60722400ca401c00282644c48004100b80040c5402018 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 494755566 1250 494754316 494754371
    0x6030c0901140d1a07020706140309061918110405010806090a021e1c020411040506031605070c060e090f131214070501020d0c030e0a080a050409050a 66
    0xc90340c10036070b11020000c80499118860341c00d50080500380310010940300c22903c440003d00c001e5107803070034000c1d40d00c0000344903134800512003002c9ca0380c03480d0307007802078074001d0409a020b041e00d911040e1780620007116810a0700445582c0755200785003010001001014a4410066450340c081000100320480c0e205910941040d000392040207809200820303013107c01981291025040300407042c1623010450607118207500020300006a20034201070b101600c58180c0700301c800748040030040703040c50700314000c40c458280c0118040c40841c203c10580c007031000071104a0f10f4a981030041c584c880c5061700c1c0c0035910200c04100d0180602401f03090407070703116070710842d4452004880d091080c07150070750a00803d00504417482d60b41401d21028441d5607005410a001d001e09a00c030580ad007000da0007544203214001d07649107020402124107001e0b000c1d1425000c54207001d8001c3c00000c0c0c07141e208aa004645410410500f04004201c0038544e00c501406400b1040c1c00040c060780716000a031a5002e5440b41c0d1 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 494756816 1250 494755566 494755579
    0x60801180f120c0b010b070624030206160512040315060b0d02160b0118050a050903040b031f0b0703020c01020a08030109021c020c060601020d17071b05010903020606030c 75
    0x80454005070940070800c2d070144074250b40d4480003404680d8910400310003810203008100005030303a0f211001400200340078000820801200d034503000c160050100d803880101056110400c05407030500041c200654642290040300040303070383c5075401c0402156040b03400142c007041c24000c1c03041c060105d9180021041080107242d041c0008400c240c0644162403500304d80010718103000101d44c111070f81000b071b4410300342e0909584514402c41c2050001900c4001c046c41c010002d2076041d2a0301070310f40644541c03c061450581001890085a0b0004001009001c1c100740e00021682c000700e841401054140d0182d0b89505440c54002d0800616443e01c0f4110761003504500b0100d41d0381800c583c1100c02d1003d0041e03403103102a070b9041c506081c0c1d50a260070144003044041910034041241c9200741d100364240e401d400c2103414113440480c02541e1060030401010001013100c0c0c09100d0540007100151900c010000e1a60344d0a802c0d074903841c03011001a08010244800741c01c08002035141000d044610 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 494758066 1250 494756816 494756861
    0xa090615050408031b0307050106080105071101060506030f092802150c06071b0b040c03020a08030a1d1f0915030e030d0c03090b10062d080601020c13060801 69
    0x3d4698034022452090030f110550300500f040d2072010000c903070318641d210000f4801166030303540c21030007080c1c1100d108002c038903031700d803600740c0c1060611500c400c1d02d4004003140d045480d20f150643c02c260008003400c005106021341000c407507003042d0b119203c114a01c0148282203070340b4418409409880701400c500c4042c280500f1810781400705056602002c0e903e095050101403a4801c5210600b184025000001400501003448260307050030058130300030354a213a040d69842200c40d90b00d100e0780345e034400050390b40220100302e09030383c03a83c0c4526214010300003250b03100c1000455900381508840324011410b11101001300d118109030301004000e040c00c04200d22f5580303900d81612842407800d0201655030b99014078407500e010b035008084183d0010b104501c140f510741004980742e0300d203008030030200d18104843d904a5801040c0040491201e0350380480032500301100790707440000540b500d030540c0145441040075442d100004030720825204c402045441ca0a0380f96400c403045c40b085240410b040800 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 494759316 1250 494758066 494758079
    0x150f090501020c13020d060f09060b0a021504021807030510150c03051b032d0702060d09031e0309060e03090a0b0a0302070606121a150d050c0a0906150504 68
    0x11090300000c070645403144c940e0701c079000c1c0c2c0000f445508502400186004c44c0403032400f201c298000d0903110945000c100c15a11082c241c419801b51117a1000142d01c0115003540341400740102e00e40251024000701e140c02c203141c46100150004868040010b5640e00802101c2040c07018030701d0042401441c914100d48100b4001070002e80c80200c06020300c4070000d5440009810340019910103003e20041e65128180000500c900f0010040b05500b900700035a4203c0040d88598122a2003a42c0284a140381404101991014001c0e1034015410702c00e1040c4900014941041814201350341503900260046c072130700d09001250035600151016a100380b060117003545907400554107075010150340c41e441c0d500f010000c502910407010010116070030908000340345d4900c64001000580718540900b461002c0780b45000c1010400c036001070310b090410181354010300b040500080154050310544801c02d0100e00410950400d03175021809803a52a0010010314051568031000490b0925155107031903d040b9 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 494760566 1250 494759316 494759323
    0x40f0b092e1805090705040e0f09071403100f0506190506030402040504050a0807081902030a0f0f12090f050f0d08060919050709050907090303020615120304150f09050102 75
    0x300700140149120070301c04058086031003900500c0010040580c1d407400e460010304a8005110b481800282c43c000309110744003d00115206640000c0140312661a00144c082c41c290550801609800b039003000317440310352141c001d401007407148000110305c90400b041404092030030100c0100340000a403105020310340c4d0f600b0403680c009030120760106290300d46051050070040ca01d50010210703040000d002c0100702041010340f00c6801a5900c0c030341e180c00380d048217907200c0c801c40920703200260000b10001160b6002e02e413401c03040c420900d41a0080c1281300d201d10b044642c803c0c42030707821200d0034400008100080190200c180458000b40c01908807414019110110240080c1c1c0b04aa005002501c7e68420400500481d605450140250b003420035000d00501c900d400780d0b500613401c050009404c0c60040031600222030381a4028002c80d940d140c0755641c40c0c180c241c0d90550004203c4412120004104054030240458405150f4040e107280c43c090044044040d500f014400800001c02c440d03a00403 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 494761816 1250 494760566 494760649
    0x20c2b0c0f14031605060601080f060d0201120609020a020106030c050f060418020706051303180513050912040b0a090608010b0a030b0102010e0d0e120615060f040f0b09 74
    0x8a50810005454001d86095004d074000700d0081c007100a001c0c4003806400604240100c00a803104103858560b400180341414045450b140c120080d8116800154854070604281c0d0900313400009005d61100300d00320503607104407030344c0005079107402c01070080c4034140d19120003c001c110342c5a80c201d580600441e8140c01140f260440c98642c01c400d5100c0105150111394240c1d03480303601004549010070810310810300001042c1c00080b0310111803d03101c0603d002c0c0209444008000b01041792020311010040d150041401d41c090150707031701c2d12002480c04405440030344901130302280c030703072600c6400242a10002d901080400002d140108010600c0c042122840045890040340a410480c0181d02614122050400c2485130910b0800c00d82e0b0311100c4242203140440b810001c220314051825620002138030700540c450503040303100c0340da403500344001c2800d00445035049061079035481d0106040103161340316003402d01000030650401c0c03410100c0c40300c2c4e048a003c0b41c2c1c174400010b280741c00e001d807910 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 494763066 1250 494761816 494761823
    0xc151e020601061103040f060c1505060312090307030206161e150218190f060302090901061b06090b0f01150905040b06070507120201030b120d050d020c2b0c0f 70
    0x340803904d100380809004031405440307068280e036129961801d000300000618034041e22014202c04082c1d014294a00071940249401001840d00410540c8030b900180d0103042c8140c0e052107154000001a11910090904a980e0004a1440c0d0f03100c2d00381a558481c545507072080e4082250451000a0442c4a110400400e00a401a200c2224100c0a8541807041d0041039000402144550840c1c49450581c000e441b09001e9141c04640da5030420f409034012441e91950002e1328200600c10320780700f542c903c01c15040740c650142c2c101450f600c4900850303815540580e40c003003042d001c0054402c4148096070050000000101e04402c80b00710041c4400035070b02403244180c3d01e4001d0310074181d580c803059895250300a0280c41040e990340200111041080034201c0c0400d0405100b4251858a00d034400316004060b006440703910064201115168490101e02d20300c0344c0c3c01d04c026160b42c2420055540c1e0a0b0350010b52210326000c02c0940b60360225210b136400200500f50303113480001850b0400e4021025030 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 494764316 1250 494763066 494763077
    0x705091f080d140a050f16020112092303091503011d0108060f090c0604080109060f020405130f09060207060c02070e0106090e04020303211e01030b010e060d0c151e02060106 76
    0x344d240382115a0711550102d42003400000c1410f20b0381c40c60780f202a800c00d9100f601c4988002e001001507909582d85850090403071090020240e015001e2141c02522924800041c0c903e01000d450001c2e506102442801100800100042c450721b61207011119892031400c4a04009601d0400002e903510001002158480c5001c004500a400c080100510f9100004c044503101e64440b45424020019500c091b5241401d207840007500740310038401c441c01c2c0c41c4045d0101187d0407000c1e185030003030403508111480495079504e150300031031214400703000118407030000422240c10155000b0301d84403c80e0450700801c4421801001402d4208681c1021aa89040c1c0c100c09555180000b038103500845241c0b0140d00d02c0040c858581c0000e4498a51080c00d000c1910701c2c0c824950001c43e52405d0003404000d00c0c000c0b14400501c030503041100e24036840b0708018501c8880010710fa039060030306005a8000712503c8402d480000c0900d81144044003801101042e00042c3c13040c821000b507407a030040c800d101c00d107c0e = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 494765566 1250 494764316 494764327
    0xd0504140109350304080a0b0f04050a17070606120204050702011109150903030f1309090b0112060f0c030606031a0d02010c0213020c0a060f050f04030806030705091f080d14 76
    0x1843c11000000d4410400c2900d44030741c1e0310103810351110342c0100100e50303041d40030b4002421300d800a224180980e4120004000e441300c25600c1105640590030486c960050510020001903458001c80d4098650025402c036108000e2041c071091b00c601420f4081964100321280702c00350041016517030301d0003088542c030740ca480d01d05081030391078450044402e0305400001868521040103c00030081001004d0a40d00b14503030319a4118104d80d502d083c0148030b5401071004100c400303144002c50203554080c00c800100181545081000c540d10450300c42e000c20307211a0100952a054890f01e0000200d000241690100210000740f005451440080c1400345010300d603415910390080024552307203110000c65032000f004500d40c0d0f941803020812205181419001ea00d2071446000b8680a0b480300c0002040030746695130103a07802400100180d4141c07003105400035032550303850350791350248400b040050740345103100381130b50110b410507085464141d02881c00c045000b607002002d04c12031104209c500742c541 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 494766816 1250 494765566 494765639
    0x92009040818060d020405010912050604030f0306081905210f0d1b030603050d03020f0d050601020f070f091107020603010605070606030b07020c0924150c0d0504140109 74
    0x1200d0080029000f00b0b000c14204c0304811907138020f001759182601c6001c80240d90391448102041d00400080007034000c0400301d00024020081402045003600b000b0902e07a80351451680703040080210140c015420b05e14000501c40306200010010b94028000d0b5521180ca1182d020300e03224aa0002d03402040004075403048528590140d09044e40308500310301014803100000f0050012800305407002d005034008541168080e00c02c5400b400d20102c0c800307043c44e074a10000c500508006103841d05500546030000c003aa503041c08010041c022446e0442d034524148189101180c249a00090b0445800c00203100541e442c00d081d01d044404900e02980d071104640707407032005055240e02c02080445240140201e4030b8011030201c100400a90740c10350280e41d4600301100120100407224003402d5203c1a0400c80d00f80540800c1d00c142d142c5c1600751800e030120100910340847c0100803000504003040500c041c031009440285070890918194041c541001c0ca20020042d000f2814000c60420b040c501c03148 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 494768066 1250 494766816 494766847
    0x140f070311060f16060e03070b0402010809160605041806050d0f1410052e3309230105032809061d0610050d15050a0920090408 56
    0xb03099241400302d880d44d412060f140105111800704444e00c0d81000032080c807581e00042650251071300140b10156586681d001550001406030400d600b0b805000703160003541c542224560010000d660f9000c1e507662074032481c9030b0040c0340413403000b64043c00c1400c00c000564400150101460700860041a82d502901e44800880000320160880e40214250042e20003601c0d03001c248a0151100d106084980110f10000041c1c4940e1a0003907401c20f0041c180300b0300100d41c015001d40d0304134038404540c802da803150384401c44d560314a07040f00045090409203c096030504120084c0428030115000010600002800900005180d000a041088600b030008201d41040d81c100c900b03012410031081071241032150103032101c00c0081c0d542c8800105d85801ca08800184148246103200c801c9400c0c1d400c0c42c08004050a140070706030b680300301015440074100000d100c1d040c0108920310000616440714034003e14551124881144003c40700170071a40301d91a1110401e80c8140c1c040c80c0c641d030700c0d2080d0441c51013 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 494769316 1250 494768066 494768077
    0x20a0f0605060d0f03020303060f090921070b24060f0d09020f04020d0b0405061008181e0601061205240303040b0d02040302040e01050606271c140f07031106 69
    0x102c107013140c4c04103258010000354011003003554001c2c0c04a83c440d041c05a80e00041d07031040d07259404600c02258081c41042c104c014804412121890306c10103488042e0a008240c03111140301c0c1d01c0c88264a10025180c48c000003d00084d201982098641e45103019180103040e1502c507426100c101b5a000c550b03580000c0c404c4010003c1c002c41d20b40101c102100000d250a21845000da442d020109500d40741030040100c4011660781e807004203651340c00203058a030342d1004621400e4070400d0802030805800380c242040c111001c0006000c550300d0010010b000d041c000100809243c906010b00640340b00840c40341041210403032081e009031600402103803451007a40d011050000011802c00e0f03a20000340c0041040781c4c001c96050101a25800300d00c2c0c22510240c07202940a04100301d020b0354036188050054180001440c002410141000407900610f0025444d02c040001c2800000400005107596078038160940020400505c0340d0010583e06d40c0e031400003a1082e1f4a2451419542d510b8500302c40 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 494770566 1250 494769316 494769323
    0x703060b0307050907030c08070e0a120c0e0403020607021b0901050907020f030c0705030c03010b062b091a1302130905120a03020421020a030b04050a02030604140d020a0f0605060d 79
    0x1150320781414000c00808000300801c000488c000c01040c90184142c5001d489000010404800246406103c43c078002610340100c40c08403a90b03c001071484407039031016100346d000b9006010f25141009000342041000303550004410311012100e500d42d2a9512102d05403202038078081ca090300c0b1448142c0c60210300004808041c803002485080040000c520b000454101350112132200c8003980c10142a651030741c1066070810000e01c80020189031881da0300c2401070044134031150008180c843d010a4524460b020780b400c6c407820b40d101d0007440740154120350000062810464010040c0e0000c2c2c3e141e40c01c5c2c2c62611740d541c1c451004a003401418081e503444400e1103151180c0d501e5035510302a0194225218910610414400c23a689441540e01e01c2035006070300409100b030190640d941c40307503505e401810540c3c040c03041500e1480142c07030402107580954000d130743e5440031200441c0c11500c2c0069524140c0c0454200900410008000c0c955030720407154046004030300f03913680601007440e1221042014 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 494771816 1250 494770566 494770579
    0x140a030e0102070219060f030608060a02070f05060703142404020306121b010906020601080715091d0906060a080604080307140703030c120504020d06110d09050f010e010903020703060b030705 84
    0x204a0240f00d45d071a541240c905032155007000e10720302d2081d821120140b20340340350358002900044c000c406a43c01014810b11401042003650b10f25201d00d0700c0d010080310804082540e441c070305080b00c103800040b550311281c18425090b0b1103480b40c2100300b23007511884011f8012500840400d01665880b12f00c02a2410031310111461120600705464802070b881c0c101c2804151109804101c5510100325036041e0b0301608000e00317049103442c81d000701a85080c0c05030703402c01060010100d101c90b14580035214950803024480501e0400700780e1a418000080d103003604c9000c015078100110400031500e50782c410b400c0249a41c8076130706d140b810b0311261440011500c44036400070302c2200b0550540d00603003001c0d2040d525034000c100c560b0044000c49500b6900079521070381c0c1e0b1590b980020340b6900318007140080305603e1030401d2800c0c6104000c0c0c40b8030000841d050b400521540800040c2441914a9241250b00a2010182c41c0d1800b940703488041c000546400d8813418a51b50030740701086014000c02029000 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 494773066 1250 494771816 494771839
    0x213060b0a0e0906030c0901210606090b040e0d140d020d050f1005100c1b1a0702180112140708060a0516020a230f1e0d140a030e01020702 61
    0x200b188160003501071054080d440880c4030b5003000941e04004040140c000d810907424100200c12003003100d40c00b45102200c9620703460002c0e50718024000140180307140030a4842c00c410401c8142c5901d103a8a106a030301c49120128110b600c5000c001d082009070142c181d48040351a1700002900c280c01e0062009410700c02403181c08440b84071403621542c030a02c0f244010341d864a0030400076030700407100040040c0d4500c0500020030549900e201c0c283c45514241c03901999038062910300c0b184192030b6810745034004564074048d41842d950413454110343d80714610840d8101800180c0c01c4180d003802070b201080744c02c1060b130000700800074200901000300444400f8689402c40c000a454100c038a809001c041140c503142681c000034001862540c001c0341d84030440341e030030b0500d03201074110300c1c00704028468004404941001805500c00704100903410041401100300220315110039106100200007041861301c00b400c2d0114281c0d2607500c0645000310fa641203902800d406400b403c00c029502007043d025 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 494774316 1250 494773066 494773087
    0x1b0f010e0d0309030b010801020a200a0606081c180611030d091b060509090f09120c0a120f09050603270109050106060e010507140f06013206070213060b 67
    0x25281c0c204da104901000c1240e8032556128247e020340c1c0040008598003900003002112000000042c1c04448030840306041c1c01c5481c0c140c19160f4075031010000b50000c0e1b525000600603541c00ba08241e83c00c0c10030110a40d2145000600d644040c45004100a40302c555810750722424000c4401d00040d490040c80074120b6410300e00320002040089101009140c180000d140d030103101a0352100300c0080c0000d00607a901d10a00d130440c90001c140c004a80181e0400c08030080c2104041c14503000104002d040c0c0c0300040ca00000f0315214014058188102e002420841c1a80580c24106a41e801d0310070b55201d481d241c151548541c505985c2c552880c000e00b0035074812950560082c1140c50141c0000d002c020342d00c183c01d541030000d843d40140006c1d020030a01000c914444a082c12480c1d00100f119020f0072500701c0c2c1824a842038001820011003070080152114000e070407200c440101250b0b001000300ca80001034814030501c40c000b4001e000402e40303003503c1000381e0303c11030003009844011b960f501c26000 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 494775566 1250 494774316 494774327
    0x9080a12111c090518040b0a06090e0a020f0103051b0708090a03060f0c1d090c040e10030c0f1d070e150405010305220201120209030106030b04050606031b0f010e0d03 73
    0x42103a000903c101c50004180c50251000620559901544032581d291078a9002c4038480080440d1281501d40783c2c00505000341d4420b041d4900768110161018030344910401040715034405161b810103040c5024032001001840d20a80c0301c1d0032400c0229900c0c54180f80503038642c026814503a50007900000e000062040710740000d6041ca5120344108169141003000381d84424040603c404440b40c0c10030b602070241840e40500380c0264511203a1070030142d440c100004001e1049030b44070b002e01c000501c01c00801117580f40440142136001c0d0030250b964205140d0245d0309913050b2080070144502000725a43d0390094481030703000d0b18090001c5807083e040e032660100b141d109116240c0041e2800c0001001e80720420080340c2d0406041407140c81e1402035400440e030840c146001c01c45083e034200b100841964003407007581b005610483e0891282e2801d4201203040c020700a10789400fa8004a0307111006010140060b0815101110114290f8400c0d0004a07100044d001506400a002c442548285900807 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 494776816 1250 494775566 494775613
    0xd0801060f030e19031e030b09010609060e131803020102180d0c05060a1218060b010e09270a06020d0b1002030409090321091209080a1211 61
    0x36100c00c107000150010403000c036800000c1400c1d041c0c0121104400c04544070002002c0c0c1e5020b032a180ca81d05442d1811031000714680500080404d40d40d01d140700341420b0450189006101d0303410f011800d186420009080c1540201000344030710004d0020001c04005c9034031210074601e0040d000c0c0f0090107189400f0b4001e40c05803204004a4072011039003c501c1c506444a05442c0d50301001030b01d0020714202c18810030b5000003090700c05200e1540c0d0240c44c450700900c16503146030441d00c1040710300015130a180088940040e50b00d810403022000030b28007034880402ca507401c0b03402d41889911910136807400c40805800018040c005001c0c0000400900c50f49402400310010740500170060b480ad1032003003110352030880a111000da0001e0208001503038140e806a04402e0081c2044d40680d10101004c0805c0c090340b880c00c2c140560342e40a05c030700b889092824651403642c00d003452403000f41004c1017144c0d501c05d0104028940800b03202c107814414803035150b15000120030350454103aa10001c6008400e40242d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 494778066 1250 494776816 494776829
    0x12030d0902120106140d03090510170609010b0909150310200403051509070f0303050c011a03071a0c01062706030309060f020705090118050f100501051b0d0801 70
    0x209001410010410300c038000071075080a05840c001440d01d4184503030942406c0701603052180e034000000e481d45a4800c2048110300076541d06081d40c403c044510340c890741c041c0c000c50280e00c100340103020a0305480121251071208960807207540d51129004002c80d401a03030550340500441c4606907545400fa000807030300c50840a45201c400da00700e202640d05006610014115602c030250721511a4802c000d01030f0003030000d20035540c1681c0c0f40d450a043d842a04e40c82100041c1c40000c81c00c1681c6801c2c4140030015006da5040071150201e1070020790303107890038000c140f0079406166602d80212040011107164004110007800060358a14a1008080b0600c010144a5184000c08070b4501074030701c58402501d6168481d403204508003401201c05104403440103056224055010815545a51509008088003200e481d10f2005a81c2d5001c11f440001d024100c90040540510400c10701c3c0e000d840f41610000e291407a00d800d2910440103400380c2c00ca25422090050b60b680d54880d81d40720121074143c03640d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 494779316 1250 494778066 494778079
    0x1205060609010804120309050a03051801080114040f022a0d020102030610030b180f180c0609010e1315090e0d0f21060e010501030c0503040b01031112030d0902 70
    0x1204014011184255184540090844030002d800215404084202ca019504e07000580f140f160f51214607200301444260301086002c542424080031817510380d04d40120a00c1c00c6031980d454002034103400302c1c4001d4018800c07629403600007164005a41614240250201c200d01ca0341c041414500c8050301c0301a40529078002c2d255104032240c014001c0b2406050041c24000c8485503040b01140204400201c1c260700c400000101341c00c1c101005080307802142014a40801428160000c80100114080d8504a60041d910700d03501c503515141900c03081502030070300030f405410900000d0701040c1a84040c212162601e501c18a42546240d1000305451554000b0070540c0c220303141050f80c4403903580a0030002907408400b07400d5140f041c001c84801146100e082d500030440000001c2c01d03540b036500446600c081d5480100300c0d030b40e030501844082c6440c41c1882c1d480c0d41415111440d4a5070140005003840110301d0200c20280c4850303010b1802c0200c00d209590f26800e5142500010300b484190581c403495 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 494780566 1250 494779316 494779321
    0x21020f18040b09010b0a2c2406090d0303050906070e0a0b090301060b0a0305040209060604030b040f06021303030810050d0b0112050309100503070905060f07110d1e0309090b060702190807061205 85
    0x240002e507880c09070818190823411110b4040c0a40702d9000c0d070079007442c2c01c80d900303124407036072030f1100c5c01602103c911a071008200da1415003030680c83c1440c002c00000030042550445101c54490110f84819191041d41040d0750f1126000428090314903980020400007001a0381614907074168829030183d4800c55107240651034003020003074071740501d0102901c00700c8268041800150848001740510f807003040c0c05800c0024040528054011660081d00800c80010400148007628000040501412603c0c01c1a072207a603110754a000030140512b58401c10202c144005010b0304005607603003520000d2021480c0049080c00400c282c0003503c00a001c541c0c0c040000c5442c0c43c0035810b031542403000c450070301e0400302140c40c0c40340d48402d0081d460317800c080f4040c02c1101007440c0054030804284003148080030a07050740380050502581d50300400c00d091504210010320fa07103020890301d0440e0120b840250492461282000c0e6040c40c0d400b508044c80345202c001540343e084044054440d002c1d45040040381d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 494781816 1250 494780566 494780639
    0x2304030527130207051615080f040308060909160f06020f0d021b060909011517070219081207020c010207090911010809030421020f18040b09010b0a 65
    0x10a5811040b64402604060035281e0300081c1d01500300e15000d6000c5801c80078250400c1b403c000d840340c1010f40041c0d200307400b100a0b1900500642d8002c05580007404070361802c1d4800400711172024104a02c84c0384000045602803070200111503803042203c640704807580e910007940d083c0c1d410520a170005402403031004c1d030205002040c1303040401c5298001d0311400c010358052400d15100a65080d170300500502580c1801e40750386000c140603001007801008030859894014019510080075020720080400400145a901060601e103042c0e9900e07840504541615141049015000d49014091b13400420041d2690b400144a05040000c0c0c00392169140c40d40d02803420386d500440040c0082c0030b441c07840d03102c1d54800c1c00099407000c0d00a054a041944584030940701c7d501141541d00301c404140c01070810b5190840403034a0030401201e03d2a0301590803403c0348202000104060441d807401400140945001e4201c12007051004110b03400700d92f210084481d9160301c0e550201840281104c115145 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 494783066 1250 494781816 494781877
    0x201230a030b0924060c01150305070e01030507030b071b03090303080105060403050303010b090a0e040606141c060903050c0d110601080d120c03020d020d0207050c031f23040305 78
    0x14106028800d0344c20030208000c943c0008050948640104c0108410800b0070070a104012403801704140b8040480d01d03504220740341c0003040d040941201c0c81c1c0001040051800948442280c5d07000c00d0102c166641e010055894644581514900c40f4070710110004041d84014801d055034483c1c0c1368031303c1c142d8849062100074025408010440d030310030401440a145443e0140900c00c1e40140100c031076949a000c00c1c00b241e01d0554080b01d0f01c80d12484144010610034440851040040c0c0704111441030001e10211000c0006401030100c980c3c5000104c14144030b8000c4400b4804201c003200c41040020f00f0040c10440c04504c0d102c524064100041050036011034150341d2035100d50b44034141000303000e000e0001407900c1c24002041c16400c21080c4c1e138100305400a0700c40c84440040050300d46045d404d0081c01c3c01c25241e4030b0361080d00032204124499107400240e1100c0c403c0300c0300c00903031080480700a801440d031281d11040f030301d042078081100701940580149001e1010300380c20090351100303000172900c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 494784172 1106 494783066 494783071
    0x11d0301020c0721120e0111161d01031208070c0506010b0c0c010207060207090b04090b0f060109170d0507030302120106021015210201230a030b09 65
    0x985000c0790040c0c0100c040c40c44180c075104903582d440008209012035064284440303c0b6017800315900c10000d40ca09034048c2c0c0110ba80214203460b5a88509000748198100030014448419055013080d00302d0741241d80c08071044d07091400718002a40c0524000f08018200203541c00c412022510400015008054690f08a40e8440340c880d80582421210102c0d40d056503c0181c0070071807541c0c00101d250441d00c00d0080012507908860009018055100c2c0140860500205001d246081c2e010700d240501c000741c035840181581c490141c1c00c00c1289040040c0f05d90080e42d201d0001601800082c05031522a00e401454002c1c10454a52403540a07003008005a0050b808120215564810444080703902e950020340035240c88112002413130b10100100041d07950405010031039001c0d0781821400000e06540c2c00b0603c42101c8030f00c10540089031314000003810b0807080030040c1030031800c490 = true := by decide +kernel

theorem cover : BRFrame.Cov 494604316 494784172 := by
  have h0 := BRFrame.cov_init 494604316
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494604316 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494604316 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494604316 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494604316 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494604316 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494604316 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494604316 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494604316 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494604316 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494604316 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494604316 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494604316 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494604316 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494604316 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494604316 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494604316 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494604316 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494604316 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494604316 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494604316 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494604316 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494604316 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494604316 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494604316 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494604316 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494604316 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494604316 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494604316 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494604316 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494604316 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494604316 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494604316 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494604316 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494604316 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494604316 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494604316 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494604316 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494604316 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494604316 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494604316 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494604316 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494604316 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494604316 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494604316 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494604316 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494604316 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494604316 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494604316 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494604316 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494604316 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494604316 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494604316 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494604316 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494604316 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494604316 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494604316 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494604316 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494604316 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494604316 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494604316 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494604316 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494604316 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494604316 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494604316 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494604316 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494604316 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494604316 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494604316 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494604316 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494604316 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494604316 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494604316 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494604316 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494604316 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494604316 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494604316 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494604316 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494604316 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494604316 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494604316 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494604316 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494604316 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494604316 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494604316 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494604316 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494604316 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494604316 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494604316 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494604316 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494604316 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494604316 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494604316 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494604316 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494604316 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494604316 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494604316 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494604316 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494604316 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494604316 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494604316 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494604316 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494604316 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494604316 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494604316 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494604316 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494604316 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494604316 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494604316 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494604316 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494604316 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494604316 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494604316 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494604316 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494604316 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494604316 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494604316 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494604316 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494604316 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494604316 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494604316 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494604316 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494604316 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494604316 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494604316 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494604316 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494604316 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494604316 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494604316 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494604316 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494604316 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494604316 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494604316 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494604316 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494604316 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494604316 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494604316 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494604316 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494604316 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494604316 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494604316 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494604316 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494604316 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494604316 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494604316 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 494604316 ≤ n) (h2 : n < 494784172) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
