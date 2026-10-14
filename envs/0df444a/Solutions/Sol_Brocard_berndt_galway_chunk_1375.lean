-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1375
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:39:13.164992+00:00
-- url     : https://prove2.me/submissions/b8e56356-64bc-40d6-bdd2-a9793879e67f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 247122302 ≤ n < 247302158 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 247123552 1250 247122302 247122307
    0x90203061003022b0f0612230f06041101080c0315040929090609030903070b0f040b1305010f0c0218040809040c02010912090605030f0604181b0b 64
    0x100000d8101040c1c01d464030105940480d100d03507500900f503950064040303255690032610180102180143c00c003e210302c64098242100000c0101150501c2581160803285c80300c5140708084a065a00c0700b5682d02c11030030311030b5540e4041081000c0c00510b020324400c208a40c8001006000034021303145c000e00d0003a00882c14006c0000b2515183e813038003a0560101c40000f00c03604180750048001030f080891002c0074070003c501c44441c1613608400ca02800200701281c0ca5595100d011030740e64800c00d50b00d1909904003100410480683d54050800c51400300e09a5042c151200d03d1303040540c010900c2c4038112581a4020412941c02c101a80210101d91130000c0340c08655030007196444d40d0400c0b0300c060201100d000101402002c0d000e88140101c000c0081c1b00d40c03190244001c0c0030344004c00081e1490100f41518129280c007420b00c09045500ea5111581950780d910b0a00c1d1499000034251608662541034030f031700c3c07140c1c981e005c5c081491088008100740b044184c1521020500360300216000c0004 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 247124802 1250 247123552 247123561
    0x30201050a3603120807120b0a090c031d030f0a08060a03051903030b03030a1d030109082d030405060423120c1009080f130506040305030c2401050616120e0a090203 72
    0x3800070082c1c9031f0071301240b08114007002c03a103009032644c0041d0030586440d820f121002d905802004914881c030340c085284c1c034401c058540c2c90340304000320501c0e0110708000000e0100e0141100c2035201d036001740281c2d0042c1c0d0300d031140b9040074100305520303200040e080e41540405405200e800c480b43e105a0045081c1030078100090880034140e000100c480008036803d041e182c0c3e09401807031070540c3c00360f0807503242c66540c00a61803041d0b49800c503079004080541603104104c01c41040d240b04a81010040c46262155103407600e19131a03194841c0700140425049144200d4100a004009000d440c4456514a400d0017054103004090b031114800c1403c224884010850030026256100790b0001919560081e55584140d402c46540c061508440042000410b00c00003002a107034200c41c400540b42c00c40a00b4055903481c565544000710b01000020041c451420824042c0a840c2c03141c8080c0c520300c82c1c0c281c03590381401008404c1003000400701c10020f40c150902352640c40060540d0700303040d0f0541c03c0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 247126052 1250 247124802 247124807
    0x190203060117010e010606030c0909020708030c0a020f1b09060306060a0b0d060906080a110108010b030703090f02041803140c0c130240030201050a3603120807 70
    0x20620a0740900c040c07914100080b460294461a91204550300810140e9603440000c0c001c0c2a00080c04000315510460004561585000f00d40c01164003030170b4030b840d55444042c65601c9070022400c0e1070851145171014000b0031300400900500304152204401c683c11402c1c10015000f1000742403e01035080308060014903129076403181c042ea4046100d20b03840c1c4000d18910170041c02707168440c1200500741003000445001c0401c10180c000d0084250040650b00080151584d0780284642c2c40c4440c801c00000707152912036400140d107070b4441c191040040c1915000a8142d412007404062694850740700c0c6003c158106e800443e0180341c04a6076803d084003844000e80351003003400524011103003000344180c0c035250365044072604c8055280d07005502c0c81211595060f614012a0480b42005411000c9040c50130398180d0021664141d440c1c41c6000104881141c0e1100099900668244041914901c0070f8000506050b40368841c50034070741161075400c0244034071070340100c0e5806101429040c000400d6 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 247127302 1250 247126052 247126063
    0x80c060c0d030c0e03071701060803070c150311070605090d020d0203070311030408061014010c0c1809060e0a060506040204030c03120504031709100f0503010501030e07090203010602010905190203 86
    0x2500d410001440b24240a0a540c4070040340c0030145d06020b07046000c2095032584e1484107203094004002c0090585130303103a90760340e8801c164002e00140d40701c04042204808001c65203104407820320780070030040700051501265820031042103a409407500104884400100b0082c06c10455501c000c0074600150000652280304800002e41044402c0403070b004100402c2086030000d1202c0c0c2e044035041d2500c880004c2a04005005000000c0d200e50800f041d01d6102e460f02d03012140d0452200006546040c0300c00000c01050b4000ca5035040d251580503020500600c23940521010110181280b2103a5103000380450340c00501071b9210328810f01c020b001040021401e04280c0340d00c800e41d44c1405804160aa80740d01850307000074000c1c9003801d070741c507031513402c0101070400c1c0c0744103a464600c480d006c104251440c030403c00c03581c000181d06000402c0f0741d61281c1c1100140310000c606a90903c3e031203601d4101a64000d03044040540e45544070682000010044031042c0340705986001111400e90b8000ad8481 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 247128552 1250 247127302 247127323
    0x60e060312030c0703090e070513061404090b030a060c050c101505040506010507060c0c0309050102031e16080706060f05090708060613050415050102060a0b0109030f081210080c060c 80
    0x140c0003160400c1014000c510341406030252131040341f003030f18114400804560021a005000700ca1440c5c00050407801104130901036920500001d080604280d00207004208102c103203035161064048145c0800c146103d00110110965101a030b11003403410961700c1c0c040340b030300000e903014a03065140c5040803c62140303000351001181d021a1680707900004030f40c64040c218024081d145065000c0501a8010400c1031300c1e18820385030b50b200c0c07075550700043e62280a01000c050480c0810301200341e04041d0740b0002c0145010100c082940400b29480e0300032240c0048004450587c0d0b40c40c0b00344403041001598000401d0f0884810310700d407800c0070b40180010320103007082d0b0180d41c000c035201104201c0c44984001400001e0001c108102d441e4150b040007001902c109400f50040101103503214105004403c0040c0040e150303621094030319a03414201062a05060710b24034800c3c030640e0310101500c0442e03801307400a80101000603090404260030403070500407281c4150000c1001555010340400c03201c1d80c4 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 247129802 1250 247128552 247128571
    0x807030507030615030c0b03090d050903030a0e1f0801090e12070f030e0405040308070806011b1b1a0310060804030909021308010216030806040507050306121f060e06031203 76
    0x40b001d41010329004c0c10025080186100141a008580d02501038085c610610040d0210b0f0454100c3c507009603650300c00c0080c46a095041000b0320303441140100d41c0901c10f00b0024112204102454210303c00d50300e071100d0340c980050b40d2513004211844450050a00202c000d002411031070a030081c0780000c1d031094031001040c1d240f110300c1c588203242c01140040a807480242050202d40740130f1a00510900b802c80b4a01d0110f0030620210305154800e0140305404038969401d40e00080080d15444145c203070681c1c00e0303c1001701003c0041600500e00d40c0c9072800000400100340c4a041541d000100340d00a50840300c10403000c103041001195029800d03030115108841c0043c0d50f60558900c441150314140c101401c95800000c000d1541040250444402170007a51100c405486600030442918030664000000400030320104001f454407144040d02d08211404645c0c003c15221060903a09065034150140c071907a44408009100a0000f1554050400c45c068030141016071100e00d414040900030408 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 247131052 1250 247129802 247129811
    0x50f150a14160f1b050a09020c0f0a0c03140d14030601031b081506030f041407092a0f120e190c08070b0a12050714070b1008070305070306 61
    0x82000701e003400c64010210b000140340140d065802c0a0350b221901c4401210003034090282400ca401d5615084c0055810080c1148009840c0c00b184001035004050601001d001d590300b092244074081200101d000c0c803c034143e050080c65414680d01c070f01144a042101070300714858078070900da0301c80070500f41425250505501d944034140101e004180b40030384c0d100c0d00e02c0e000d00c00d1140e40d90080005442031001030130b071203490803295043c00b44501051f251001c0c0d041c0d0907408140000d02014901c0f59a1300c0300000c0359101350396400d241d015a40032481605540c040c49480c0e40000a10107009114607030300e82009000d0700d0740004001e00c801300c1ca0035a00785441e0b50b50315120400205002c1455400d4440080c1c82c40703a0814201b1100703a002ca48906035040c46440784c0001d003e8001d078169640c150017519a01202020528444058403004010108009281482154200b0510007030a1428040c0340a500b05140c020a20103c14109421522043d80a1350f4208002040040c140003030741d03400440032a = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 247132302 1250 247131052 247131077
    0x2031602010c15020706050a0b0402040b0d0b0103200408011b20071a040513050405151b040b0d0e0c0d080c0c0d0f030813020105071101020705041104050f150a 70
    0x403c1546801c600b00304140c00002c100341840b4803504a54002d01c3d40f42c03c10402c9403151002c010403842244108070705000b0610414030010410b078480341c0d0b00001810049a01e80840075000f804000440901540520100301403110740700074400e0484c243c07912407400f4a40e160005010f081c2f02074042c2400c01140a040c50141558001d00a500062040041c0c010618000301100e85c080d401a0140d02c1c00f0b03107442440104550b41c0c0e03019a50045e81c0210203044200010400350701d18480082c90010344c003000205d100030320020784000f4801041c0e0914641c0c0c5907100c924106013a81c031004207286c03256000354030624a81e07a90452041031180e119501d42d5440001c03107180f50902c0b0510f034060354001403503980603051103450b60a00b40c007540300e50303035101856071001c0c0000c01015030610041d00080f428800040003c032000c5c0c442881c2c0030140100c88c00240d90300b0002e000d8039000440c6007a441404101007006043c102c041d0301001004031920714600c01c11f40084200f41c000c200200c41041080e00085 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 247133552 1250 247132302 247132313
    0x301080d03060e15120f0109020f030d051b0712061e090c06050d0b1503010515040b070201050a18060e040b090f0408070c171e030c070902030c040b070f030e0102031602010c 76
    0x4005a030145c41903035150850008400e00030301c00700340140e024429003210312801e483c000c24500020b0043d170300c0701d82c2014100382c84540c50f0100300341c640d0504d1040078401f141010f14032180041e114072807440410030b00700422100440030b02d034108006450341060720361800904405d2242c01a82c2d041d20b401a01c80d00d000c83d41c0310152030000c0c1c1c0380340c0011040180200b2107481b0002107050369015a13541710318154000022046210303e12811078555401c0c0700e00001503114030001c0000c000a0b2034841070050050030100d421240580c41100412a4074007520800d060a0046a88801c0c1c1201c2000e141c1ca0680170000000000030402442c4810000d9041c04010580004001500340c504800001d80b6108144030380c0c2d00104a4114a00b001d03e8100e85882c400c000b04450840c0c081030060141c0c03a01e00035004c006900040c03c45e44000409000c0481c0e8066a640034060b803d000712245000544c01d410701800d81c01201000710f0440d0410401071092240140112014603070a1905180a10450501d13 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 247134802 1250 247133552 247133569
    0xf0604091b11070311060918090109060605060702090402060f160506150a0b070f050102042102090115200a02040c020a02010806190e100510050301080d03060e15 71
    0x65042186050944100d103414141001c20301601034542c1d40107020150b0701c2580e158442d110091140941d80c05600c00c0d400c113440500b5500314054411038030f10710f414816003031460302101e09070840d079501c81c114014071915000c1e00d03000f0301081e51800c3c039210361500400c0d80f504004002038050030000800010a207940000c6605407009484807040c42140e503c1c1403501d500003610001c403404e403081c0c8603060134500b403000c4c0c1d0202c4440a030f542d807400c04103960b801d030b00c3c0140e1a400d90712554280300000e6074103030414520b0080d400e940f00c0600e0242d04e510400c0091401038101840c1480000144010981c0011001003080040e1141428000100d50701d20314103107081400a410500740786580c111681c0014658856500c00d80340e44104cd43c52000780300405100348104074903c44210720800921600c011041c0c0c001140c0b6884030070305511000440c0654020304040f0001a000100400000d2814804980d50045c149010300c2418074190824001000140c0345141d01c1c02680344c07181711039484010 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 247136052 1250 247134802 247134809
    0x2030f04030906050408030409110706111b0c060d0f09210306081c0c08091009080c0916030c020a020d030206180307080703051c110a0306080f03041e0e040b060a080d0903020f0604 79
    0x4c203000408151078201200c0cec0007001195114000400f20300d9542002054220b454803001d0000382c20181022000809014200c0c21141102c7e5110003010200345094035400d40c0d2249541c9034507248802031001011501aa032100c1219004171760814101025078481944822191405260200301400c004400341300d14484243c0c040c0340400c00c1d00d0002e801c10002406c4a200c0015110854014024800140801c50388a8041601440d200c031125000b94009a0000500d01c121445203810380d0200d01e007003605030001d50242c0d124200300503000d0b855552245480c010280a18100041ca945a034a00c0c000c5803002024400c0100e00611440c031455200b014000e00c1103001c2c001c006869140700d01d181d11611580c000030341403441c003140f07031500060000c104100c1031004528203498000f83c602841c40314140c0c04940c07503d082d00010075051982d80316005500400c0d10080b241409010000c009520b50700c0007085400c0100c03840700454000230780200316501581c54818060000d40007441c103104540 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 247137302 1250 247136052 247136063
    0xf0111070b0a02060105010e0102010c090303140705070e0f10060903080d0e0a0f061109010801090b22020307080f040506041515090e07051804060b0409020402030f040309060504080304091107 84
    0x200e200200e83d000a440d41250340a0701c8103090b00220000480c240e81044c2c0d0340c2c0e40400d408080800c002031044840300440b525141c402c07418036081e5aa00b07400c00d00f45078440381075400080288800d1805440c0040d070030a80c0f1850070000d5030724245004d8142e40c958400544900c001040c1c240c0107124a402c5004031036045402e84125842510b0014030a51100c4400e641c03961605005200b6455400200d64160317005071a40042a0300c1d2401101c0904410500107801c07100c80f6601300e0b084007000b402008840c1b010a005030b20f038a0901d900800069000f400740d00f0418a0fa02804003048000c01c8840e0029000000b10030021241d00c0004003402260031401c1c00d486c00081c0c0050000810380c401c000d080d442e01e0944640e1a500d0080101c640420500c4110000800307010800240c0d0701da10484004070060004500e501241d00080c049820440d03004250701c0c0c1e8101003108160340030648201401d450308205081c40d050254a503a030b40070b02d00130b038251545d41e4a004000b4104640640b0815503120 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 247138552 1250 247137302 247137307
    0x304050a0902480f070e101818031d041a010309050c090705040305060c04081c0c0c0b0904050912090d080c0a060213061e0e010e03062509050f0111070b 67
    0xf04001e0741c0d1501035144811a601420f070003c254030014941c094001c99607514a00203050500e10105102c03041076181e1071043d0380d1411440c9100360644000034419000742c88401e6190b080d08001d00c10b131000e10300314510903498030030b141c0f43c008004461f03080800420300e030006c0c0c240c01034902140303460440860240d102d040301d410418a40d500034001c0003030301d100d001a6905a04c0d0604001404d00941c01600c2680e003000300300c0b0f038140151085a1410500a160070b1103002440d0b201c401c4108201e4205210404c0005400700340b40c11316024544d00a48650020329013940100807105190041040c82441003520391101410300181c042a9451009005c0680300e04000c545800c00007944102040141c02d1032040d03000a5040c00362144130301000c00b09403002c842000c1103100700d130b504c408510031030305000a0020003d07403a2020071680e845404810038083c12035506644412029000b090102c04001b4450700601c42034860030101e41005c00d003800c00304445007844083c1d03424280d0513005180c010001 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 247139802 1250 247138552 247138687
    0x509040b0414070b090f0301090c0e040804090507090303083d050402030a2324060c0f011509090c030209130b09010c0f0c120f03110c0304050a0902 65
    0xc00c002014140d0089411b130310984029000e141c01c0e905059000b41c405100b0750300401c403940410030800e502c5031084810341d1605454000d80003c03544103448620001d90b00d8041402050341000329590800300b070714410940e904183d00d2014800d101c0364001c0003840301c500e0704c60300b80940d803400440c090320000f07005645904d0010821001042d044452115414000e101c0610106a40712410700902d07070001c08000d80700241d01072480f100d455211690300408200410240400188040c1c03012401203000800e019440900b040442006500b00394002490403c1d0040041c5c81c3d20454401c5982c141c40404055403081c0780c2d008911117110340681507424035020028018419407202e100c4494a07201c40403070783c841041c11180794800c000020006480e40d60490040c5001700d0140401d080c481c0341c0443c1c3c02d4004000d80707003141c1001400765800e91000c0b0741400a81762140441c0050703c003d1004505005003001000e110704105c4441c1c0041840c03504080f0022405040c8001000349081c4101020151 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 247141052 1250 247139802 247139819
    0x50304180e0c060304030c0803061903050105070e0a27090c030b09071a0d09050a0c080c03101104030209040620040e0f01030c0611100c020d090b03010509040b041407 73
    0x3805203410a960141500032860b5103440c4040d24040c50701aa0707107404e1054103544411150348050007455200100e41051007803005080012009584140000b00e0359040030381c400b0300780e0002c50b0001841107000b60014881c2c48049101c900841e001c036500208454143c0e2981c000818202c5c0000d0842c00c031034034001c014030040c005c5460144c100c0d5070444103016a114403040cc6900c1100c510a00100100800380001c40b0f1034003c030f420719006074192075219606998003000401a81e008031182d4001c030544483c2c2d0b103428021040c1070782100606100e52300c42c4003110040d03442907000080c80340d0b40d1b280103e814043c8a0303002c5d10300d00070700720040701004440940c1c4081e603800603c941212805034030000b8412005480d92203048070780c00111400c1d51400c1800a8400c018103849800c0d06104040d990104c0300300d94000e024000340340390081c00d42c076400745500074031a145036080700804040800c010003031034a41c141007580c881d401020300c0466464900e0080d541a0402500c00d04501c10b91401146001 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 247142302 1250 247141052 247141061
    0xa1103030c09091b03180316030f02070611031b03071707120c050a020103020309010209061308070806040506010603320f0604230c040f0b03060a0f0b03070c05030418 73
    0x2c00c01c035800f489a6656100201d00d00b0b0620034014683c071401d0000c61003000c916810f01807480151800e84c0e0421a500e014502c030101d0b039000c01e60025081408210082c2e40500440f00501303418034094000f00c8610358050790b24410007031180000889040804401842071003501c09036640501d507100540744142d0001c900ba0080c031401d6400000440d41d00380703424003810003251002da02c540038280704841c58005400a41000b0849030441d5000c01c02c1d00000e03540c1800030041014070041c400c0301c41341402022458031030341c1d42141002d40d0055080c0400700e400050030074112042c919010489403c038950080425242402c4143e0080d920b000420030143c030a80c00c21b200b010b007080044201c2c0e03502e00402044d034044a070400e4a0504065181c0c01c0d00074116105940140d4924082e85002e80e12014610003c10a9005001d400c4001c070500000e40342c460340080080c04003900001c2154202a800c10140c0b0018102d0703810301041d00f0800c41003240900540300104840700c007680344840f90302003610142 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 247143552 1250 247142302 247142317
    0x506030711011401063015090f0c1b030917030a031109010c020d0f020909070923060d0201020708010501150e030a05061807260c030601031104020a1103030c 69
    0x15403c01c01c4a41142071a40e0030a8101c84d020f42d1051140078406040c00303421180d207032114803070782038915900c00301c4d2105010b44c40c14002c0180e104c441487c68940554100c6801000141f1020b08042d41504402da00a41c08031000c0400d441c0f540d900541494140c8034411030ba481503403541e02010f207441a800010015103001030300c648080c802d1007072211084138241301c2c0c0038681e404215441e40700740250416921601c0450700c0780c3c084100c982c000d5000500914400c442ea080b07941e00001003401258420301841600c20680700286405010b215a1250b00000003410140101001d44064041d6031081010b4401450340ca00200480d503113500c0c42e141044001010f601c0415084400719801d400e0004144140e81e42003030140010f603d40c1c00041300c0a190800d0005401d205080001c91b888850891081c1d090f5420f1543c40581d10811000905040700300d41c2107842130704924010804100c4c01c4505403251041214016903c0026400030754031022850284912888007000700022880644000c1000 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 247144802 1250 247143552 247143587
    0xb0102010b01020616052a0106031b1a030a091505060330031306020d06030b010909170307020708060f01030506010b031306200d0501170102090102061501020705060307 74
    0x16450410059035500d01c10385441099130080c92040c8845840762020f841d8107c1441100554104101e0407411413080458951025940d1403004004000e2407044040ba0031402405858015240c0349000c0142462007480011011001000071400f110951000d41e0306e50303011030085401d2038001c2d0f1000c0200300c00c0f10b0250003842600c0145e020314010030780b940c0d90007550f448071940c080f614085260f950b40001c1c0c40041035840e101000c1c40000c1684c0050204070201a83c006605499800c1091803058103034040c54601c1c3c60681d0030000b24003076000c080d04c260500c14105035130b038540000480c41d01d00203502082603070003078406001108142c0c0c203a19041307a018a04a50042e41c07140040410ba2109640031035100d88110103d20000b04240c21185100084006800500c050b46140c840e4952041c0c801b550381503591001071152006100504042e82c1005000f181004103500000c2d43d280e034040d244507249401d552070036405071310030068076019180c0074140b50740702e06000f8000b91034140c25402180d003 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 247146052 1250 247144802 247144811
    0x8070c09060b0903071a090915091506071205040b0414040b060310120206120f070201150501050a0e0a09020a02060a141302210f100b04050105010915050412060b010201 74
    0x3280140a020f544040d0780c000c000d000142d2a103541517981d0003401035910b03000882442a0a620ba80e01c814080c40f80e10404221002400c40000300503c8540080c4050b1400c00800e442c4a52a100e54003520802940110440084080e04c0003e07101d41c043c985c0514140034001902081c0b44016800c0c00c600101c0c00d40d0f050164204140800245001c1140c480030307080f600000422010304a08246c0c0a02800a05440c0c64020140c0c1c0d1122225011140e80f031811032040c0c140402c0950920603858484100c0182400607030810b40020140d20502d18817008110251541d50003079950084c4003401040c0b101700c119581c55080307101a454210855001600b540b52000c203019400c421601188902c40b40344080029032903607030030400c0300342000340c0032003050b420501405840d60301008442c1c4503200b0744006180c1e4001c082c099200b52641c00a096000781d0404004120326600145028141e400d0f045605842e1580c8400840b071600590313004146016006000c231041c007040d03600580c2c0300701080e0300031300 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 247147302 1250 247146052 247146059
    0x20613050a09021204020d14030406030914011505040c031104120201180b0f16020301050906160203090f04020c03160803191a10020c090c0322032a08070c0906 70
    0x10b04902034045a40540c50000d40001d0052030014281d00d1801d01c0707685410710001c00c0d00d5042e0300d5030b00142c0050700440c4e03803251414240302c201c01415403641103e0000b031010b0860413a03511000c000d680b00ba180500e4803032016102003400fa411041c2c031a028030010f41d071905d07911031200c58144031640d4107a010480c000c0300200d005261425079010f0f41c00c5910007030b2030a06900044c21269000e044400c5d4641940c0e450000181c2c0c4c00c1c0134150007000600020007160400c1d8034090b501c0200120800d081d075000700202c02c1e4039265425041d0480e17008440058440d030400310202d00b1480b601846d18084c10041400e4010032070030001850140110b01c2e41c80c1c0c40c500258807980100d5184010300e41110302c00041042c02c92a1091501181e840c0600c103403074800403410f001c1001032909440b0001c003140d002c0104400d0f519011860404800d0345030301c400c00f800c2c1d42c0d02c028060403c0b2001031002c41c41500130039500303041d00608642d091644500c546580d0291401c2070030f01e85405000d100103803400d114001 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 247148552 1250 247147302 247147319
    0x3070306050a030b060607110618010e040212040209070215070210140105130e0106260607020703030c080307021207080901080106030536010504030513060504031518020613050a 78
    0x78070680c4d81c0500d03e4103244c2c95000801c41c441c4c006803c01c841000c07003040b85075220746420001d084001c0d07140341c11069030500341d400900100c0804c46118026031051012110f0100c0800c609a0400c0e01030340c4000313130b40d202c1c640224202204001e411001211442c02c1c048240e60000e14807500b1401100200003c094041e02944940e40078858142d108004804880117113044c0e40c01030111009000c0000b0f41c082e0354081e01c0c00c884111481c805898003040f038100c59040401e0007003591211031440504103040c10369034082c00b4000da144029144480c04400120018020042c030428040c007902d00d282ca610b580e01e0720030155804020081e0000320107c000080582c060b004050160031a00700024252402c40440aa8800704020a4018401c40c0804c442c5a00e000e00c1880e020b9400ad036502555245142d819005404803030707001c5c00401c4010030080020690581041d0508684410081464501403281c080c10390910308020f90700000002d168480c000011142034121070065030049051580c0b04601d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 247149802 1250 247148552 247148569
    0x3032503050c1b15090706082d0a090b18160501080a0c1b0b1b03090309010e2404080705010507050304060e01140412170720060d0f020307030605 64
    0x203510b0048000c0c8a0000c40041d40010720794500242c0044800c0141c440000340c0b1812800d88003051241c000240034444283d100000039032090070205520010400102d005002c2c80400c01e0f55a141301d0a080440e240c150241c201004030343d0400044070140c2001481e201c100f2410003908200703031040001046d611221040141c01321803058488403032543d181c844c03035001350a80300c80b800c0800200315a122400741b041c0e401d05a0300c0f0b0250040884901d03014180340b5201c10146e5a10008c60380600030402210300001c1180d03960802072030329482d0302058001140d40f181000170303405aa10303030031407039501001c1c49980500104c8819600300c4580541c1d0b80c0066a0a1283c01400791283e0400c0205201060184600702c545c4541850300c0c00d000000150000c10070b410517004001440c840441f00f0083c0107081c004245030984810840b460071009503201c2d640d400c5030392240c00e400b036036002110340c0c55a81c01003600e1130380006030000c0c006220f496001380002c0d0300c100c50020100786003140c0441c5e6410100003 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 247151052 1250 247149802 247149811
    0x4030905090a14070e040204090509030a021207081c0f0e0c010f090315050705120103110310020901080604050408040b0c060603060711120306033307030203280e0303250305 76
    0x1414141504d500710201d031101280c010458000c0d408102c002002d8681d80f056030702c210b140030f001e141c071801c180d84d00034181500c800e20454004410302124000c03850100485560000301084141008105008103000d40540c082013421189017080e6071006078808901410303030000076030380c4000b805010b001c00ea5145913140805800e5862610072000c2d214480e6104c682c01210f1424064208051101d4805421400f60400c95416090380f8600d6444d04040009051000040c4000d509140e0380c100020b10b00d4600900300d41c4102d0700d50f00410148819807084401070243c0c5440c01d590740162650190741c54a007526041d00071f114100000c2c0f410781c031554131f001030b501c17030a0082c00440c0355000030340380650030140285a1500030144100b8100b401d8054404400b44490345287d03624402c0c0700c1c04e0020340e100601e103905142c01003042040c412941c0404c4e2990ba64143ca8040039490902e0700303a40148a00345d0b01014030321002044c40010075050b44001b2608801200e10752400c0d0402d00110f00344c1d00240c4 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 247152302 1250 247151052 247151081
    0x3030a1d0714040f0914072103030c031b1d0405010b03040b100f03150f050610030906020405091f140102031e0c060a0b030c0a03080a140d0504030905090a 68
    0x20800d00282e40561548051028020000700b000401000000c04882d01d10b0030880b120900702c1c0706c0f030a00100030712044004041c960520b0a890407521140e41d6a0f008800b001400c141d40c960039400350b180641d20800351650060864118072000074400f4122280002d0040b910290f070b0401701071580380a0044506890215883c01d0460326103680e080d03040d035009005008a00e034104004a004a03628103000f00441c05900f85003441c95070901544111180100804032076410b02042026685401c0060207210009103400188d030442030420300001d0042e0b03007101d03074001103090a00c85c0074001c2b01250002c11064058016585940b40b5100c0c100b006c1d03044c02240960002e10908403080e400c0c40110a55a2050002d9850410510f601c10f040c0f840490302185460ba40c2c0b0032140460508010200414106507000644c00342152105503480c018440010f04000310208102c2444000c142039036800d03101e2741c0c1d09012600305454050a0071009021350340c0a181030b5400206800000d000e1200c00c2150744 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 247153552 1250 247152302 247152313
    0x6070c060e1005100b032a0732010c080f151201020702010306050613030809060705190b0601050c0319090f0905040b0f0f0a0906240f060903170a1e0203030a1d 70
    0x500005c03002080000c000b00b40c0ca00b040c003114000c55071003d806e0340588482044400040034a1544200502c27020086aa06a02d444030405030300c1c2e00100666000001d2081d800c4007550350303009111014580c02d40144c1c000060740c0100c2c0441c44150007038628503100f620284910760710b88060010354000e00d0b117a041d462840726400c00114008900500d140c01c0c014143c5441d11f5125114285040240034950700c155103650224828490925071007600040c003468a64607041c01c4604036580c1c2c2c0a1188003022003010800701e401d00764040d070000c0005001c210465410f05969100b104014a01110241d6420134144005603c207400e24036068420030f05102e81000d10340300c2220581c002c103144d1000f2914070340d440309100b50060a82c840940c85c2949000c0b210b02090510411840b07004a9620050920001120501c0042c000380c0045ca01440101129903c070902000125003d1003002d1003047c4003402228100042540400214401c1d141c081c0b003405810400c9244120f5034200c00c41501b03154006 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 247154802 1250 247153552 247153591
    0x20f10020f070209010e040b06010e100e0a03210801060806060406050903100501171005060109030b1302100504170f0d0c032307140c0306070c060e1005100b03 70
    0x85901515452100440302401c100303150b80403c8000100b0307008211a64000300402080090394412141d0140c801c0c6030038a0500600c070081464180c1d080c00c00c000f4000c0302a002c070440e40301c20505034001c6411842028812030a500401c100c14542e10a680c0010900d8001040041c06070000b01d0003101c014007500d1825192200440e0250400c545840e41343c0200b00304d6076003c50b03a40c0200d41c0a0300b0901701020700c0c4900004c10b03a00c1c2a1810b070217003e42d64144800c1005070b81c0c0080180e411a41c01c04c5521803155200070b4114409202d200c0000e50007100c004550a9155003703025100f52001202c0801e0042c2e4010b054560303c02d08141141c48580c40380c00c000115500c1200545d00c41031090515044152110503184a50420004114000b10000c20000e043c0b18400010422082e0010094080d0203608030101c1e4451000030061020b102605600000304045070340401c0088a4007026070b6503126480305a14040c0000b0344080070380001e03465003c191014280b0860303004082030386808010248 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 247156052 1250 247154802 247154833
    0xf06020307031b0f0e010e0a05040902010507051b120610090c020109080d090c0509010b030a0b010e09040c031103070e130c0f030507050a12050d14210f07020f 70
    0x425507070406488074144414200110501c01c42e0b42c0090f00c1c0d580140d0042c800007441441000348080c1080000f8190300503944641a40d8070070340c1d00560780030404018500044c0c0d140e12031554020103911510001da030240d14416600c01800c0d40440300d44007480050f003c0d0540e2490140c41c80d080c820701500e03040001c02016030110398201802d00001c00c1d002400d40704c0e11001d821608900821984441c440410080f541c040c141c05820708a61110a650601c40280d215010050802e00083d55420745440c1580c02441141401c050040500840380350514040120b00c14521084403401445801c4900300e203004204041690390386030503110302d40e84509010000c00701000041ea00160b000b034004c2295240501c1c2c01c1c0186010720000c0041516100a00448001c1544264214000316140b0303000202d000c244a48070051500d800d01c1c42d81251980c00d48030b407240d15407c004040d800390460a49142c00510700303118051128203a0322503030300c000099071203052204941034181c0010041c20048038 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 247157302 1250 247156052 247156057
    0x307060e13090c0506160c0b0703050703050a030605040203091e0102160303110708070302060f1005090609070e061b12040f150201020705031b010b1012020702031c030903021006030f0602 82
    0x180650f0b03201c04002c0c0c0e1000407800c294025452001d00380c40c0869403c040c011a0901f80000b0002c07034040301d18003000e5490081050055520080400400041e400c449521a41010300070b810000c00465903400d03d003603503941d9003075640d000190070410302d11404803444061080e610319852805000c010740d6403540d4101c00502200101c112421001d1000002207040c0b180038000251280d001402941089410030440755001041d0004031400c815080c000780d01c0b52006140c0004060b5031441c00c68480c084151104001c005003035030001c03004504003841040b000d03842414030000c1c01c02d03202a81c0c0401d0203404584600e014000401e1500c0c80200109040b0400c12181074001d440010f0030a1a140c0d10141141e00a40071600103031844605075a200342c0038803403000041d0040f5203840580c8443c41c0041c1107495480303c0150701a030701003281c80a548090069203c011a20104c0400300383e03981c6005001884625821303001071085102c0007204090f58844c10055035004121740c92150182da60f81c0c0d0195 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 247158552 1250 247157302 247157321
    0xb06040e031e07020a0806010f0905070219081903090b0103020603041a010f0510020a03020601062f0d0806030a0309030807111008070221030a020c0c0616020307060e13 74
    0xe00c070400c91002c0300109025503804100c950000c441e50750041307004124000711103401c0301000da00200010080a250103a500301100d4a8000100c0ca5994480307083e4100182415059032020b0300030444010080c243c00180001c0402c102c0d01c045800c16850110100c5400f4500142020071172030050002d07142c640d02550b03104d0302c59030600c180105500701391101e10101381d10514418031151030620443c41c1c1180045000700c1c2c14402040550400c0c4c030002d6540e02c1c117101d00e00904c00a06c030003a01002e140d00c2d18040714400c0c003054a001c0728203001e2659a51005603981c000003200d00c400300307400b4a800705484400a03010350707412100c1800c0d5102c42c3c80c40e9000900450740c0106403009060b46071030b4854200c40750304003901e504500389404000642001e9000754110800c100f002000b400c545500c0083d00d800c0900e030840161a0700c003840b44185003081d4060003d92140001c0b80803500480d2802d2442c068910079005e440741c01c1d955000503640c1007013800180f940a04540c0404502900079400721580 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 247159802 1250 247158552 247158581
    0x201170a1503060b0a06031a040c14070c1502031603030c0509040504060218030303162003160611030408030f040c09051617010501090b1321060c020a0b0604 69
    0x60150604115005407650b441282c0554860382d00311401c0c500349442500520407410f00b030005050102a1140400d45020010f02c603580c0c3da080303144814456040304ac61001d48642e250baa905a0342000c02030002540302d100012003400c01c140030418404000d4410009481180c15410b040540d815000303840481454400c22406126003e99a0390301c7c000e080c000c50281c0c800603900c0c481c0d200300c8020140b03c800890301a60003002440b0300d40d9050092840000303124500034140c40d8040020315400c642e4298090380038030001c50508040d40a400ea001581131103228104600ca405168008550004690182038604144002407801114010b800d51041c440c441c82200c054035202c111040300d106aa41520180a8000500d602ca4200480d0038844141c04401c16071580740900003403100d4010700802c1c03012000820fa50380900e03000901c120107010840c1801c0f0389100c80d40c00180203010035500a444640c1400d0000710b640c1e002203990380c07419401c2001405e655403020280b101602c4200d420a61 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 247161052 1250 247159802 247159811
    0x80a08070311070311010c0c0809010516021305221e030201090c18110906090f12010e03130b0309071e030506041401060e130303090c1e061103070201170a 68
    0xc82c40034000100820b038401c0e100c0c0c41e22800c100b440c2900b111681c41c0c03103905106e608004c2d1030110b000c0c1e00a070360a13035009223001959801444100c0000012034040290407030001c14079001181c9081d0000d6100703410010f0281081d03945e050f04440c0085d6094000340054078840f485103514804d88201d090250b00900005c100105c01c0c3c0d60700c0070b04c006650701c003403c198880c4a5105600c0d0090042100d55079003402e0581c10080b0040c0044d980c1c0c801d03e20f901d88143c4e9051031280980d1a005480303852491600002c010808809151940300e41c4008440c0e03120441c1361402140c410030038420f880c0580540c0c0001c1520a0030900110b11b2261120300001c8841d550800c0000060000c002d003a03c542e01ca4101141c01404442d000c0b800e503001031300160003203c026000c20045c1e021802c03c0e09680c44e0140360104900c1d12a082c14201141d00c2d0700400725104040e54800c0c100404401100c0483d0b50950361080c02410031190f1035180c0c01401c2000740020f0401c5115000410b60000d030a4120059080008 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 247162302 1250 247161052 247161071
    0x130e060a030b100509010603230a11030109090b06042306040f060609091a0310150f080c0108090c030d08090c12100e0718021c0c020705150403080a080703 68
    0x12a002411182c1c0c80403a003d0007024044c5040080d221801851542030074049010b802e074000b00d00c899185410405400f00000041c000b02d80c0343c00130400440c3e1110310765034958685441e98003070300516104ae14401d250b24042551f0303090510822205000080001049280442c003118001e800a08200d0344942c0f9072420803039000851003050000e10460f10b0759214541781c18000c006440f8101403116030070002030180b03e4941c0b400301c1c01b81e080034500f080000b400c256001d06919080815003200902c02038106000c41c0d00c08001a100040c4034090721101c1e801e60314403c2040c0eaa940500c030b400e0705900582400d00032140548059500720b08800d003914541200b550100e0b40b00c0e9484000403000c5c0d40000d80907003100006100d80e50a034010300000e001591300707250700912850035241c00143c0c02d550015030702e001102c0c0c3d00341803c45054022018816240320460096031441203004082c45500c00c0c10310700c00016171440854040703a9010b901039003000d4840078143e03180400145804141741d110007405 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 247163552 1250 247162302 247162313
    0x30809010e030d09051807020d050304080d0212010504050f06030330070e2b0807030507020a09051807051e010903080403081201080f07050909070e040503030f0c130e060a03 76
    0xc3d204605030340d60381003200d49400b0802080d00100c031025201540c8060030b100c01d20340c0c0031400c0c410352411810687e0b503a445500c1c01070082d11405100e500b8031803001c250350001500309046c03203040341e0f01101c080c46517032602520f106081ca0181d40541c2d06034020840400000c8900504014250122600511150460b5240a1000b07400c0380c03500000343c0039404d50780d450b180012418900410740450341d80b441c02468007107011880d03214005084000042615820140b0620440b05425805482001100e6944034044007900f41a54000807a00c6201c1110340491400036445046072402040e01d0a800207a0070584000a0703030366403d0b4100100c811010000c252090002d0008620480040e0b9940c032001c03e08584415040e00581c074a41c004011101003210001401015600100c450b00c0e40ba8896286e0545031603119400380030b00010f100c0801c03040c044048055845204a21180d01c441d6850785240200c0744203102030309400716048442400951000001c880e4802c00190a00c40d00c280c480c4c495 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 247164802 1250 247163552 247163563
    0xd06150305011e11120705070f05160303020c010e06160f0206040305100c0306060f11011b03090506100303120b041116200d0b060406050a180b0603060a030809010e03 73
    0x400040c0503001d0700401e0039107148150040c21000d02e41017030800034600c80040c0da50034060301d4a400c000e0081059010311134102422404175a11001300c90351240b1240185e50007809520007500903024044c011075055004900d4a207105100a08451801344c81100001c465454410107480440b14003c0308001a1920002803018501030303001001503140203410101550050440b1034105400d20404010013034204507007907101c0c000340c101482c141511300045170061200810b202030108d01020303947c1940e5003692003d1212802881990b405a503422325082243d1094030000f4001064844680d6800030107600010035002e00030f0000c6001580501e0140c00d40d081a0896801c20300c8183c8090204551886120103403402445080d03c00e85044000840c400c4840b0f1019040c2d1b920400015840d0303459074403420140400070014142c1d41d440e0740549904508040c0034031611407a104803c00380d40b5003d429170b44a100020f003c50704c21030075a6a00801600840c401c507040c48030b40b5401140a5400713000 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 247166052 1250 247164802 247164821
    0x4020c121315091707030f0201032a051c020a08010302190b0d1b080c031501110607030203100609140409030509150a02010c080903030103020907020703140303061e0d0615030501 78
    0x15a0044513007440084084040907140c9100e417a403200c2400c000249505a0801405409080c0010180c1c0220305072a951300c4a1105030b071200024801000c08940c1101c0606594000c118500415243e02d403601d9040f4410b621640780403c0c04180100f00614000e40c10b042c8025600340380d03c080590303034800408250000015420310320f469201070350075210b8203949041c0d42245450310306114100504020054440600b00c65100306a402c0304480c50790199840c0c103800107100017243d40070f14143e03000500a41041c9d42484e034440d020702c00024007a22403c2c2c1c40007501c400c61400d01e100440c10040200400c80c481049092060038410b041050b030310b4040300d08685402d180d03a56910043c401d0002c1c211001e46001105001d088402c2c407806030000420b81e819283e0568401a180e160100107a10f0701318968001040c4c04c400038544e07d107032100131001e90700444003039a80c44a52040702034000c0c034601c012100c4030b4101090031002c801054454109100e400d000508825800e40c030381d182d0030b007940d00381c52 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 247167302 1250 247166052 247166057
    0xb040c0b1603030e0610061103040e090f011b020d0309381f0315060b0f04030606050a0e1b09040e0f0c180705280806010e04020c121315 60
    0x12070302014543c00d40291007111000e4030150074586441d40d401a0a41c00c0c501400c010010808480f0880c1c079030406c01c0b01c01400302501440181d10302594203036a1040c1c89540607206500305600c50040010181001c0029505030300501054184110210000c2a510b4001c4d200a401c0c0f400a030030307008428061041d100e0781208410400c0c5040f101c088141c0002030034a8524a0318103440f1a555414024100103580e4040f031648002035510341c1840240903660031810b4548400a86000c2c13142c03844000300102c0340709400034171680c0e940350100040d90317005e4442c0d80208180200000c2d030701c200c801c070030281a0203049001ba00f81991a00400c0490381016010312031a0b20081d00415684001c0110314060036007114101d07102c281030617a011f54a080640000180315001c0b400d07a2100008032403008207040d50041d07103000fa0080b00e100404181c4107a542e07901080f0705c60703100880740c2000e000711003510b10103500412858014035044803c9900000c9000c14420b48514049042910903a81c0c5c04c0620165 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 247168552 1250 247167302 247167337
    0xa030b010605070c0b040513090804083a0509040207061d0a03030b0603010b07020603040501021608070201030b0f0105091c05070b0408101b0804020f03120406030b0102060f040b040c0b 81
    0x81c81c00138a8203016800c41ca02c0008140020009a40da28200814034003c01c040800c038510b40c1d00d0f220341c480c09160003000c198040e5903403144004034080c009240c451034070445d00d0414080c180d4000c070040180101c810002d042000b035401d242c2000c0e0024110b0710303c2044d00090307001403055904090229001080315603003141441e10306042c2d1502411400c00c008a40c04c41c55945000d0320440c4a11071200002e010740c6012000800b4003900f903041c1c6101503030004420385a58101e280c81c000f942e00103441203020916102c294511428014400e0109220617100d9074945542d400802c881140040c5102d0b203c10759020f290400982c0612105004003454504151124140301455040c00c108400401655103070a1081c08825400d44c030b450044915814411000e480d24008640003200303244109401d441030700404500f011a030380040040310700f103a80c20800100060300480c1c903040161901c0d40c074000000f0104001c20800074905821500c42c2c000b12407915a1412030643c4c54010010380b21000200 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 247169802 1250 247168552 247168567
    0x40c020c01030b0306130605091c0207061704020d060203190e06040311150412140a0801030209130b041205091e0a0512030d0f0b03030705100f02040815060a030b010605 74
    0x501803c02c00c403808401810051829100354410700b000a400907210a403501c004c20030600707040c4181100001d0025000440300b80c070310300180d0b40790350500c01c1000051444080300300d0541b00f40d42c041d0241d5802480c0c1400071015031103070b101a4001a00d21643c00b1400e85000c1c000807010700c81c0f4007541e186e91019009500c0c2c58103000d0700480d039003404c20403290032100401440025400d5a00d9201c1e500c142c5070150b84180c40005ca0340c0070200843c0164010002400c412074981040380c0302d0480b44201c0d50245c3c40d54405000400c0702500f0100103040d8009600400c00003403121290b01a01c003107500d0b0081c1014403c0000400c06130000070080c0082c095000c41e40220305040140c10040c0406a82008800c42c00c0c001003a600c1c854008010805039036685075214071110303a0002c045403500241142c1d00d801ca07a0414039150450f44070700102ca01d1900e41040741c0c004a0f40241c50071503070b14501074952415580d034441c58818009201ca58001c00940c0003200042c441001c15010384003950b1220f885994 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 247171052 1250 247169802 247169807
    0xf090c050f01110307060c17010303032c1207020402250b09011b0f0c020a06030e07080106050105040b0a05040807090b190305060714070506010603090203150103021c080702040c020c01 81
    0x2101a00c0c0c104020fa110300151004004112a40d00750300620019003460104011900910407075245211007504400010a0592640041201212902c2105040f048602d039240340c401849440d0724158000180d00fa06c1c21f2401400b0344207260000c2d0026142003402c00700390400b000c8044080e000c200c4540c0001d01445155210b5a81c001003400c000c0280002c403541c07404201421340c1d120410002019850410b0340d10459128800a902030864602c03581c5401c07024028003100c1500030b1180c820808009078a05050280d68111101a1030700392806040003980701f400e41c447d590070800d01800700400a4181c3e030030072580004106031840003440b4069002001444044050f15171710f00141d00c40c081c4085003021507425000600c904000c01c031140042e0801540303009502d0040c03c10300400c00001141d54045d04968107842c421002d40da4410385509c1c1e0b40f14804402c2c0406074005030340240026080620204144400d40242c04c414100b64050b4001415207003240c0c0e0f404010781060b0310740a403d58 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 247172302 1250 247171052 247171069
    0x706030203011a092202030703142a07050d0f09050603100e0a0e01020c0c0306010602061b0706060905100e090c06070822060503091c020615040f090c05 67
    0x41619040d85194505410401d8824600511410035100021070010315902d0768155008900340c000402c0201da0040ca28000942044030800c010038146815800c01000055019108400a0107550840380341030915240d88416002ca1440e6103104001080100f001001448402000380d40c400c9a820800750005004413440e5110502400e401d1092120701290070010750281e0f440601280b42e140e960142c0c1c44c001e801212a00d94455200003007580800380046420071700307200c1c181c04668030f03640e0740d110890351800202c900c240040507080000804041600040141034003a10020a100791166507460480d42e00b610981849000100200100c0b480805060750001d02c08001e010421618008a8224841c40320028000c83c030005041c59405a081c0d00c156120340000034491480307441e207002030410792081ea2403001620400d20303408244040c020522143c0c00056000d0201e60b110742034614201d4900e840c559074059102c0010101081c00c5100e402c2030039024625070400140f51100303024458 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 247173552 1250 247172302 247172309
    0x709151404091119090b0111151005040f020a03050604020f04061206090504200d0c0b030907090c09062003160c1206140601090f051302130f060207 65
    0x4200100812050380ca041140344110300503a0046404601450241c4035609401035055001c842518945030310310a520302c581c2a182e10307160402c101c145120041d41c582c40e900c0c0d130075080e0340c0c040340c141c020b41702500c030301e607500840010040000e2075100c000042c01c1c0e40e41c005242000690214440e50100d0741030107540d07000b600030380c1d04610700102e216040b40d85100b140a05c40a0002d5111420305200640d8040f400500350820100843d080c68a004000c05011101d0390031103540304c80481585140024031490040c0d44a040c40044a190010b038001c3d80c0c00007004081d807800f5000b0001607000560141c0304240f452565505045800c2c110041c00c1d8a24941c0070b080d085910640c040000720b000001c41301c40350b0200c40c04d400301301342900d002c0300c030902150482001d2014110700142046103940010940322060f051001c625503405004480842803441450340e01610140c08021904241e08186c7c04070444001c054640041810641d1000070164003640007034505141c208502035041c000103015 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 247174802 1250 247173552 247173581
    0x8033106021011091f180b03060d1505010312091a120903040308040602150924060a091a040c0206070504150e0910150e0d0b18030c0709 60
    0x5820308100a40d80e142e000780c180665030391401d80500204001d001d03a490a40003e080344a0074480c0c1c418059520003400c400d4001c110484205890196642110010f58400300281030442d41c0c0e42c000c205c44086501d40580d54007840200c01c1d08074036254041e04e03002c0d600030b0860901000c51050010003001603580002a00300d83c1c00c0042d400c0317807840411601c003205070001c40041d80d1a00b0190034254801d41d4402801d510f00081e0001d5219004a0b1400070f12072101a40020f6a071003491050311024a04114050780040c1d0399150300064085100a8005801602d050001500c91070f01c50100e0b48044c80340400c2c00e0404110109902e05401480d544220a10150046041c411070241c0240a140280e214645080c507200d141d403407003022140f503555002802c00b460f500f061044410000000d0080a220b406103100240c07145000c0c1000360b5241d80c0207031506c007030f01d6060b85907144031007001703008007100859400400040c1c884c104050310180f60940082c00c6c0162070100c181c02207071100c4042000 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 247176052 1250 247174802 247174897
    0x109020906030a15170c03060c0408030304021306120305030a1503020108010b0313081c0606020c011403130204050705180a0315020d06050303040b07140a0f02190803 73
    0x103035121035060301e4101041090100f0074203502e000f4910302c0c600d2074000324803003440301940546410001602c0000c821702078065410a84130a401c0d441035101d00d0199003a0b070780c802c002040050800c0b44420010340017401c000191310f40c80f104554920780e00308005130700080010050107080240e91141019130b94030341408a10301840e540c0007810010b070500c100d00342650f001c40040e40502c001b00252040b00e60040310b466941c21003200d0016081c2c41a031600f0441c0d49422004202c8900001c1c0c01b02c05054140c440c0141401111400f00040d40020200400f40814010030300050f1105c0c040e02b03000301680c0c0c59540d141c050790040c10315089408042144201c00c814410800710300000030305169007544e52400350303458400e0101040a0151a48501e405100018000400c0110907010b805014415800b0140642c05114010754590080c50064032000d0b50042d08001441d0000740d11200300e115110400c0c40700c0d0b50b40c40315400d54012042261700352082e078030480d48201e031481035004610b480129000 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 247177302 1250 247176052 247176067
    0x80d0e0904020d08030a18030804030206100303081b190201060e0a090305070b070c0c0609090c02120a030221010303030f0501080a050a030809010603050a0c14090912070c030f0b0f010902 82
    0x101c1c203c407000006420344c80000b002c41c0d0080313019044458600c0201c50ba180140c0c01616000301401406c807030641c014000c6001250141008030910400c503605035076650361980300d59034541c010b01392921200d0106402008104072040c954902100001015000040c1992814000d04d681c42c8004080c5084646042c602c50001398005040d60101600304410b6000395882d80f0042c3c900c0703005000c0180044900303036070000320254004045801d942140c1c50030f1040307100090f400d83c0d030b54890480c2c00341210307070a000c6c4010481c800e074050314850291042801c821008400910160b000030303042640000c1e00c601d00402010b003540229801000e550008042e00c80894450b180c5410340c2d00310040c2044004c2c000b01e2002c8000b5001880695048011f0ba10300c8155890301c1c02d04603d803407280c20b9201c02442d00b07000443c900204868031601c08000904080840150040c0a0380e00480085880400380c100210120798241c2c181c00085120798404101401c103c0b2045468400507400070124500400109 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 247178552 1250 247177302 247177309
    0xa090f1b0207150306090e0a050d0c02010c0f03021c050a090501140901030b030c1302090a0501080f01060f1b0f0c08010513061a090403080a0b030304031a07020f07080d0e090402 78
    0x100704545543d560342d841c501d80418220082d2845a028050382807c145001d080c0c5030700418529402403007401150702158082d102a41d2103106500c020380803414010318117002c41c2ca500c0307040e01c0740e520030b01c1a1511481000e00c45203586800300054000030f5004120445407580081142000d08ac00f4240104a107000d442c1c410410310038102c00c54100354507400e826001c1e40701040050440c550040c00d82981803091300040001350480c2864a00c90039841d540062154040c004042c09011005481e1500d682800c0055503d40d540881100410403140a21002c0d603174188642c00b80d151103030900240d403003081d0510440d0070030725070031005441e4500f000303200200d448044186070a0350f002e180424454191000f25880394450209141c201074514104400c05900c880c010b1b2050300e408500304010311881e010b07d036890146001c000d0030b20448510580e40c20300788104e041d90080c02c1d8070407034000351000ca182504011041e406070100d0b0348404c4c19061102c1d002031340c0b80034001081d50407000714601a00003 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 247179802 1250 247178552 247178563
    0x10611150a0c1e1206090204261005010f0503060a060b1603020a02030d0c051b03060402041a0312030717090c040203040312140402010807030231050a090f1b02 70
    0x40d101c0303a640c1e008920b800c207006a5402e0f41d0709502c0341c0d004a5a02c19854050415401d0401c10300d0007914101c0003080340c26152083d1010780740690426070050840701c19050b051307007031243d0214851052440348542c000c454080da0740600700c101000d4211b80c5c60300c0d09162800c18042e109024040c28080280f18032280c6c07005989003540ca50002d00084041414142d0415460000c0170307406000da00c1e441a4520f42204072801305d030340328408a644218004c0c40b82c040b0b911034205c1d165455003208002c54094585038204600c0492804003000d141d24203980001d01c0c142c000105c414002c0c02c080200302c0815002004070000c90840c41c0700029614111113240d46070010007034050b10a55000c00820245481114484481000d001c170801c149020307a003840d420a80202c400300d00052411340014801c51080c000d9480c158000354070503604205030741e4215060124100e029146000e000800103159039411f21901c004d1120300400100303480c919210034140c80c0c0c4011007210101403503032441c00e5140c0c00541d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 247181052 1250 247179802 247179811
    0x18030613030807140d150501050703092903090109061a010909020f04080a030903110607030e090601120f05010503010e06060105070308090c0d030806030d110d0509130203070801061115 81
    0x300000583d403105400e6a400c480348400d00303000d84000c150f012146200d54002c05055100c040c0c0907942a5036072004640c107215865005000418004e020000f854103100d9292401400002e0071000768111420300c0d54130740040310030000a80d1034980c00024000c45124010041c1c900c0945030000700360301c0001070080c461512541403241d81c0062040380c03140014003038601418203001910310300c4500b410001c00070709850000765040007041603d05210301c2c1c080c007200c4016601d5103d02e5120100304c410030030311740c0c2c0041640e81404562690504c25a20364440d51451030b10200300010154180001e15085901d04403001409138021030900001da82c100082d140a5903052408031a10b55032035241905014007080140c3e0004c500032544020150480c0d90144a10403d4044442240c20f50b5403c90740f00c05034002450541c0c0044282002d601c0c4070f00002c0500e900d018107040150402a2000812603208880c06000500200d00603c0740580c003170021140507000c80028401240604a60a441d00002e030 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 247182302 1250 247181052 247181057
    0x12050c150f16080c07031b0f0501081f090203010f090b0301360f06020703180b1b010b0a08160801050f070807020c0901140301180b0402040c170c1803061303 69
    0x150b0750308104922089800002c0107205541d10b5654919002401c580310300c2e503c40c10b250010b00042020741040c00e800c2c0860790141d440d00f1194462000071180141840110200308007074042c0440ea10700325000860080880e00c4c0b00c0649903152001c003030b0440d8142c991692107a410f001e0306011800f444080415996840b00e64a90341501a080c01d800c0c03044540001400800c20b26840010300c03142d81e028040449c0242c0b16500080f04403142d0090107540d038010745800031000d000c4068200e0500d051503108846620000032944440000a1860005030b40050080d80c40b50b02003402a1600c0c500e84401002164000d02440c1040c520101c21210014003050800042e040000c0110307108100008108102406c01030f43d6503190011100c0a0315600c51081c065030078221264003070a46e130380e00310981c070790005c03004c000e01d03141c44d400c00c00a41064141c0e00704000f903d520b500d40b640b143d1000c1034041c1038101c040982d20010000682d8988203400d0f6514444d42081c41003101c205000d80c2c05e00c56090340f62 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 247183552 1250 247182302 247182337
    0x3020f040b13060b07030915080408031509010902090a0b0f0904090804090504031e02150f130510020703080c03010305030702040b0103022a0c030106060909090c12050c150f 76
    0x501c046107100c1800342e1921101800c0c04000108003050300f0007080c48038041c1da04c01190644a00545038100072242080d0005842140000c01060700134014540284d11f200c42d040401180e6000101104003c0c2c0211008560004401c5400e18180010000804444284038148400c0081d444094002da50040d8081c0d038850f41ea00c0d080040c0d0b581160040c0c2500b081c04c1000d4101418001d29420050104003c0e40c440705c00107a0041d0700001c4c1020903803481c10000816690307400503800c110000030f040c02c1003440c03044181900040c41440345010700f40d44100010f0302c0381c03318213008000303640150041e04520000c100500c04a03102000710313841150141c40102e0304801140c0124000c1c07103259110a5018807403000f1100521208110054520342c5208030b404480d4207034100340c00c0346d18912500021804803401001401b10603004038640c0e5000b06d06440a00d0b03960030950790071144a0004941d070343c2009110301c1e82450106140e08201441c0140e5030704081e013000595181d88102c075a11000070580 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 247184802 1250 247183552 247183571
    0x809030403032303070c0501050703110f0d0b030f06040506070815060304032001021b16030308040f0f0b060306070f08060d0c03050f1e01151701021306050a0f030603020f04 76
    0x102411a0f03540c1d080c034a900d0781e0300c1c03401e880e00400003641c500b4220b426508190104544900c2805500c40006241845614000c0b103102902c01d16800001495a490b88507100003160707580900940303081c034010102800661410f850007500b011001000801400650b0301406074690164140d01900041600c80d85e0b56511a4142a5010b40703c5024140312541030030704020740003206401800710310300314a031142007101210a045440f1030325480080710400e2001c07010800b2902c210710480c2c2150046403c0c6484030895114042c3c1c505042c0c00c151104c04401042c40401d0a040060030f034081c045162400340c201110740014056840585080d108200c40349011007400181540e0078001c2d5800000c85040942404000d174954001c8040c08868440580382810030f82810f00980d100c0b12035000850303001e28201406c3d000c1d519040c9a40380903d41d4248101e99001514243d548081c0c845070b1185511800c01400041804000c001030908040c1010010401a103070001c000d82d503000101c5000c0f520015 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 247186052 1250 247184802 247184837
    0x9050f060405070e2a131208032a0d020703090e06100311090612070e060711010c030e1e09180309060c01090b010b04090b0405160809010605030a05070503010c080903040303 76
    0x42c03005003c035020300030034071303c04800d075424006d2203058415007040307010301c0d60384003030000c0c01c015890040c00c214402c00000312107030440d0482c60180c020000f00600034840d010030b0700805401c400c200d112096030010f101c40901d60006051401401401254418ce10700a40410b119010050303c1d00240f5807500e4100d440c880350340041d2034860034003400c1b040c1c88462142003118410030070348444001c155000d4040c8403e08016088400d000d4000c2c00c508403103000c000045805151855040c4d040010307502400c112030341c4500c41114410303148881c0c10b45040c5240204001d0020140010b42c1a18004542c962103200210035595048400c45415840303009040a2034054810ba960003044000d04c1300010030000c84800140068413048601000380013418024001251025250400500310071028140e816100c0c00b0095400030070034001042c01551038000c28500b1518510807a0309070083c40007401541002d1180c42c40c85038440c94840d01d1418440c0071651284101d01014040004103105940c0500c1d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 247187302 1250 247186052 247186081
    0x15050405240411040902030a12020102040f030b06010206061009052403070504090507030603020108130f15021b03045001180b090d06060b0d09050f060405070e 70
    0x1400c0203800c1c880066050680651580111001c44041100b00541902da040c07501c113540446078040c0042070340b5900740d15080344610202c1c00d00e10840d034007000081031662080070b01e1001188212400443c03820428000790808000510960217401c00ca07072038000d800d074010307240022550107840d0201740d1140390f07090525461070355040e0340e013031030000052203048c9030702030f004104803800403504001c26200e408003107003a83c404c2d11010307000801c514049108480320114a074030252040c11142042d503000c2ea1842a80300c000c1c180c1d150341c0cac1e034042071114100c105001d00b1004c0580080c051450942040d00c2244681e950700702d40803602106120501c032500350381510003078140600b1202603401181d0242009c0540c0d003400041e0009103d42024001c0020b00c03000c94003540c4107c041503040210359030600c00e0442c0c15032001d0303414903140d100000d0f052080704000d102c0341320038a00c0411507a489040052502c40410001581c42e80b0440c100b0012031000b0404400307441d2000d942c540744c0e440f840614407220 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 247188552 1250 247187302 247187323
    0x1202070c0e09150c070302060a0203070302070f0309051302040b0a0c03022401210c05010305070203071e14120403060906230106020d021501050613030c0605090f0d15050405 76
    0x84000d072040c09070071800091420003401d2a4001860180c2e1000310341c09181c050300300002c0140e070200b004034407003000c41d801541d07110a103071400609140854641c55102d045c003000c1136001c44c1144506008505102c5d040d00620b40c000b01049d0325051900c940d0841c0c0b0710038003003050200481040d22000b05031003440410110303448261009603842040260764800f05c030a00c80e03844d004a05000ca01400c40e03100000d0710341650070000e0074402900d09001900070b050024028402c6000c104800800aa101c06000300b40440b90100e601041149103801c1386c4800c844d00142c001c55026440c1542c902846200b1141076170ba001d403010074502d00c58030f080c03805042c811043c86610040018205101c62046010604840c1076a08480c1c1b4001c0301d80d01a611800c01a4110502a0411005005030308060000700501d03607003925480c816940c0d03519042c15540f090780000000800000c0e0700c803030b03610b000310100c0016803080319018220003d031b68481540d201503c1c41811130036141c10000e0240034003803156003140c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 247189802 1250 247188552 247188569
    0x403020a23090903040f061115040804050a08061501140f0702190806040b070906020d14040902130f060206010b0403020108090f0f0c0301050f06030a0201050c010e030a0f0e040c1202070c 82
    0xf4108500c0041c1c0700c0d0014011010248151000000c140388551420005030081c540603110300d1584087d4000702c080020f10503201c072482000002516110700000000820108005d0081030070411680d0411841c0c10030003a04200007203c08018840290080340d05081c010081103a8407d642d2001c41c07103001c1e54141114a20310300401c0080c01c000d011036014416403080b5041c00b525500d03030b407090b903c070641c80c0241c1c001640920540d910540c040c0e28140c030500d10440c0c003c0d00301541d07814003409a034030403078803115801c01d0000b0403c2101190090080944441c0c00909081e605050034016039004900c03019040043c607202150140f40103000003030100c00c03101c056039008440d01c20030b40d0380d4900c2c2c0c40041c0d0181d032070710b40003607095021981c070107020761402800340051480540045403076400c05c020f909500d540e101c414a1000804000078044030340c4946410780c030521005c4c07000c0c004950240b07449005a007032104030308200381d104205c5614440e584000589416003410b111000c0005600481c01 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 247191052 1250 247189802 247189819
    0xa081807091103010510031a0607060906020a090e1806070305070c0f0b010f080a0b070e0a090603030c0204060e151003020d050103060e0601060c1721041406010603020403020a23 78
    0x40490090340158103131081501c0d01c046d0120803403421401c440c1260402c01001003404030781901882d01d04000c0560794010a40803600200b6512010200d902c2840039038041034028000b0491444040035040e03021012424603a0b8510740c0c900d0340741d20391f0f80c0240340600b007543c0c4000040345640168290202542c02c1071100d20155220302e00f80201c040c0a01800d00c0c20300041c5c00001c1c040600103402403005030b00c640010156201ca42c2c0698011800c24030441d0312640421003c25042814429400114003d83d15007017203922a005000403507140e60412003107c1d181a007042108080d48201152100003624020184208038804500074021203050000e082c1c2444000414894103802804018400006440311643c8c1c818003070ba14400350300d00041c06c100d40400d8102c4050f000e00301600c16005144003241000d0711404c4c1c1203d42e140110380c2118140000340c201501001d040106d9805812a400c00318034040c19500080c0d0045820701c43d1000c001c00454104800f91501000041e070160003a01509 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 247192302 1250 247191052 247191071
    0x3111c0c03142d0f040315060b03040605040b1602060f0c0408070e0a0e0303010f1404060b0408010f3c020d180501050a02071e0507050619090b0a08180709 68
    0x1680c07403002c08a060405a521010321940d4146101104d40080f480c0900d0340c40c3c03a1941da503941042500403541c15200ba940c1c0d07400a2043c100400561099100d1140000c80b407a0070311308550346040251459141707080d072403218030005400241c500d400c0100c00420403440e40d90703680007510074860303608a05890700404900003002c0107240059401801454024000728010358020b40c3d490000340700348246070360104800c000350046041e00d402810805480400c445803600c80990b02c1d0b030701952200485a560784800d04a0140340d11480d4500c105210030010703010b2404c0c0000071361080b4206041100026284036290303542c45a0f0449034080c0300000c09008001e0740d02203d074850510355406075425404d25000800c29403d0b0720842d0411540011600d40c1480b960b040d04100042c5904125517a21904c00d003c55a03584203005001500f4a800c400303141c07049142c40081c071445142e440300c804045c00b40035000099030405805c5500151080100214111403400b0500d041c2a95020515843c034004110 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 247193552 1250 247192302 247192327
    0x1090f060b07260c0a0b0a090b27060f0403030e0d080a180b040b06150a0c08090102030702030604061a0420090a150807030b060a020a11030a06050903040303111c0c0314 74
    0x11030707515014903904181980c410902c01d050308d0000000400c1550040001910307202050603a4111000c05d101d0f0701c07040e841d9048403620380301040c1c4000c005101440c08101c20981e050041e041091216000381170480c0103d00c0c054144a0040c00c5031000a40b10710880010004880100640305c1d0046598862410700e030400e4908191f0690b00340740185000c142404148010b0000c560f4505525070741d441000096498064580d0002c01419045000400444000d41d60402100340200d003d40ba00080191180d4228900944840d00060141c0c0c2468080da1420352038240c02890440300080c81907803a4000c0000502c17114050f00060480005480f60501c0d0310760101c0c0c100d01c03810040d01d040211011000401465000300030a00005034059000400001c070a00e108040042014044034078501071641d40c44191030003101c9080d00d80e03101060400c14107074000745d259040110720010f0405042c5000000c444409071051800501c03170100030070002c241c442c010501c1400005d504c0c9588501d00002d88 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 247194802 1250 247193552 247193563
    0xc1403060f0303160212030301080c061b010f0e010b0a03021c060b100806010801051c031119061a0f0108040b0c07080315031501060c030e19080601090f060b07260c 72
    0x59001d0a20403481e0b0180301b800208403810303902c1140013451003440410030000294400d40468a10082030070315842102002d000300c800001c4070480c0032422001600c00c0c1408c50301056101c0340316032801d003020000341c0c44400803400150424070668000c102a41040b2000e03280011030150801d0025250001d002d51180c03800e80074640903078a0118507682c61080041ca0800c0b00340403c000a20241d035840082e005803800010070860341c06903400c18150f1201d80e6041da84804091340c8994580100003141d014408080f8032003081101e1008008102c4030000b04444c02c001c00c010a4a1610743c01b068442c2c0c0d000056580f0203501090f0b490f40c9140c24800040f8842c03520546900902c01e060424512484d0342181a058035040d9031030120f00b05090b14200c400d540c042019035046045220300c80b590031071301429030700582094002000b065140400d1402190749201c0c908502c40c0c03034820140440388420f0b003100c0404e500710452000c1450b14403200c1d0500c440c41182540b1001001401c03500e00c4101066 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 247196052 1250 247194802 247194847
    0x61309050a091101080702100c020c090c040e011a09030318090609040201080c16020a030b010e090604030906050a0219050c0a0509040b0a1d01020406020106090608010c1403060f0303 80
    0x4103000e251241829031080d500410401440340700c4444000c03000d035200b042015800390062040f5080c0014078680319044452940c417101c0103030000b003040d40c403d00b4000501900883c1102031103252501d04440001c294a040c0101325400b1055040ca203241c464000540d43c4107103005090307e0342c07040a54500ca48446144098501500794040020700ca450a00078543c41103030103271140c1c51940d032840c221800c6030b400328038480c03c1c84544250318005070b00e805210f04080c520031040500a0350401085144100000b84144400c0e0300010800c80042d6000281d43d00b01d4800d400c140e5100c0304014026400d013141c90720101280a01251b0300b07801e0002c005442e0140d60b90541d8020340c655240c0051080c07044007140e0243c40802c4000125680d0003031a031010701410260040f485850010300c03285404d990065000d00010f0703440e88000e000610b201e10075007004010707410082021280090b0064480c2c0a0049600840000800014010b48458841e0080303444001c0c00d4903550304010b1200d00d1520364004 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 247197302 1250 247196052 247196069
    0x80a0302041508090c01050d090b010b030708100f050904031101050403120c0201150b0c0129010206220b09010b03150a06060507020d0609050a080412120212091903020613 75
    0x8184460031070183e244070f07020300c00410280401d010708500540317141c0e11a400740d148195585800b1004500c2d0000014041c0030501c0405942e8101804003c003180d001401d8144880c0b6101c0041142000e1501868100d80e400d513600d00059440e07044c140d40e081d6010242418039400c08082104141d8440409010342540d80c4040101b61040c0100300d08840103600c0e0300c91100701804050121b1103d220142001e44141c2001050400c03420443d40090610018011012080c003004940740f50f030144a0a41d200c00380800c0e0300e40d441781c80354612868181c0c5d030b100504803850b01c001041c003454080d000a1641f203000740855000082d01c03142c600102000305c80785848a8604000428854451000c44129680040038401600d505803920342c01850ba0300b404841c9807003444016030010784000301800040c10464140c440714400c5050809a001007200742c0f104641050801401d121140c1d800c1d0703540300728140c400c00c2e8154112130312010301062541010751700000c04610304034464102c0ca0050255010030 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 247198552 1250 247197302 247197329
    0x90309040509120d0f0204052101050703180f14070605071a010605040b130e0411040b0f0108010620101e0b0108011a121504180c030816080a030204 65
    0xb400d454890100491800301d9410400c030031991096203411010304000701d007000518180d0340e400001d092800300f4501301c00320254201c0b562030a10081c811150b2020743c60506010410340e44094440503084135100502142e5192004c00610184200340310320300c410369084854181d02d81001030141e8004d804204c1d400c044444410010242044001d41200c0701c6803203290916052010901041c1c00080800300c1c00f440c03010001420f099000c010f107004a02072012030314010741040501090f5400404a5802112903000b91102640d0001070241120b02074508042900c50b6441c40040003d5105caa5004074802c4202601e400481640803020b254199011003816020803a0100c0c1039800000c0158007062480004200703045001c0b2514001804950489191904580040c1c4000009444104013081031a900c100075041c184988580c0484000001030b6003085651500c0b11480c550100524807003020464000c0c0c070002d040e0400140ea84111815201c82d811030004000f90002d101d100700c0c0c03d980 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 247199802 1250 247198552 247198561
    0x309140105091b0117040b0405031620010804020f1201021c0204060306060f08040b06010e030d08040c0b070f0f030212030a050609061002030a08061306030f021503071b02180903090405 81
    0x2c03c4170400b0341030403104003801d503078858442042c041d4005006a1b03060004200302241840728034440c1c04154492000f070801c14114190300c500b8440603601540c148203403001444056a14401c00d0505036104850080c503145500d117086002e03000301d410700c10f01c00d06882c0c3c1d1607081c3c0046401078025660681d40130040f1a944140446a00740d2001d40c5102041d281c01c041008102c45000099000c101818107031031444611b808249851102409400000c0c4528140420030540d00362039002800c0b00003810781400c03a5600c80c010b41014402005040e10f80341c0c900c0304c0805000303100e40d0709400817400101b522482d2408c14107000e4441241e480e880b03500d81c00d0019a1a140c03101942900130900d900550610305000c50680e00e00704d010344115030001428045da000780d10b40d40100c101451040481c0c03409422284140f11410314072021031402d6803000c2c010450042d1b8810b00c0c40000e552022400a070075003c2e4008110f500120000b0608003000a2080060640700080280001107003503c041019994 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 247201052 1250 247199802 247199807
    0x3090506060105040b03160e10120c0809031209070f15080a14010e0411060a03150f05030d08040303090b01060807120b0915130513030f050307050405010309140105091b01 75
    0x15074010b02000360000d001003900352281402c0b10901c00080d040231540300455100249080322401c2035500051580115140d4081140c001c941c41441c0310b04051000f4180001c00e030fa128000d90034003503001405200040e1803070740100a1100141025004156096110703140c07404a00d0b41000076001140c01c6002003100c020035413003458200d140c20781000c101a400c00100c80119403016106583d00913508117030205550f9030704010f0551044517207000401480b00d001d506441880d0361b01456042e1103071181000a9140880c107044c441d08507141c440d200fa5500c1c03400350014548000047d000c40c00260000c034401e90000000c500642140e201d083c8824072010401044d078000d01c0c0c810342c0204003040803a4200080002c007980c140e40040080200c0030062880e0811140b086a4808041074a60b03100d6041c950080707400380d0b05440c0c070701d051855440c258038040c046204500c15a4101a5140134034000c0c06010f007000201c05c92a40020300485c00c1c0030246c10381d51180c046103820414902d03448a40c01d0360 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 247202302 1250 247201052 247201057
    0x905040e010c020d0813060b0111010e0102040501090b04050d14100e010b0103110c0c0f03030918011e030b0708270a020405060f0f060c0304080d0207081509100c0e04020a03090506060105 82
    0x2046c480e120700d58459030f4840f00074026004c0c0326410300c90b90300b0408181180a000b8009500c3d17103500016140d41c9408001407800426500082e105041040300344071548aa40322b0f13200140d004000c4030f00c10019078071081d00d02603006d045070003d0351801d10708444241e41900090070019090f40c060255a106002040300e44c4103c65409120740e0041c0a90812428001c1c103a00306014001e060740d062100120220f0440600c6031068800101024014040e0190740b0310302c40745203011440c09214450540e81c400d1034801001d000101400503c07000900604d800240841c901004c440c6032428801d860220b0643e1854581c1003244a6400d00d400035080f800c2810040c400e00a004000701898000782c0e0501075158804016985203000030080071031011020170910240c504560700078245a40303064140742c1050480d0049000000c054001d01c0808070002504490803101d159002030b400c40004816201c810340f26983c03607000360000c2040550300c0d8059200c812103078025010b64401d82d591000448051 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 247203552 1250 247202302 247202311
    0xa1407120e100e01030c050f040b1b010902011713081c271104110a02031e2106010c0b011202150c030307140909010905180705060a030c0905040e010c020d08 69
    0x40c2a0fa00c02c1e44280d0310a030007065003c80a82001881c0580c1a0711944030b0741d0090704008001180002c034400c0245803902c01070903658603000208110741841d400245955902607540521142074400f08a6141052b2400826540c4c09894196280d040700d0807031003411000380141c88128078080c080481c5000312840103104a511540c4806c8105840c0d841c00040c0c2012040d06822603a031b0a44000300f91885c5004001c0d51104c1d0b0011a1107904640001091134110500c50900721030500c442100003580306809040c0c071004004204044d9220030040f01c5501d0f0b4501c025103170a02c0e040002400c03903581c40408c0c18140c002d0360001c50b210911070503818913100e410b169440b241d001b080080c00c818818070810720801c1c1500d100300d140405a000142c00b0740001e820215403690380780f003480394410029518294500003140903150240c501000501c49001d1160150141070f05e9220100c0791074803428008015010003402001740300002c144503402009001102c1b40075204480880751281c3c050b0744000d100b07 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 247204802 1250 247203552 247203557
    0xc0c010f051806010f2610050f180c10020a0b0403031b1d0d0f06020d0c03060806070c06230408030105192d09051503070b04080c04020a1407120e10 65
    0x4907252034804a00341d00e1b030700400c0c0f5030f115840310755134010081480744065491072418046990304000031202c0c1c840c5800b6001c0743e000802e1401400c490200460140480c100c11155114a03400102d01603080c141c481d01c009091a00c0d00b0100300c101505544410310721042c40307a16210842001205503111101401e0b69040c4c0c4d10a000301c801c8c075240801500805600c02c2e4101181e02c0c01c15034901099811002e560414107485a8074842c0f042e502d842554014481b08000b808641001c66000d09000300740980508078a480310a04681d03034800d129070503c88550f401001000d0b19180c00c1c00d0980390820b00400b07201c0e00000c0c40200e00301c0c0780031264000791000107809034502e918180c143c4030018192105048210490f03580002c01607402c8c85940d00c00d81848007205406205401058105074080d04548a50340051109024020002503180c03400e1805480059840042800c1581c80c0e600484c0140143d03400011100100004425001502071550720340c00c0007441601d081007604801c20003080b00 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 247206052 1250 247204802 247204829
    0x501020a08120606090a1503050709062309060a05030a0e07030b180717011e0531051c020d03060b0703030f1b030c090504060b120c0c010f05180601 65
    0x890400310880d250450f100501151030510810b011614085940c2c0c84100303440080960342954039014040d40741c0c0a1014a0102451810a84040e10a00c8078002c4803094803011918070140042c6030f021980022402000745450302e00900009121754030840c0c0d090503041c00d1011641d43c0f90000900c40d0162544080d0401e6507503600152600c10410120203540144200300b00010114241c2001c1508034038003900104074540b81142c0011002003084404840d5481c0c1000c02407043c0490040040c0a00c11000d54119100c0c1650400d42407103030841c024100d401019071207003003d09105205074040e50070307401745ca299580c4110164111021803140410307215007000b402002034481e46c031901002c3c22130b21300011031050714002d41e165100d18000900119550b84003840507141c00c240e0810007072000b1502480349e6424074004080a0245441e05400007000c80003240200c04400166510040a00c00820014030320302e8100c00900000d45600141540000c0103a201040102c1c01038180d8854401500 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 247207302 1250 247206052 247206067
    0xb03070b070254010f14090906060d151803080c1c0f090b07200304080a0f030903060f020d050604020a08070509030f0a150b030a0f0b0c070b1f0501020a08 68
    0x1a5200d0128540c0260b4043c1d010509042e03c0c1d80105406003440c461910101c4e41411108144002072040c6244078000800420500c041e0000c2c0c11580001e040d90491a0102ca5140c184481296881b41c40300c02401c0008206241030004030800c0e02c180a6070f00c420044d21140000301c154480e8520034058142ca807400000f40d00f115801088040c040c81c140040c65003503030340300c82e80c0d01c1800341c1e510f8000800215825002ca075014040440181440b8050b5240c585805400c680d2000401c40061544074508046400c3c507000345810380080d40c000005001404030600d59500070b5224030300c1440494507000100b00d41b4103080c800d56103e016140c64185107519005401d4805401480c0d0065047c40b814010300040c40301404040d017041d00c90385440e40c448489000c036105544071003035200d02a41c01240320001003542c20708601c4481741c0150300500d060301c890441c160640310729180a007002000400380b16808546400200c14425000362a010640c1c54070012616a1912203019100710424400003 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 247208552 1250 247207302 247207399
    0xb33220e191110050d020c0105040b1026030c10061a160b0604060b0f090a120203061614041d010b04062106030609030503070e01050702100f02010b03070b0702 70
    0x283c400c41907401d0250030003610701440c1c01039900c41030541c2e003d651120103100401040b0700c401c41c0c002e5001800c4080391414120a0f00e6402a0f2011800d000c0f200c8446c0c0a04656061045440750141e10041e03442c0450142042005400c4d58814880000640802ea400c0b1001410560351904248081d0140e141e445803206034000b000500b5081d40305949030000144020000010440c40e21041c00c82c0da1a00381c50001c0001841d0940d01002c11070410143d02001a81c0120344194080102d1040c2d0002c0c1e40c0d1b04c03008448086002d050305840700070000740410030410900030300d1914081d4640b00003190782c8404464001b40594401c5c0030101c1c2003100f68078a880203660a80f5101c0c045900c0000b0071940c3d07501c4101c2580d02c610001d03000b048000040c02000ea601181404d5003000030b090640c50601c041c0e01181703803294003030300280400c8060290901003501c00c6d003054082d0304d0000c0460f202c040d00c40c6040c07481c3c0d42c0001c004a10489241ba4040c200c484030f0700800200d0790301d00d415021080180c44c0f89 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 247209802 1250 247208552 247208569
    0x307110f040b0a0915080a05071e05030a03080103060c090f0b0906090301060b0403150b13020d2415020105040c0302060306061b03070b33220e1911 65
    0x10341d4001e864040e070044984888074400c0060524080c0842d00e01c1c02400614000c01064010907290740100e002d00c4085030001400004480808024950106106c062138100c0d01e0b09030400d83e4140921140581890360140519041e2402014100604180200d00380c0b40c2d00800c5c0b08440030360400c0f040400c040703e00d2001600c4001405040f041c541020140000d0868480341c1000350500e10100341401031200c034074554034142031461010011b5401c05800102c2c0c00401c8141c0c2c0030100c0d000030700480c0d2005143c0200b2101d0350048400c1004401c40140780400355110b000b00901d0032007040e080d0803458414001d2600480d00513601c801d50380d080d5000d2000c0d5030300003050780360041400c00c400400e044001e444440c0b004d1810014540365002840c1c001202d02c0c002d03280031300c203419031070710310040c80c50300f221500801c132646201040c801035150100d00301721454145504402c120201101c010000ea8016840e040040c00950700900024020f50307812500e502c0016107104041604000c2c0390400071030 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 247211052 1250 247209802 247209829
    0x1a091c02031216021c0509060d020c1b0111010b010804081e0f0409112a0106080a0b0f01081501090f0b0a03030c020907030b0d0b0402120706020d090602030711 70
    0x1660310b088064001810580740c00d441000120301c05040040b030703466050000100c2e904010130300e104a401902d00041c20390090000940c8681000120005c1007445a41104c66401210043d030b1210003840d00000c00c0080c0c2541c0540c08503149503403c010040d41803250041007907050b11110000c0e292030b218010140c002c44142804a600c42c003040200600c82d07809001c0c00307107031890055995810940040f0554581840340104900d061003a40e80798000070f0300111880900f810480b15445102c03a2013800f424444e880702c001d50203400d5051081c440440c82c1188541000e00d000e000a90b621014a81d59000c9043c0c2d0000003403021005010301801074004030100c41c0c0360395020a40312050000600c2c20700207070340120003181c1e8081300481181424000150f2114031400c4c00c10a06a041c404542034160150000b44050a464005811961030b40801454500c1e0003044034116915000081c5d0f40300100740c03d03a00426a0000001440e6100204540348107900031204082c24a5100030310082d03492040 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 247212302 1250 247211052 247211057
    0x30602090d1b030309090204120201051c0c03060302180601020a0f0302070e010b041d0103020f15040b0f0a17040507030f02011b03050306040b190e1905040302010204031a091c 77
    0x91070114109402c2205007030004800300d00c0003460341c500a01643c40c6036119050550040c0000c0040380e40c0310200540071358080c2461550b4081c5904041d644801162003d030085181c820200c5507950b1592100c41964402e852545500072051210481d4940854945006912603c01c1d84001011120032000c00e40c464012204020303190f610480c40b5003000d8103c00d42101d800302c2c0800000f040590740b1300c110081034400013030550668001c11b14010f00d00921a019100c200c400351205040142100e0040c01a41820b54807949140e541801540c000c0342900d0010305d20450000120000216940c0919070180091001c14516a5000411080714200780d05000505e00f50040d100407040035015558032940d5040c2e624a0b2103020002102c0c404008140225004a43c003208480c0c1c000c0b04500341d804144080116648214800c4190300c0c110104201c45030501c0240010507030150082d0092783e1148405c4400320602e0b08a007580d904049410500d030b075110429842203090207941c5501901e8861 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 247213552 1250 247212302 247212319
    0x1e1506050408030f0c0f070305010b09010e090d051b010f0926070b061810031202030703090e06030f0a030305061828020c01020403030c020f030105040323040905070f03050c040f03060209 82
    0x8900b41d0030038400354009e50f136603515000240078614140100c540580320f01c80740400230781840d20086035a48a4100c5480500c10b001501d17149000d2444640c11000c10840b0080c001d480d030000300b41016200140d01207403039190f00c04210040c1c0007111110f50720348040c000c90350306205407529180c8a100002c0c000e1900807508a00f80c402c040c040340805c510540c2202c9494525a2840c0ba02c030140d03030796440f00700086410601408000a0748517803010b08842000c1e0501da181e444800000e41001c4a11495071150320816000d40d0030145c168100304d1180d401281e5014007100d42240461030340d002103030800000799160482c816980c180d2007014885202c4030174018109652110f1403800c980c8550000e5002c50040012101141340c009030302c848858095009010504169030090109140c03030042c0801020740d042c010388142c80f410280c50091451203000d114a00f412034000c2c3c2100d03464444800000c0c2810002510a03280e076003100c04803400642d000000618603200d01c0300030b4001c04186680304811 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 247214802 1250 247213552 247213573
    0x609030d0b06190e030d1d041d1c02060112020f0103020a02010609050109090b01080c0f010c080903070b041e030503030a1e02071a0709050d020d02041e1506050408030f0c 75
    0x40d603500f9800c000c0d05446820b50340d5004001c01d89010b085c0e0300c0040401c511030f0060508040b01000c142c400460507900070404600c00020300302d4007185c0007055001031084610281080301ea0342440031041c1940e07000d690321170340c03100030b00d0788450300b4103001075085134107000744140703951003036005200600140c800050900d440d400540c054690aa0082c0382c59a2290511750511002070021780c0100308102c024500c2164501c08507040e54200c0707001071706104d8008c40010a01507160200c0700c0440006094411864484066004c0e0790000c0c01005424400c850551104c9008040107800352a0800d0045003566203050000001c1c000c96400a80598100382c044000985c060000d0151103100300403a00400c43c00542462800a00401c003604020039100c0410007504c076217004600045e0142c640745000d00540c0081000b8000d010307400042c001c001100b074801701c6a00c3c3e0009100c0820707002c1c1c542c2c40e03640c0e8a40803100c3d40614010054143c208100d440c10529041004040310602102034808500e003 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 247216052 1250 247214802 247214827
    0x90b0304240507111212060d020a0b0a0c0606060203090d110103020d0e0705012703060c0509030a0b042117150303120f0f073608100e0609030d0b06 65
    0xf51400d0012692101d403a42c901602404048000c502aa005c58145468040d09914482d030281142c1e010b241007a10342c0065481d03111801000e0456030702181d079150a803100c0108a8103052030700361082481c010700480c096102104803460030500807c007480446464680030f101d00e0440d9003150600d5420005160360100c240030300342c0d071828981c01402aa40c41c01d000544241e6245481900307601071702e44041d8202004400c08401d80fa0071a01c00243c03024506800d0b9420300c1880c0c04140e1501c14210b181c02045185900c040c811480b411502143c4000400b44010800702107000c400442c2d0340359021500704c42a104119800784407419200ea150300400b002ca41590f02404511152688035410062031402c0008501d4000c200450b0b003500a00d000303000140311046070740c0720b24080000102101200484034000c2c400ca160070318940508a640d0707a0303002d0b6880d281c00e004101101c0c00d1848601680c000031444500c101400c0740030394030300b0908520b641300a00509613180e600100c14410710f2040f80303 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 247217302 1250 247216052 247216061
    0x907020c0a0602100509011b080c041d0a0e060c041a0708040303050d05010b2107090801051503060c1303030c050f120307020115030c05010e030a0f05010516090b030424 74
    0x7100e401070711602613203c2032136040e04c100404a24003a810148141420008419541004045403030038a03101c1e2a698620486441144c2c060101000d40001081e1074911a500d0b080c007a05500c0d00400500410080c0b20b5181d480840d00001140c000340030400001c4100c0444e00c4407000207600b030500e403910b03a603500c80482c0c2194100781c0000d0400f06010344030394894032403030703015103120702040c1d00b00884102109141003030003854101f9850200702041440303001d01ca04030068804840280a107140c1004002d084001d080b140380d100c1c3c80390102064403031020000f140c040074074800828150a0030354906580003460030760110741c42d01c1145040b490641d0103003c8a9040d508540c081503581c00c0ca10402130030748094015010755101e0030102000050580154881250400c0c2400781e20040c41200182c101000160b01070131080010a440c0200401940610701c5000003500d91405258805c40841d14507040b8081d042c064041000444d02045500f455110000a040c04e1201a501c441c0181020384 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 247218552 1250 247217302 247217309
    0x105061e03341d0c16050d1e050f09010c080c03070c0501090504020307080f0a020d0e01061a0f03070c060b100804030f030b06160501020702030a0b090d0309020f0907020c0a 76
    0x25108070441c03440800d8041d64400c020409143c080d60822040710a900c3c0d645405004181d10a00001e180004541d2100c1c02c1c48076540c010041d101840500380c4090714051124480043d0110650200d080c0f00c0d015106650000144800490900e0b0b8040010748240d061058180c844040610110507803a401300018040c01c1c0c4520b0310400301c58030301000034221803016044244924018400c100e090ba0740880f9590380180324416011190f1111341c00e41000f44503200340e401d1898104000c200c41148150005000c40b201100405c1d0010b0040301d44c3c074064082d021a030030184c401000410b01461060640400090107038400003515020200080d16803000c0990400100c0d01607420441450b801099407043e41055003420b104a200c0840018828030030344002d8926202e681e28500c05011003541619811a4041c084503d4880e007404c02c02000e1030111010701280c418504001c510754402d000721040300340d010309564140c0d1030400811040f0f6070000c01813000c6210795004111142c0d21056600c004 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 247219802 1250 247218552 247218613
    0x30204020d1d0f071d041b08010e060906060307061403100e15011101060510051e0c1f1404080c0c0a1e170d0503041a0106050c0f0105061e03 62
    0xa0f41a0030840303003420031a03030048404490380800600303440c415001069020f6480302c0e110f00380510f441c401d0050000a900510000d610b45006250b02e03110020303031603006e544807500316900303a40e0380340400d42d0390300c90780c00781c0e10001d0100c0c0d250f01c06054042001d0b607000a9411225030103030342c035540380d4018040110b40c0407041c1d02d10078507030390b10558000b4240c020000c41d0400078490320b030500001ca110424481e60160401c031001880d1000c0035041d60040b06030710b01000191b0b546a4a07994a941e880c440101056000c1d8400c8071f2003281c07802184249102051100c850350707980c0e074550f100c005640e0415580c1c40e1031400382c1c0c4441c9035140c4c4e6400074080585918401442d51860075140300ea03074080340740c11000c05e1802c0300b0f40a2246420010f1480e00300b03951441c01641d01e948131b20b01400f05101c0e20300b164450f012050008a0200c1e0014003405a100c80c0c1800c580080700080b40c210b00360b800c10b5a00703d400c0805865200d04000c2d040030903c02069010b001c8428003503148a8480d4164241c4103403c00 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 247221052 1250 247219802 247219813
    0x1e010204180b0f0a0e15030a0b01140307060f02100e0312040c060e0603040f02060a0207120804060807210b0a120b010302030c180a050a09020d0b2509030204020d1d 72
    0xa0b41c50104280340d07407443e05481d00c8642d42c0c10007441d41d1044c3d00180c007144d02813580c1e45071030300603603010090040425844010103c80f035a660507041c2c1201e4950001c1c40c031a000780036010a020744030b04056000c0d403221b5401803c4038450790702004000d12140c82c002500340000c0092100d4680e10083c114083c92142c2c0030103001915280c4c0c010120480c400450b03100e40010014080810000512900c80c6074048413410750b110140310701a49001c1c1076031720403a11201c107004004140b12404010300121800c07a203420120f940c1e401000c071030340010449400700390320304d1508500b56019964419801100040c2400d215943ca81c400a00d00308030b00d0f8402c940790500d07400140110f003001d1200f5801c0c040c040d074464141c02140301c40100700c01c0c4002c0020042c1e69079040020440c070b02907000f0b0030b5415005403021080b031130581402d0914010844454500d01411803550814032150b41c000c03d4014029514041c000d802c6500300806913008006030803c032a15061191429450b80ca40000b04401c608010301c4c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 247222302 1250 247221052 247221071
    0x5100908270103110f0418090f030c030e04230a0e0f0102041802090319050102070c061701050915010c05070b04080a0605011e050402070501060308220e0601021e01020418 75
    0x4040d905840e40700c00a604062104005d505504810b840c01c0e25881240030000303010316640d140c01040d00c418080e200d40850200c2105040e040900420180d009036203501140b4807210a100c10b40e651201002c8059503400c5d030002c10b010489841c20b8021685100120701401c0502810340f81025226461000ba540001c0411520740141c0d45620f0290711440150b041ca0005400a9141c0c18100800300348610114006000c12800798100c03110035500c0704541e494a82c032401c0007800c6003c0e08040c0814000c054001260910704107519500c03640c030022903150000040e0b00119503001c2d40c10b804460b41d00c50590085006403480c400f078409401100010b0040c02214280f180a50700107900c421580000340c0076841d550400c0028110640304181c1d40540e840101d440d02900401d219400076141d1800811002e65a0b800c110080700800c900c420459642da4490b50150203502003942e00b5400340c2c0c80504100300c402407e00c081c00d07400030503400040c01d080d0364154404001c0368550319213466650f00c0c4600c0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 247223552 1250 247222302 247222307
    0x9010f020a1d03010c0f050703021c0e0910030c151b03050307080c030702030d0e160611010e010b100f11070609061b02031513060f0608010513051009082701 69
    0x142000c100480003403049891741d41000c1d01c82d6807806403100c1001300001c0d040d01810300800c030010203800c50b49210710711300301c044600078507105031031510920843c920b4021460f010580d140210a0340d4202600d040c3e607502e0400700c01d0040400c52400014048461082440200c00407017002d101802511001e43c1d914011030000c0c5109402040070100900c2030090100480c0c1c00800e58402c10903c2000054480d80c1c0703159549825801c0318252190040f02801042055002c0602c20078145010000d00c4414204d138007540c06d8030750810741c02d07402104e0300520341c0026204601400b00c0800d942480e13003c448450610313a0802c0c00c2c0e0340105000c55000e40d41048420b40c0002e01d1032008154001c2032581402aa0000352145080b12105c204c070040c083c08103600079442c8158100081d0710203010403403110316207280e5011b04a140b04500c240e52810001a000055010075079044503807103005400743c03114041600e001058811800c4c2d90f000421701c9039541d46074680d540c0c0343e5001200f0350075a6080b00d540000 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 247224802 1250 247223552 247223597
    0x60c010204092403170426010b0d0f02090c09060c01090302070e010e0a091e060b0315130b07020a0b0703020712230c031e070309050f0f0909010f020a 66
    0x5240e29001c50070885200300c074542240f002c1d240d000c140d420f1807040300c00110380503010315000442c83d1400501c0258030740640040140f140d43c030750130003404401d00b03460802815920b10500a800540c020100b60014901000d070150b008003d05171080c00c0c9824040482c842d50841005e0807010307036591040000713040d01044800000c00c0c84a10740300066041c592030043c250805404188000d4595a58808000711302c801401d00760000c1c030a2030b0520900742000c401810f20b503400a8005d0103800b50306480034410520240c41078480c0291024141c800e035490b051480801071002c1c045020b42e0b240407000500d0f5503090740c001c0902d03503005601c4101c1400d180c2d81c1c03c0e840d903100e4014002d50600d44060040b841070303460411502480d1032611580c0b040003250642c401c44903805200c03600e00d110b440101c0c110b0380183c90075901950769201c00340c0d00ca0081c002101100050b0390f070702c0204006030b402149062040c2c29408200e03440007107040449900c00c002680c00103000200400c0c03082c1c0d043e42008009050 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 247226052 1250 247224802 247224821
    0x3040f032105070605190c02071d01080a02011d0405072d020c04150e0709030312020c0c0d061d07050f030604080313081e03071e0207060e0f060c01020409 68
    0x51180c2441c40703003024155104641c0002e01e95030302d0702d0005101e010a529820b01801c1540014072a008030f4000c020344402090096103041009032041c05a49079042500d60306a41500e002804504060307001900c000d5130180b202c00003202c5102d04003000703455070302410340146800d8540d049980c0d803184881003080c0c2c4174032101131741088850011050300d03800100036064100c1900c00203050404200301340d101e86d980d50004000740b8107171020300c07008503030000400e821a070103030341c5912144a04a9001c02a84a807046440310355111001003826850404140121144218000034031101c1020812036203c110f0100d1140c2504540000c00c1030741003d000754903c014080b0080d1071289466650f2400701d00015024185942200d000b032010000c0680445840104456041d11842401101103c141e48112541d90000394406440100b0020900403040640081c2d005000b0340c60070310604079041901321858581c003414942c0060140e440d034400071f240044a1a0015030b440e8140003001068454000 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 247227302 1250 247226052 247226093
    0x30605030307050d030518030319050f331017070513140a030f111009030305030a0b0316030803160908030a111c030507020f010c090b030a090503040f03 67
    0xb20700000e03008180b6002650440c00d0010b42516000f038045814445401407220301c0c40000140049000c030000402d0112503074460510603551103010346c8800c140152589000c00c06000b4605101041107510b0940403010a16103610603c0d80c04000f594080c11f1350402c8001c100324500b1140c000304d41000d0260702c030180b4100b032031030710000a000c10f46584107403185c05000134241102c42159910201c403e002150043c80f0104c5698203801d05080c1b000b0102d138a50303c142402495040141d00800d006000c60740c0507120982144d640394020b03809092405000c0703600d4014030311400340c2050313402c003801c002c0c500031120a62286010079501a42401c040b0188042c0150781d2410410f507400003048076005c41551924001c90f0902c0180c40d840c3c00304e03501c54860030340e4410345500c041a51660041d032180c07000d94201c0307407202d040013001c070300b2296144400700c0014911501404119080d0740159003050441200250382079454855600b075400a0f00081e180204d20001081404541c21b1000d810540741d4 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 247228552 1250 247227302 247227307
    0x40201180b07060914031c0506030604030804060506030a0203100c0e060c07050111010b152724040e010602160603020c28050115060f050403110d080d020d050103030306050303 77
    0x81003070405405100402407940d80c48106000070007440a01080035070500300203d035120a00740141d0001c2c000005445100b051410300020064500011400d014540544825070f1340e4490303885150250600520064241c80b503521440016102003021003481011030f60002080c1050f10b0005208000c0d0150440c4200310030b00111075510390104801007180c009003041516408a128018050705e411072030b581c0c1c8440c061a0103c3c0a180c4100200f4204403500034030a800507200b07161262094151404035002080d070b141d00e502d81c03030380c03282e4031000488a64000c41c140b070396401c00c00c0c0c4224002d8100e00d005801100c6000350811680f5212005000b843c00d055060258000540c3c1e903d00b9030949480e0780030100003442c500352210301124010907800c8002400300741c041d40f4144546130701c580f058000054408800380c1134980320300155410340e5486401c1c074591020102c10004ac0c021000301c159844c000402030045200664401013107a0701c21900040b481d5071550a000c1c0845555603c02c80c06900708 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 247229802 1250 247228552 247228559
    0x30b03030904092105120a021315020c09040c15020708121c0c0c050d0905090a02031f08071a0408061602030906040e0417070203030706020d020d06030b04020118 71
    0xc0291100c0d41d000341c5000840b4002800d021004080d403640c40d11100b00780e811200c0e0131540c0640140030035600c03035610380459228400c01d02c1c01c91082040f1100c0200014602388000f1440c2202c100e0040007a1048030b43e404201301c00512082001c1d00c0072203a218504900b005140869007400718984418006400d10b1440d000c0000d480d00440d11104d103003084001100035125580c0300600c84a100e840000f00400c2180c040302401584115200796668030503078a101c0c3c0000d120700c6110003954070203084618076481700c1c403164010350400b07440100354290380320802508000c2098803c000f402000c00900510346130502c2c04111080502c244515290104010f11640c200010040d41151190702d1500011049400032411401101c50259029100040000e800415802c029000300c1c0038806074041e0305844401c0480c54426800000e406410134001a404102d59901820299030b0410b00545002840b080100444030283c10440390510322100380000d659200c440d40003184000c4012a03d45402d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 247231052 1250 247229802 247229809
    0x110c120306190b191803030507051e0a0b040611030c030118090b04020108070c06110406110d020c06030c0712030e0105150919020d0203090304060212090a0306240b0910030b 76
    0x31544c240d402d00780c0101c40c0f8850309100c0c80c3c0d1900741004108044d5099605c030301e0010f02c00c3c2c1c0042015103c0707216094420500605402010920708254801042521006d54400d4410200100140c0d0600d42e01d4008103c0401d000c8000c510868070407503855075942c100704107112400104000100744038a00308140c0005400d20603081e400540908000f11071313954420085a8101100d00020301880c20406055080034682d4040c0003078984a032030358003880d00f014560703669403c900300344080141e0103145669003508010b4011600078a165170000d1034010759031500c090081c0f00b0340c102400265200401410b100c0d003841126040541115511070794280c0381e000407020031019107544c00c2103a82d074800700010545941141c01c03c0c0d02541c41035407289008a031168603074100e8407904001d406034514800c003543c050411a95000c1c00244000c0c001e50441c1c865000804003400c0044080e4681c6034046401c6c261750101034028070550319015511a402424490300386025280c2006050800f52045810b54 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 247232302 1250 247231052 247231057
    0xe07020613060e030d0e030301050123030a0c110d120b120a06050c070f05070509100f090c0c1407050a0f0e0115022d06010e07050a03110c120306190b 66
    0x80e007101020400d600d030601018150300c01d15005d441e2640c030f00b00c020000340c14007001443c102d5009880b8280d024080b4210100c1140c0f49048441c103d0700108001840f03141ca5510000c4070403618034041c44110805161246007950030343c019408192640d200360300041d06405040800da1095542c000c041428000c1995140c0451000800c0180c0316000583c40300013680a540759175412030711041c0703c14400c3c1042900c40e2034a000c1c0c640200100000144080181c8941e10111a08400d1100c1114038200300080108000606842084090b0f011000402c004881075010b59190102414001d403900c000c0045034050b81d80000c2107402600c208008603242c04134001d0450352160400b19140c256210708030706100000c00700fa04984034500d041c0012820202c030100e1f41d1907103041150443c7e40c8074404001d02642c111340050001d442003005104580c400e8000341520050aa40503042c009902d58440c10481d0b0600f41d40d045813008400c0100625080304820110210100c4d0311707a000d41450b46805951 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 247233552 1250 247232302 247232341
    0x406051506070212011104090e0c0909060f07051902150601110c0105030606190819091e0201020106030b280501120803100503070e0405010f0c05041a04050307030c0e070206 76
    0x310f04e51061420610000e4102e013400c0548000826a1140c403240300000030201413000916501c203520301180c240c140414a00d00491850006208a81e00c00110800141c001000722003041801d02c01c202c4201041e40d58903030703d84125000303025010780c821100c418800d40104030504004031b03004c030701010000c0030032040804131080c44c00320707500e83e180c0c804181c0d14402c50104071300600340804522303142c40d0320003009801081e480b50000b107810480d0762036005603034082e0300c090301a1541640f0744216001e100100710f4200d1040c000810350603501c0c1c9454080150813551500903808000701c00c0c10329407500408001241d83e800041149504004d4417241554a1020081c600340e000404241d44081100703100004110040484010307070f40724100290303102026201100c0319801c0c4080088100b106006184441caa56a520350a0a20742803403000c610380300801c20038900d0070412012405071028040980518081c000581c0c0c40c0d8640719043d440144024a00f030119007202c2c06100740c2205565490400 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 247234802 1250 247233552 247233559
    0x8190210030b010c05030403142505010f021e010501060e2d191823190e07030b06030609030f04030809120a0f05010c090302010e120a1a04060515060702 67
    0x90600b800107a6070000c5060018013180b00c046000020061070300e490000d14111003058503a000030484c3c6581210070003440c01a002c0450600c144015441041815251081441152400c0400310540200141c82c5c411811099449400500c28560803020f00603c01f01d007560708070070081c909609006100c0c1c5501d01e8103a01c011501e0b244040381d8460000b0b203140941d00d035015140c55580e80f000300c401b001a040840b50107041c0a0214540c03400c01d00c44242500c80d6010300c40080c0d40f1200501d01c0054880c0d00501440e6896a224940d14401c000900103107104a0000180b800c14008251070444010141385d2542c0c420030662601c0f441d1070007554120780d88617401a8035205410002411603500342c01084592203140311040920450100c42d1040c6401003000300168142d100c0c044030207900e203000181c080390301d038031082160b4282034683c075030b0158010040e03401e0800f11f6592292021032000a050400400c6018081440520310a242c0c001d520515920040b01071140483c101d40030754180070f4403 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 247236052 1250 247234802 247234811
    0x5060c0a052e18140601080c01030b03150417180f03030703140a090b0a23031e1909031e2102130b0c1005010b040b0f0f160605010819021003 62
    0xa036200d62612000154080000b0a04c09010842c150b40d5600074400e01c40da81c400d039422082194003a02c81c0b400755003005806410390700c0701c15030450210740025204494000200b2140855407002101412840040002c0d071002d800500040203d040c890071207040c070a4004200480020340c0003064050701440c0d050503a500ca2200c10401d07140300c13850740e0150b09220400101100500d0384200e0780c40308001c041e407000d441c542e441e40440c07589001c00c0702c1e0f05698a03034a0b5100314010700ea043c0140c4d40007000f120395504109510111100f41c8022590071000f15420070301e2001101451040f903606100945000740d461403010b601d540d60210103d40d0208c0003035000030b20103040720310700d440320000d02a202520f0760369504540c181d0707941e0f00180c3e110000c094034140000c914200c0342c00803501152060700d00c6a0804001400c0e448090784541d0b03030b5585843c410403101900544151050140034010040000c007589000c1616080402c1d60001910070800c0701d4203040160340702481c5014a2049140014 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 247237302 1250 247236052 247236071
    0x102060a02040b16150c320306060904090f0302010501030c080a03020616020f120c011a030d0f020f011a10030b0904110301110409360809060405060c0a052e 69
    0x5c2032000c40f07403152400715007484807140c49070750000b4000e8004501e4501d070705184130700203146441c070412080024505040800118210703140c001d020300f000442c0108005082040c0740e450b41030001613880c0440150751203500400a00c079030f0038003040c0241907190103041b1017030040e038001391168002401c0d4400005034000c281d010070320821000d050505403804440e4610503120a0034074507005141050760560030100b0085240040070503950109001030b00502d000c0041c1d807001ea61200c08038180c07404501c585030544a141009000325001120b032041504000c01d81079042c004500c0303020007203401f41400d2842226594841c039000035806034114400e0410510010002405005001042d28168802040200320054664004110781c068400c3c1c0149002003640510f200980f484050510303806040e90400208064000074410b040c03004110620301522a40011410f802c403200000da2a48400c3c08002040810440040420081c441d202c00142c04d1110700c5002804605c00d4020841d21515560f = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 247238552 1250 247237302 247237313
    0x1608150a0c09080f0a0b07050a020712020d0c0b0703090b030112030305060406091a09010518010603021804060303050d060b130918021507110904081b0c0a0902090102060a02040b16 79
    0x52001e4045101501c100294645045580300c900507000c0d100300006c0004a0310842c000c3c0f0464002444a40180c54402e10f04440912459002d04041ea04090140711002c001044110118043c5c040805000d44580c0703281401002400c0303a801000c00c1585c100018001c040c2d01c480403500030360b4549030225455603032001180c01b4107025400a000541070040c14560400181c04408032410309032240d40590b03998100b00003a041c2c0c100d0040c54502c03160310060145a03c20740045c482e40e625003004102e014012004641102c0095100382c00180d07012402820300e8100d401103c00908054400500382100404a01108401841620240c41d80e842d2a614540600aa610032180e0010300008100e181070b041410198010507080300c81610035840519a840e101020501440d00014803034141650680000d103994022605003038244240c80c07200f81540d07201e80846014280c1e080015071101303402800079141a401400c0da0036100d00510043c499080404280d48010f4172016800660300d010b802c08 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 247239802 1250 247238552 247238567
    0x4020d060c05090f090408340311010c0f0f20240c07030c060c1701090c0905040204031101142203020a050f09040b150904051608150a0c 60
    0x1406a4100071401444a411a01070070141d401a54107808404514040003c51101100c0050440c9001d100d41d03000400d85c5141120b900940c42600404a05407450030310b0b84000b1100110001400714070710380c01000c420702031005603448900306200c00f81180c0b034018001805c00310110301003102250494464003000100d0840c40b100d200b0658036030b2a0040b0003480240741d00501c040103140d00c0008034800c9104031003203501301758055561a50701c505035070300c0e1000340080062600422103171140310440e41981012442c000c2c0030100340000c800b05800c20240090000758002031040c0d20600040005c202c2d5440310702d00000c024681311503c0601001a0030b6140107103c450044540c072159482d5402041c0d8002c801902c0c0225488420303e07070303a0010810310514000c0000d400c0794010011400140030020601e41014298400d04495940c11000c1002c41008440a5601d544202c2d80c82ca04990f81440581c0a841c120004c5c080c00b81c00003e10340c4207000c0c05400340e041e02c0c2d511130002001e544034403031 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 247241052 1250 247239802 247239829
    0x30f0d0f0210050f04030f020a170904020f030a0506120a0f080f160309240c0f020f2d010f050a1202091f120522171902060c0a14030402 60
    0x40030011411300b460780c00205501150101d0104100318480d03200180000741e0240c10540c00100d0000309068000c092080342c20010300160015000c1c012400b58009030303009103103d0300f1007001c0054185440c0301084048030a00c400c510091b04141000c50100700c4c6030300e01c00b0140c2e40244900d5a10340c0341c00c030b146400d8031861101c174100d01543c69070001019844109601103814000d60f4004010075031400501d090f030003051000104403c203090900040803108082c603800d000526642c80034000201150007a00d02c000305041c4544840b000e1850f081440003051040a802e103400403c0380241403005d8458030450003e40240700400d688020400c1031074041321404c2c4409022021203542a04201c0c5003541e6040300c0c50080303a141c540b028a0319000b841124805c2e000c4110140203001040609041245580f0b0250340040030304400950700d034843d400408420140703100520450001d020002c0c217121000d0920140c1503410851100b403103a00840074460b803030f1a5480c0650320b80745e038030018851034010b00 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 247242302 1250 247241052 247241083
    0x4020303090909030a0801061803061a09100317030601020604081305060406030f0e0f070501030b04020904020c0c090705030907091805070e2406041e090212070e030f0d0f02 76
    0x500b080741c00c2c43d0110140c030740c40541c0d80354244240d88450040c3d5001040075205d1a8207030840a0400c04102290031401c0b80b0b81d9440c0700340c6200c0c909880403850318a41100c6142a4440e850000c00030054044600c10b0700040307080c5001e06604102c1d0000b5112040a00040c02141001c1440600918442c443c0f8000b84801441a9074403659450040e02902891035030288007440c04602980008000c10403040c621400f00141403221f0038407005400401041f114142c00039400d0000305825200c520082802c50b10250040400e0400d0408002450b0b00c014200010401c0030b009202034420002860810f50310704035000300d403174812040191503080160300c0142c06d41c496110001800c006600040b070099800d01a00c011180c43c0c0c54804002c00c0d05201843e801c040200810400d4655140450340020010b01404001030b6850f201740302680c100a0f4000035082d240002d0000d039540040403c0c0403c1804d4014203030f46649400c1054403000704135541e0b014000e01c40c075042940c0d80300307006c80c803d00e42d00700 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 247243552 1250 247242302 247242319
    0xd05120415090617010e0a1413060605030d05030a0207110402031003231f110c011505040b0906040f0f020a0818030c190312020304060c03051b09090402030309 70
    0x7520411944011a9400c1001c58810311010401c41d20400c0441e10f4500c00221110b03c0d64a402610802c0c00c4004100800981c3c1d50110444500b4207000c401e405082c02d81c800b415540803e00b001c4040b50501e91156100f5800602c42100107600141a641c0c4242c68210058442e541c5040c0060782c046400c0d18250f10520010400200401e42c0c04042d060300d000c3c918143d1701054090700320106a002500d41c1c04254400411088048804075070083c507990b0084003c141e041000341c43d801c058102e9490b080701a51505190400d01e030107800c20a00620003280c1c24040e440140003c200e80540c00f41403c0d01541e228241c12840c03803043c2c0c00800011010160465442c400c100c1e0040c030f644402da5048450501003240d00b11003850003c140c035581c130342070b10140045c04014002c40c8007084038414210140811416800500c12441c80598826801000c0101e001d090340b80004049440007080716440c54440c040070084040c0c4c2e0000d44251407000c2d513040100341c031039000003443c43c0200011070f0b6201070715 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 247244802 1250 247243552 247243559
    0x106051305221419022512020f0601050609010806040603020a090603170712180305060406060501020c12032706070302030712030204060806090604140c031b070506060d051204 77
    0x103a44802e035118030711000c0102d504101c801a011000607904050008809485000d136440300e1750007403540b051070030020200301c1c0c00d04580e2101c5808117402903c8680082e00c0d5401030707035018090500288040c8000d007600d50f05001c0041c40314022800007904101020300002c007152500e41c454070241d5001090000d299540e140c407007001e0b208a010445024030000c1c900590000c40c0f400345c0d11000d0f070106d00680c1d040c03d00c1004071000b200d0300d4810240340809410010100303809000c0317140a14000c400c0821101d0400002919000341581c032140209075441c29003044e1100030040e9501940d07440b0503051740c8000080310f9094890340314036050f40200001608801c05400000130001184107058130404038060031825004c82c0118071803000850180400140e16142c1940307283c5d0b06c00c40081c4001548800c0003c035440c0a0001c072400d00800800100b03022000038101241049600c03420107142c50202280c6e9090340300c2401500060090000d25a68002c0001c10304c5182d942c4500c2c0c00300503403207568 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 247246052 1250 247244802 247244839
    0x1030f1e110f030703020a030807081905120105060309101a0303120709120807022b0c0807082109010e06160309050a0e040b060f0a030b2d0106051305 66
    0x7400300542d01c2050200c00c19512410082012400c03030760001c010511552540d2110040c2c1d03030140e081155481e0b0104107842c1900d0080d08131291050f426601c06483c2d07202d0460002c400c40c810f8200d0ba200c0c21060081014a0b000014a0700d1711490900c00421000c6840c450549140604041940d0602021138030960707100d80ca000c854400c0e2010782d103440701540c0d64440c804450031040c20103000040100945400b40c10078646034111940c521081c9407000341d85155458000a40c11804c5076094030641007000700700d1040111001509540002e013802280d601510541c554a03108003560910340441c049285a01540c04404e0b08003010703114030307645c14144000e50314000c6e5038142100032030468a0049407500740103400d802610702003106090300e51655240c403510480c0040c01d4990204e200040381c4070b90345404001d14001c42c40340d0740821060402d100c5503615010006099031403500c1005503414000891007409045a40500b00580d60390404040c01407c0107160f0801c40d04005140b40290720703081c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 247247302 1250 247246052 247246073
    0xd06150306140c09011403040c090e0d0e031b0409110a06020f07080c0907030f0b1012050901020306091f0801020f07060b0f01021e01020705100509150402060301030f1e 74
    0x3907201c88102d20ba5951605030026802210b0100e400904410040368820782d08200554100340901c046a0362180e0310007082e0f0945910341c0c0c6124590b04602d40011100f40c102c00c2c4120a42130807800342003005203032465070101c401010311051089407103a440f403051028600e1010319450010b8260f00200ba1203030000b80d0b0307822854440081d18420200002900036000c219141030b060014080d400b83d4503500b034200d001e06a036041e4010003540da0040403130280d6a203200b2013520081038507540e60b17280149510000b00c500040604030164010010405c130355558000480d486014950206043c0015202044500790f150f0050541c5600c00600f2840401011019042e03c5110311024045010100240851410604c4401d030140e0311084202c14034070050440b1992440c901c8000508041c8d180e2506c034a0559140d1500344103d954405001d50031005100410111190404241260400da03021891a100520014016040038108e00c1c040011007140d00c48070140c1018610700100003400d0154100 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 247248552 1250 247247302 247247321
    0x507090303110a020901031205190207062a0210111603111002060c03130602181504080a06050c07060c18090b0108041403070807060203011a090f0d06150306 69
    0x1641003604050301220003d41000401ea0240041e1443d03442d5544201c00768200ca00c8500602400344882d40301e101116805600e040d5142e030081000340d1a1107005030802414026020f01f00c06190080e2004040b4800b1020f181c1f0fa05031901054104a00b008039140b20f801c10710a2001e00504c4140100b0064103483c0c034066034040d18a60031041820002c10014502146288001d40c110800203001d0415000207035074040ca010070980b03001c54555580790704a80c0300e034640703d444003540d40710a4a28140b20380714541404140354020300e0310f814080e4807580d40d0380452000b41011340303440005460340541001c0c1c840c01d6a00060034000e204811030007821200c25501c480c0c1c8110201000060302085a001c0c4034101441078540c070400e81c80e10b0f120b80041680000404585100400c048000240200014a201ca00441c0c0c010303100c0d41081403a90981d854920b07440d0040c1c0e0705010302030180d5039003184098030040c00c0f034480441401901c1c1085c0900720030581c2d880341d298450310010038010b0780d80008060 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 247249802 1250 247248552 247248557
    0x8010c02010b04020307020a020d11030a030518030703020d080703031b0201021c02041a0304060212091b03010b01120e07051e0301060e07020d0503040303020f070606090b090402130c0e040507090303 87
    0x1d882c0b02c5818041203010444d070b4500141d1106190ba805424511002c00390140503540140d4041c0c0700e800403031720b4070442c240100c2c0003460008550704049130500c54414128030840150960714515000074140d2003601e600a45520000542343d02054066448210f1203100328801c0030a101c00301038082d00070340110101000c100010104c00c15130748880cbc800c03581680c1034100c0300003c494800c84400c00d07540000b001200d01329030030003245150040300302000744900c1e018030080c00929055292441980c980e0142203020b80c4c1007100e0541680e03040f005039030301a180130000040e007001031491549441d1403a480781c1d822042d0702c0300026108000c12107a803060b6405400030311000355601305178240000100e40743e00c010780043c5188a5030921400003507030424040d150160518941d814120308503400820200d0301580c0e40c0d981003110326400c2c018542a02c0b01101ca40b0450b2070180c0100d05052080740c8078010781681c0350500c1d04c105006403250780c00780c0d60250042115241040f030251810f0080d0005602 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 247251052 1250 247249802 247249811
    0x304020f0d120302210a0c120203100b07061404111c05030d02030c0d1812020312012106090809040623010e010e03060907140105130b070c030c08010c0201 68
    0x60a12070000308515600080540015141d40411802504200304080d045101004400300031074043c003025000740100040001d00d40208403010740b030300300624050382e0020b0050081041082c90035044400300d03400e031940d80b82e03110900d1606900074410102260801c0b658281030100348034468641c00c0740d400083e0f9180d00310230f2801d503a082c000c001c03125000300582d208110443c15506160003458001e0841c0c10034508000c80c5851080a90303e540040300c80586100c05468240404514500100d903004c1c0013a40c40c14240d800c0c0313007581a0050080489507080c1100d10300308000d04c10409071030107404c500208a49003452030711040c03640c40740120f148034034145540815024454198181c0d0f0604000d48514030f81802e600558180346980540c1c1d041c001000404481074030180b01e01403048030b020000e0a00b2a06020301c0130b034076004415590b4100030080c0104005000030500c2d441c00d40300c500c3d26558844000f8544031554220030b82006200e10405600040c480760305401c03403480000799400900 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 247252302 1250 247251052 247251079
    0x200105180d1b080d020c06012912060d0c150c12030c0801030303110d1d0f060106051b010b04110a0f031a040b040e030a0f091403061f030f0602030402 66
    0x480703103002029200d140703a1584120b58006180880200b030444140000541001d2110500385d00b000026400720034880c9080d128881d000c803011062068130340c00960810709086180701d80515100b00100054000c4584203511800d1100701c0c80940010320182540c52200500e540d4014188180d446040300c1045186501c0340701580039000d5583c119440303640d0764200e0fa10b180c4044018100070318015501c0e51080041001e408040e00440481d031101106c0041100d500ca44a00c3c90600200118115600840e005018060740310f0101e80d0003640400c80200c16185100c4481c1c0100030401899600034584080c103030f41501103c1c042c1c86009699100ca2441042d0341e032080e425221066000403518650040c8000380703241030743c0301c000601d00c0580005003500311825014035503482102c1c00b1021400d64500b15800c140c0c001d6410010303044820081010b0100c0ca004299984070250514910301c4020b0f4502c42039400310b4110000460700105188808060b6060808c020b502c2514164000c0c0e00280100c03 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 247253552 1250 247252302 247252307
    0x30b010f0308030c0a03020c03040b04031a240f09070c1202060603030a120902040c1101270308130b01030b040c060302180114090604030b070f08090d200105180d 71
    0x1042182d0b00014560724581c0d4940b011881940018148001e06a00b4042c10600450030400341024210044030381d60b8550440c10814441401c4407241014a0210010883d11540c50b0b07804810201841000400e1004850300145080500c0400c00ea000703084082040074443e400140c08c88034a016240000c01128690012615000212585505503000300460349056229010310b031009010784000007000001a0300141c292188444130000046000d00002801c10303081c81520340d01902116a20b05003041c84450380a8444090070180a001103c000101d81c20103009040b49070540c8107580c0d5110b9a100d2074200c42c50001610190364040c000707640031444e14004c0c400c0315401d40302d50341c01801080f0282d0044a20f010441929901c00070248000c20458070340c0400f401c0030310300c129582245460100c20040a480440141c002008401e60522101140104120030500468600001c0d9581da40c05203616aa0b5202c800d01990740c80c10081080c00c065038170104905140050681e1020700244104 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 247254802 1250 247253552 247253579
    0x3060b032d0907141201020a0305011e0806011703090a03050322030515041b08010e010b0108010b0d09080403140109050c0a0f09020d0e0a050a03080601050403120e030f0610030b01 79
    0x34140543d001030024020003889114075400c1000003031100c20603161606007942643c105070074550200380c1315001070088a41d0540c0d10803a80c01d900210304680d52404031043d583c0c81040c03180882e00403c03da140082880288100e520807030018007031810003035580c81e29954941c400340c180548810070b0042264841020341e410310440f41c00000030050100d200b1050351180d0000342c004c903030315485003032005501c0c103400c1c1da408010125100001030018042072060b0a54940c0800681000000c4d0300600140c80d480342540d1400022010000d0030101c0340c58520038500c156000942030071001d10071401c02c0c9805410204041c6d210fa81a610030307221813018003244100a00842901c600040344c02e0000000ea54064400c01d0440600800c4002c640c1c02040d041c2506180143c80319000303a011041815006110b031070b003080d42864281e160902c1c58a50f103030350422500303271070041159658101c01c580e64200801c41d034407201442922102d00345024500c403420b42c2c9110842d0011428000054040e03c03c041 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 247256052 1250 247254802 247254811
    0xf04060303080406060e0c07020405062b022b0816080403080702121f150f0801060806240906010c02090a0c0e0303070503180a0e0405060727090c03060b032d 69
    0x7000e5040018903270070040a46402401300b41c101704c4a800c208007001035802c04100181c0e900045180700303000c50052000d0400114a07030360303800b00300c800c1c48456410440c0842640e01d030032114140d2200005600301c100b607002480b010301b0040001c1404828081054000c001c2a03200300c40400b03100e200000c5141d242d10314114480c0c480c104040322040e071580648c004900e5603080001c402ca00f85c0c1c469079004260b0049070042c00031a03648800070300105a0401405811401c0010500000c0b03108484118203882012130960098181c1703400700300586d00452130019100e1b0300030881c20b600d240002240d001403580301344250000e400504141400c0c14040704407550960010090f41c0b6010801d0308040402e0138000b002500220305060002e03134945104565800350b44540098101400c100d0780042100c0d6008120b21444486140c050203890034241003103040790202c1501251806880c02c09030000c000701d500210100c2400020806403011125100c02e40ca00c05014100c400280c60b001c3d050b18060448 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 247257302 1250 247256052 247256071
    0x218190b13050a12022202091203070b010509011a07030917010c03050709060818030f030a0b100905101112070c0e10050d0b090a02060415020c01050a0203040b03060f04060303080406060e 82
    0x4030b10601b450b00000b00c01c610480151000f62030a031a00010401c143e51403940031285400120f8280304000541d80d580e40100300c11a140282541040800c4030003000c0b640030311005040004a0f5810540541420802006980803000700e952828107468060003c1d03080d80750010303207400005807045000b03c200005450007a56808010b40d101c0d2440019086111400210ba10041c080d0540400315000103501c1920240c2000c2036134020217081c8100076641a100b10140140d0160034030940e141c2d440d00e01d03d41c0e00c1600d44103400a065900131803d00c0b0300344c0903200e40c0074ad00060070320078000c1441c8000121070720101c1c00c01e55035450b5000b01e20010680d000d9543d0204094200002103810030403030a400400c50820344000c2c031001d5000030081e500590085140301445021800c0894050015440259003800c2c1300e403030b0500d50b000c02500da1185000d040c00200c804400701d0115140d40d0080120307210058000c222040e103904002d440c07514200e07800c0390241c0c207005000c10034044030462107001d24043d4 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 247258552 1250 247257302 247257319
    0x8070b09011103040906261c0f030b03060106020102071a06010c140c061216030e03161103010908130f0506030a05070e0904030e010f030218190b13050a1202 69
    0xe8004451400c84211890220700c41404003050788003807482070000500703000d5041000d40301300c41650804038411004140031900010140305043c003030f000b48074048503114600742c5070488086109900034000c0301c613251340500c0349070004113815405500509080303000361641d29140c81d52500c600600300017190382c2400542c400300d107000018085030700c0b00e445803158816126410b80d2140420440c0d0040f1400302066103900081c8245490341c58450480300c91546024820381005c209001e03600d110b1500b0b60429100b490203a6014418088a03550350742e28001d000340a400207905210b02c060b003046464000355080d08070300080641c10a60a1401c544020340b145007540d407801080001408010408010300048092904541d50307102d210500c204c1c82515201c2c4660b0840000421003400b405003d014584104001c0c850345070a6460444052402c5443c0c10300100041801d003a4002d8990020401580103d40c942000b401060040141c5000baa41400c00e6603070303414038010220340f40e039020390854400c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 247259802 1250 247258552 247258567
    0x414060702060601270e04080c0124050319020906030709110309010b0105040e0c0306010c0f03080901050606090a0b090613080a1e0b130302031c02070b060906152d03060a08070b 78
    0x500d5000d94040d00400000d82480380c4101690308bd1061f0f007001c039202000100c420800c840b9030b0600038010700750a80080a81002085850589000d24407020348507580070740001d10703155010841e00c00542079000041c01816102c4c54100b020741c00c140d4080c405035003406032004c42c1d54805e800740c40031900c1c00c2c289920240ca80c8001340c1c4141c2c0c00940914100100090700402280705414004140d83c483d903918403072843d040700f055007120f4002d41081c0c450034081220481c1c40c0d44850510060741c0201d005290340e40000000103006d4801c060000c614100e0454000031541d60110381c01b0180e0340200a45c00d0f040110001c46141d0100440d002003000c01000d000c6181380c1068114a4000341c402d004072490001e021210b65154251011081c190703640000b1441c0c1040005010290805001d5038845041c0c1444000511400b40c100c030b8aa0314032030003044841c60f51100102d00724510324071702d6060b090461400c0c4048016401180d0050103040b01d01400a43d00350b0009101c81191107402d02ca40c00c1008 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 247261052 1250 247259802 247259819
    0x804020105030a181a07020c030102160b060a030b0915130f120c150e0c0604030b040201080703090f08030103050105181e030f0408160807060203030f041406070206060127 75
    0x150155003407500d0104d103ca02c8001350002600c980c3e03802c0301d19007010309480c02c160024034003c40b00480034003036401070140c09038030808600d081804a0340125640f2680d03542c00c005c076400102c0c1c1d900150a60910006001e01c4505c042842c1030011303441c1d18841060b642d9203002d951441032114004208100c9100f0040108030100c9401012002a2170a500042e80d139840d40b00a0a01e504041428256a80788500040700d08201c9030741c5501c800d030303030090816107541c0307840d00310400060001c0d05015220000545e40b501c00c1c0d010807031095004c0c034080101c690754100992150802d000c2101c1070b41ca0a404500c002c0755451410080006c004000d001c201c00350700d00c0c100c000403410352100c00c0b0322040c448800b2004004010740040c1c05908020710410030b903081e10203442c044070b074040c00180e0031400d01404056808400c50b03500400c40b02da49201b644503440d280f1360800b62100300900e5401107605100300594086003203030082d24241d0310701040250740400000b0740c0c101448194400e00800408211000c0f = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 247262302 1250 247261052 247261061
    0x7030e0607020d0605040506060a08150103030806011112121f090f0216060b09060d031e1704030e01111b0d030e09010303080403080109290a09020a0810060804020105030a 75
    0x28400743c0100018401566054140c80042d9011a8280c006030100801c60804600050040142c2d1005200301d01d1803400d400e030b610030103003c040d040141c4c0e900000d07a56400b40d40c2c0305601c420f8090440d0301d5902c500440144540262510401215600300820b5405040e0004200d41c00011000d4440070703840d05511000800d62240002401c40d000e2018601d11644108504800c1e80149000301f0082d60307490410404410041401c0c3c0f0401680300c6020110f6400040c2c218030007520300008040e40350848096070000b04004203004a100441e04100805a001403510b041c0d0000780c980d01910002c200d42281c8622606106e641044802a4158854600668481142030080c01c0c075400030610303003000c20354440007604250040340b250b4050108043d80000c003140144080c038420020b40411031441f05241d920010303148191802c0600800f680d6550420340402030280e814210341d508140c01c4042c00500381111040c04809a04600090381409001d12a214540c160748051450f07503034010810080 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 247263552 1250 247262302 247262317
    0x30c050d0b030c06070506010503061f0603051005040912020c04060506070305071401060308070318060e1012020408070311030c09071206050d0308040605090106030302030307110f070f03051207030e06 88
    0x6100e050440400398513010f0040c400507000e00d014240560400090600d002005002c5000d01b0300f001c81d006480101c10000300c81070f42c929190204d42c90b1149043c1240c107442903000a80e1091510208104000840b6600800010740d80c0036954000b40000811044885c107110301604054108140000030388240f009005280c4541e501d0940020b1854078035003100c8607508112480c2c0400a0303014203058018400c02d607040a05100a50214240b4000a1109030380e00d40c8140074001034a00c040304680142c0c0011240440034104640740e940e02c04c07203a55120114031090341c42070303001c040390611400d000c100401c0742c51024140c00525205c103501110f80341c0e600c241c0f0303001456445801080541ea000102d00380c2c58003036035a807c5242000d043c11030840e131018040d440240e14001c1c0401c0002d4001c0f00350f0b544040c59041c0745020b4002d0081c028241410050700501d03030b01409101248501d030f00011801a83e02a000301c1ea00d000c220b0312440490f100306103010b40840d4040440300c2c003d03c0c01c80020040c5 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 247264802 1250 247263552 247263559
    0x6011b17130305030a0903020310050615030c09092d25020f01020309011505030a020916050d05090304080715020a1e0203060a0504170906030604022a0f070501030c050d0b 75
    0x24590b07a40b9164216080548194000740c1521801c1080d4901008070090041c40110100306500340440010000170741481402d20b00400400052040301c448401c1c0e502184000c0d100f085940340c07090102c542160042d0207200c48400c80c01c02c803d84d44040511940c460510303442020b000d03810081807281e40c0075001400780110300c1000311070312141d082800518054003440d000845c00c20100c00040d684001135030852800ba40c44a081c600244e0750300c3c0030340d5800c20180401c04650100400d0708035402e1142112250030701e0f0034001808a000f000000500441d41c040c801d642545881c2c4d109100d1030501d5945190043c1d008011203008640306051001c0349a80c1c034007040020a03402e90200341421000ca90040034617668a04100500040c0840b0b0560089080780d180d181071801000510f15010240c509402140d0101c7c0ba0030501144802510072590540045902142c602c015070b40d4036107079071004803141d020302d5400182c154002e02403103502200340c2e125581401861456580145210b0142951 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 247266052 1250 247264802 247264837
    0x51216060201270c03020a090c1b0308062215080c03010c020604120201230402010e090702070603050a0b0a12110108040c03080a120e0123010b03130c05060a03020306011b17 76
    0x161f417030341c48030001403a2524003c18122940c200141126030402c2c4d02100c0782040e42d412400280c0d00c00c107960ba006c5002c1320103446a900540d58050319080341c20080404603d09900c0d1901060700c0c2001104440720f64003240c05200c2c6410903d803d03991016064401b43e401013002c5000203103415900d0030444807134030000a6400301c42c2459420128000450241621240c00380025568401040303068210140c81174406401c0c100030007551030701c0510401c0105580c510102d003003070340c59800c440e8040b03c001300b00700c4200d034458030101340c0304498402c2102c17460768800220005500900e02c003031140741c102e004182e215141d43c4075803116500c48403012080251040c034801c20b060880c468074044c60064000051425000040340082040d01010001440740340300040040010610450303a00043c4590104072040c0c0c00c1c0b4100d50500ca040d0010340d401140440c003508120341c50b50107036116480990321071414010701409102c00400a40010303081400b020026994110401c2c010024510006035868 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 247267302 1250 247266052 247266059
    0x52511010b030a0623100b0a020307050318010909050603070501051b07031104060608090c010e0105040e0f041e02030a0209090a080c01050117121e04051216060201270c 74
    0x207040800114044901980c3c407180880e103c80360904036218010710545c0010a41840300c000721822501e841204880200001c100003002e00c00d1083d906640e81c00400c072915004011080359150b0320540d000c5000500c0e42000280381d1502d8040c0c50700641014002d490864201001102c00c1e81c070140410802c02d00154114002d80302c10000e1000071801204100001c0c1055000c001c00d40b01903a0100040200100038001400b40c003190101c101c400c2403c02c038203060007601c01030703030a40559484084107210f10410042c168000c404418400ca01c500142c0e480c41c0465507070504440c548280103501a400104048010b0402c54482e9410895040c100c0300a10010358070602c1c00d60007400d4002d8035035110801000600260301c00500c40e4816400038081c10f10840b890020782e8010001d0304084030080d0310341204030802d2601118050b08003d00581506540300386159603903060025143c009695070070001031301e01d00c180709040c9401242000d042001c001d040e0702d5030000100d14400e4580340070208000 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 247268552 1250 247267302 247267309
    0x10911190e0418060b10022404210201050109061203050a0810090e0a1202010b03060a0f0b0603130b0105010e24040e09100c0c0b01030b13080a0e04052511010b 70
    0x1c0c50a00e106801c0410151600802e0182000c28035104500b95800301c0d0300c5402343e4400308403c51032080b040100c0c80c1c955071542803402d00381c80048090004202c0000114040716819005035040c4c4554200a01141d999503066014020402c000580050004c0c080c0c0d11145114541480d000a040328400030001d4861110900300c071030026407481158001820b40c01042a20f0020004462040c0000c20018035001d0101e501c5840c014402013410307a84001c0c1003960512070f804403c104601415064907440d007102070243e4542401c10580301c002500c0c00010b481d41c42a80300e25222680501a0070111405400741d82c5011202900503c80c00380a00c0003144145154243d580704000d110000d004040160321000110750583d0000c400304010100108003040a51581c207045a5010030040569076a684201c1031090f84510024140c1d6800940750001c01c1d4048103000740304504540411454030fa4aa40100782810800c280e181580400b50b40203500f4060051086200142030001c601896038a001 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 247269802 1250 247268552 247268591
    0x30b07080a110d200304050303070c0f061122060f0311160303060e130803060f010c0c0e10060903120e0a090608070e06061201140f06070803010911190e04 68
    0x80c190382e0341421654001455013002d00c45207411035444c42c50600d5110703181c813844010508003d1003940c8001004010f81860305407440746d042141045198500082c264440c1e000b03008008070070b002c650590030b8203a0310b54000740486a1903200d1f800d03420001c1c1f0040c0d0140062680341c4401510512000c050031032115501c0f9055440303070760000348050405140d0401c41c0d6010713001c41c40c10081200ac1c64001a944001c8a070810360444620710f00d4503204d00121100d12801000611403400d41c0c034009072903400d402e44039005101d9040c43c1480306440c1e00c02200e0303603841440302806000031420340144031400340e400a26a688041c1502c8101911402070300240d4455500c1130159074440300080003a00001c41d1125040b02c011501c06181c580c07045540c038414501800f41900ba0808a00208c00c190b0324a950411000c501a00c090303100d5403541042205030b0002d100c1d081015080c4810b030f0030901010000c40b00c0d8005051079140e4040303c81081200e03102c5003001c40c240c0081da10f07040500b40c070202015 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 247271052 1250 247269802 247269817
    0xe01090b0f090a0812040909020f0402160b0105101b1b03050d0906050a08150a050d0b0609060111102f0c010c05090a1814040308010303020705030601030b07080a11 72
    0x142c0c0e1110390380b00780881a0a90382c048200c0e0740040500300d170000f5494085408030b602d84a004101d0381810700020300c00c5a030000b0b02d03d07403181c400942c0c0300a004036418101d05490103000b41d802141c1e40d900c20b01040c0480d181282c0001030242c2c000105c60306280e07081c0da03240d42c02020101c80404402456a12143c1d00350400c0d070316035000c2031030102c030180e109450001601e900d2130001d080080107640a04140e00c040d011010100700020141034907180c807822034005100041c1a000c0441503030814a0110901340c1c0c88900988101d000611154081d1401c03400103442d19008160040400f80c03514010005400e2456860055101120000300708400080718000c0c0e07010200e0f034130200e07000c3c620b003110461003254050000501c4602c0c0f05554210440040360802c8407429110620806d0390300050a4181148400b40c5524080c4010316030300c03400d010706036803083e000c441d5115121002c050340d84200340b0004054462810000c1c2140d03102d0044a9081440d40c68040b40c2c00da241d0845211075040940c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 247272302 1250 247271052 247271077
    0x20412080309070816050f0118180e01141f05180115080601140f130803030103030906030b0904200310050619080d1404150801140108060108070e01090b 67
    0x1c140040040e051120400074961040201104400b5000c02c2100e0000c40c46540e100d2080d900c000d0320f0a0340258092107440030149400f600c244d41782c940d000240214002d5002e1380074a0061030207032003c81440382d402085507008107826940d462110380c10350f412681c41d1031003030500c42110004e00b58450030441240008180c8140365250305010908501079451409030003000300601c140701490b6086210a42014070b402c01d0250740300b800958540b01071041010b00031910740340d0303080080e8500010000d5810780c2e00c42d586040001d070355120700b00c0a0356400cbe807440340d002d800c5202040c001107207010240081000300c4040c141c115424800203040092480003510840c0d111400c00045203081e03c09080c0700801c4116406000f8282400c2302c0d035841002d0710b9902441003a00d0911140c8030b841041e140102491800300d24001218500146945400e214806050362030b4142a09958002e900c0326105103810381d0f032140607a513100340440c2e5014144c0707411414003070003c030003245034040800100b00141104 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 247273552 1250 247272302 247272307
    0x72309180714010e041e050a0b06040b091207030b010b0a1709060603011b05030432010c180b1c0f090b090f070323010b090f150f0105160602041208 65
    0x24000584000d1040d03004c03920031403801280420320300034060079000c4c031060f01100083c0740d80c9400000e001040044541d6a12000206000509000f00c4000b460718800907928510f0202e000540155101540d01006000d00140c0e00140018050600686104e44041c41c080380341d4401180844007800d015254001d45421440400c14681400d000740d44034000312030100158483e803160000e1039404050401451403000c0b9040810100c030b04100000d80803a0400072a04002c45400300600030580490302001080001d80c400d016454001e440d00203c400803260f0524080c0c00c010103000100ca00d03103214440d590b80b51700d1074032400c419200780d9008602c6204e8007403850401d00d9009103042703075040706291030b5400341a0038000a00c0c144080d90002d032881203c002a0001544401d01406202007460303040f04508c801c00015481e0412024003803490108420b00d00c2040400303001c0c81d00724291107503020031000c02c55100c045030307001050b031540c13400f075a00142001d403240c146849241d000241074602078800f = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 247274802 1250 247273552 247273589
    0x40c03051008030a02250506030c070611031005060304020a03140a14010e1504142415490201020f0703030c02060d020d05010b04080723091807 63
    0x11841d040142584078020360802c00d054a000307650707003640030183c805408508425110b01034a09000405028010714182c1c40e880c005000d102c064000d01c000f5681076051580f8803540c401c03210112809805000c0c0d03007160315400d00d0144600c65001400c12070308001c01e4040000440e0289682e0304080a100000d415081c0707240c00c14480b0707109180000c6480c1c2e45000c1e0800308c0c0c9200020a104445050304002a440d41c8904004000c1c2003800c0901000d40030b091041c80f0001c60074080076201c0c241c2038840c0d90381c0f078032104201000411700c4004240c00000c400f076082451902500300c840d080002d0380070f0206884905418100101d070415460b01412041448041150303014001044d24154500040004603d15180100342d0070590318043d000304400900310740b4803062501100e2220084060034002540e550020322032039441403040f60024040d962000c600c40170034103203050134090102085d5466844110411107035540241c094407121400c24651002e09205104041c000c280000000000555 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 247276052 1250 247274802 247274821
    0x7020c0d0311120906031503150c192c030703050703050f0106050111060402090a110a0e0a050a031104020f091504030204060902070f0b0405030d0905061e090703150b040c0305 77
    0x24607540180c1007083c2400310342d8841d1504000e40c1e42c0303c5040040039040707010303a001083c00d040e030340d2241d94400904982001408907500c0d00400d906a102013901c20041520801201c4040105141d0105015500055860103030901c0700d4046250004003941c1540c0e560742d0341d0514083c8642c0c000c45507a0412007540082d40e00a02c07909009203000e08140a0000449070015115000100020300c0307016031a000c242d0f2001154004103a16030903082c407a6481c1d0140070003810b00700c1c808001c90b10035400c1c24004600341c10128101c90440c0e03441840100f28048460803c03010350000000e864803003000b07110b413501542d12042c0f90303015951a00d0149664900b1801400156034035508456003c40c010801c0d0400103200049052400c0e402565200803600d451074402d0441c49903072440240c050030000b03540b081c0040812442c0c06000507602c00180400a40c0c11010100412a0307a890b56402c03d1302c040020031011001c0a00e12419880c0008142102e032000404407552448420006550f860402802c0003 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 247277302 1250 247276052 247276063
    0x318060608060f01050a06030e160b0711040b0f040b1c080a08010501031505060703120e01020408060906090a1b0b0d050a2409020d02070c032a0305120307020c0d0311 73
    0x2051410140b0f115810711000c6141000c5a01c2140304041d500c01f0140d800400a0062808400c510302500100e651385528155550704000800d40d23a00054a40300c410b00e181512401005080240c02036800501c450100401020742c1c00c010b507000f408400761054150301080b82525154031030000700782c50b088504002005010140c11960606203040044910000300c000c40c0c0e021618102c550701da60780380625045034050200c0304012031040c01c100c50341081076410340140c42500c0404044074072503034488680c00e070740345401d03507141206401072801e44002c151070102012104034440d0680700c416a40345400002d40e4080460800103660b92014040310441c1401030b494011109040700c2508244c1242a6a5104191044802890380003450024000e4260141c1d908181c2003003500b030445540c2c2c24068208c00440e0605565489203022010321504000e00c0007055980100c02080030806002800c3d0080d07001070030080561040c854040340f240d0303a5120548406111307590f500002c00c0c0310104649040b = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 247278552 1250 247277302 247277311
    0x408030f010807030302030d0b010e04060b19212307020c090f0412030c170c121608010905040f0f0312060b0a050313020402071a040b0c0906070b0403031806060806 72
    0xf078115040030004694000161008552a510005907285007840181c8110009403d041c4e001401d0850028a902500d0082c1c1180c0550850700e01c10302082040850303500d400400142c082e00c107643d004540c980425840b8038858620042c00f4010000c400341c1c00210103204880040041e80500742c038041d681041802c40c0e8000107900c2c0104840c2c00e00741d42e81468182140164001c2540d00c0d11045400b91003000a52800340600304c00755501d051020344489a580403582030105281d40c58003140c9e10404410022458130010341d80d00520380d0030654500d010344400740040e100407143c5180d05020036440c8480181d000d1098440c03d501029441003c0c040d00c01e9607012420750309d010300200305141c8e008412a503100b034403094140441040c6100240090284020143c11186080c40e503044030381058011034041c030b000c0d40420150f5920240140700a20848c004290040000e000c5400014007800b03900c7d4000e0f10a003004546038180000364800084003840954141e500c80d0703000c1107443d20510406411 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 247279802 1250 247278552 247278569
    0x50f010806030604030305070909090309081b061606021c02090312030702250801110703020c030106030804030618020301050a27020102120a050405040603030905040509060415020d0f050408030f01 86
    0x81c500000043d0311401d005001405040e00e820004401301d1041c0900e4024091140b02040302c55403c0c10300a0148031036000d0f2056901c04d03007405080640da601d0421a09010081c43e4a282418400b0444080503c1c0c001c203e603401e409004d5a29880e00d00300d000340c001c990400700145c070b50103c0020140340c100d816030200041c038020000d100c48964003095002c0c021940314280a405507028841405d41a01c6511000350395182200840e006003c2c04000d2840034081ea08490415016070101405c8507914800106120400c0100b0800269250040703498220701c142e08400b0000742d60082800c6d80c03801c50b4421030b0190781d40045c000085a840e00301403d80b04800c1c111108407031720790010356180680010b00d00700d81d4012400402a902c214112006404081c206104441c0da904d4007400300b02860041500c90b0b4200800114480c2002612030f2103a07421020641c000100401d10710002d40c00440b1490606803200a0409403010a005207030007540b061800310780e02c2c43d20075076045030f101c0d0603005000c0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 247281052 1250 247279802 247279817
    0xb0a030b03160810090203160602010504020127060807020f070807090e07050a03020402250f0b0c0a140a02151008010e0609100513150e0106090606021221040507050f01 74
    0x1030707030b4002a0a05003284d000000007101c804a0000901d0218803200b1684414000240410308c1607040d00460300440c404c2e200c0703400d281a10b0751401c84003801080368103200405458100503680c412850719401c81a42d00540e44c1c2c1d841c00200c014206409a00010440c0c0d10040d01000606150f00c1080c1c944044040030305102c0d4101000105150311505c0068400c1d600800c803090702ea112144442da0942902d0092080c1c2586882c0c105000382d20240241d52550340b580c000745484000c18102d0361214469510038079400c40c031401c200c2807500305413100400c41c4165104040c80d4520700c080c0d14043c080c8090494620352804211500b550040419640d0303a80100d0140085800c00040300100c412080c6c1c404115035075032078210082000050000b401c0014108081541d01420307070b1007000c803654090000d11283e81c4130a0148255100e5103d04801a170250004961344448000500030711481c3d09050071310700050300b141032107450041e83c0c00d8900b90400c007003c101b01d142c48505142c040000b07003012503 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 247282302 1250 247281052 247281059
    0x503090c15091f020c0f090a0504020a081f0c050723030d020d1a01020309030d0309170304150606020f07030303110c0a05070e060a060519030b12011d0a081c02040b0a030b0316 77
    0x47c0000c40140081c1c5000c3d48800100e001c66a501d2201000b40030858100e5601c0110468510700440014074041152441c0c02180c1d411180302c1d00403208081c4e042641c000228a0b4480c1e15001c2c00c4040f5820708540c0414001100024082d00082c02e18440e859000300d01c82440b4203c154041c0c00c461a0103040d54800c01201c0080e44020a40c0d03284a0f216040003e07204c1c42606000301c1d02d002d03081840040c111300000700010405150f030443c042100e00b14040002680320441681d0f00c00720302c1c4d4000a10380c044201040044e00c241c003c1d03207030b0b600c21303100c0241003100010741c05151002e90142100c850704011018000000e4601c01260b0000b0200d131f9200c480d901e071140242c1070b4841c00d5070708a8010014040590583e000780c21466052001508400c6510f803107890540c001c0104540200a9aa0ba20f100c400c000c0c60000e0309110321078000c10300da40741c41e0400b461840360b0205141c450384059020f010000e080b802540c081c01342504991000b2a41592010416040200900c4041000361201a090 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 247283552 1250 247282302 247282309
    0x605130b10141c0f0b010e0604060602120901020312040821070c110303090306040809042306190f060c0605012306090a0e04210503090c15091f020c0f 66
    0x280c6280d042600c0f051000d00794200b50388648000604050004c2c4032039260f11003086100ca0405048401c41074002d480c40d1204403c02041e6180c07441180010b038452509040640701000041c03550b040140112482c20a0000c81000c03204000c4506451900c1d0120300703030702c82e10080c0810f446021174079903031941d46140c5040050100c045051000d09205441100441c185d01e00f0400c85490040080c200c422600e001e00c1d000d61f695100740c0c2942d018505084084198a0446c220b1810510210600f031815070b45001c00d01044040804507807441702e20901c40010f0880840d1000e001034115541d59200e20b010fa800c0c00c0c01915010b9020010400d11040f0711543d545010aa5000780c0718102c03400d550303c10380600021080401038004040303040031002488104000f00141024142080c0d00d004680400200207640501046440c00c40c55088062001c682d440c0031003d00141440d05640c0d14141343c44000442c0b0034800c282004010010400c0148540e0741d010884441480030032a500303184000e05030b011 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 247284802 1250 247283552 247283579
    0xb0607051507030207050115080c010302070c03061512060b0118030506390c01060803030c220909031107051903081b190308100e040b06030a0605130b10 67
    0x644410000400440c1c5940d00c82c0d0111807172150000000d0042da82075800001c500304c82480780050b0b0348240483c080481d4040c2c0292641d03150070004c00c0d5000d9286845580140001d4203e01e00c8107601100b022544901c07084c641686503000307000005a40101100140201c04021880f03c1c2c030f01900141000002e8000880c640e100340e20713220444809047d4603101d1001d9403405c194006a01e1010701400041b084200034248070540ca070000d2203055510b41c001502ca110958107809118001c0081e450600303110b2001131b4464000040007030301c0a0b55105400100d410000003100080d070607440343e000010301000b106000c0c1030121007298009400189820014100d8800142910004a800001091001c6100240071081c9003550141f0102c086807144d421039044d000c8020401d25000b040c007000d441c0c8448006d881e20101550810707141c070341310180c61000c01800b03982d06100341c2800000040a03405454055a0808203500c0b04c103c4502d0102000709004100c030540000710b0004202c0700c80c1d003640 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 247286052 1250 247284802 247284823
    0x302090112141b09010b041415090301020f040e0a0605031b011115070809030f07033005070e0301090b06040e030408030a1d18040b060d21030b060705 66
    0x9640c5031070341d161420540c12603140c0e00c0c40c007141c000d14003014030080b424400060951002c135600c001c3c50303888101d10340040c0198002d548000d10300341c542c000c0d24106060310090a0064550503070a00c6174640c0002d00f0baa002841c904100400030030204081403a20503069080010900140080b40c20403010030340d10701220881c0000710704040001003840c0d0080c143c06080a46410075121040c540750b90003209040c007518070b20001042c010000700d82060100a480700c80703108200d01c03807a000007510111900103501c411040082458002c3c92940880d40780715552581580601240a140c6000d000c0c0107407941000b03003406030b4101040030000940c1c241030f00f54000022640012410a0281035a166000366009458103220024140b00300301c0d0042d200180000c0300b420b02514a0130b40d10184000205d028008081d100041d6021900056404c0b1080c1d60019000d0070328402c03200301b134840c0030342180d4901403c542d0078000003080490a5060003010f942d503100762078041ca00300c92542e0b0150744640840 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 247287302 1250 247286052 247286069
    0x604050a08220e0907060908120a11030d06030308060a050105040504021305030f070509070c05060f070516060501050a0605040e07051e0c06060f01021b0906060d05070c060f020403020901 82
    0x202c0c00c502c14080700c10124030451100c00101d1854680390261036500080d2910748913841340000010358544504000c80030303206c03820090041340c03000220081503a005404c806051294000903916101805c00142022842c40100810b06614504000e0943d03440942054040c005640c0c080c8201e17600a000c99040780d10660780180d070341400030050380761214181c0080c1d5060003908201c0c60003180000303410043c2e80c003c8a0740059501c0d80b000a803640302c1c06030002401500840b001400580d0340c1d041456124519050052400c0c070076080e110a803900315541190042d907a0030046c4201d05200704110058902810120700d041d08212030403600b407000610f40300400c0340002e44081e40d030494000d081e0110a0316801d032515119044a0140c0f100c1d803ca48840c0502140307440c43c403481d840091241012a805210954096208024026101c500404e880e41240040040c55200c0d51148039040c803d25441d40c4204441c120351a00c00700b03440c0000d0f1242d80c1280148020710160340c0703010b40641110b03a5a03 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 247288552 1250 247287302 247287307
    0x1020a030e04090c030b09010b040221070e0a060c0b0609151315030b0402010f020d0e100c0209070203090a090213060806010c05070602031e070b060d0201051c0b010f020604050a08 79
    0x9001070082c04048600a084e210248400010082c0c0017411602400418000380515801c84040c04200d005030450542406000c80e980b1200100510249800c80301310300d4941d19900c0d91340045166032803968010380004080c2d602e044184880881042e4202030f00311091407072818214401c8103e105000c04581c81103a0845050115a41f56440741d000f03102d002d41054031095417410b004443d1682103e00741e02040b00403120503092840420a01c01c5240d0310748800303a054010509102d000d00400d00d0031818040c90301540c0d0003680da04c0c00914440c440070390045591b2581202480342031404d90340626290760060000043c444044502c4406460b000d140c800c010b0365400c00100c0784e005100001400500030110046049540071008110b0340303a8240242c2d80f180c00c0c0e0801d001d424490440051b0125a03e038011034018500100c40d4950a401450103134180780507801542c0301c1c81440d00ca5107001998a5154265550b00104a0251082180050302061516840340342d1184582d80c0e00404082c1700 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 247289802 1250 247288552 247288577
    0x303040515120907090c0203132c090c041401080a0305181225030b01051c0b0106020609060703050f0a0509011107240e0d210c050706140601020a03 65
    0x94042d40d80c00300082094900c941803090400d070b1110741601644080c5820300c19001a43d500000c01c423940c1d42a40708481820701c0c80c141c101e9004160b010080ca82e10343d44160b030042c01800700c030707240d034096070822000c4d008103445c290400c0106e64051a02158010859004101120300803c2c0249809c1d0107042c0181d4030905112100b19003a82c3c0000650f100c180264510380c98100050380d8a0100c01c5101207850340750380c1c0400c070a005c45851000600341c4840c00018081e1341024000c0e9049003c0911290300305036595640c1e8400f40d00260414001139000c88100300c1104030400103140c0007500c07030a041045080664001d0760071032004201000143d1540003284481d40b09506c01410007011f4112941c480341c1c14604550101c40c43c44d02d420a140781c1c0600320034002c106100c0c0c410001c80b17090091441d07070f031290401d68058420303001408015400031004402c54105018102011040360b0f10030740d44075002c0c079144044401da047d40185481d01c03d4104011660001100d41040b60913080001751101c2 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 247291052 1250 247289802 247289839
    0x102070b07030c030c0b010308121008030406030908120117100908030609100b03010602030c1c0903030f0c0b01141e09010501050c100c0f0f0503060604050609030a140f1b03030405 79
    0xc4450004000d006d43c1000041401462000b03001307121800080c1c0009902c6a20b0100c1041c1000d015000581d00100010002c80d8002d40c082e1a034948541e08180c28040d440c03100100b10203090f4098008010f80e0394007003510010030300c1080030422003c081006203c6041d103c0340a40e0200501c2d85010307205440205a46400016003c8010925440e40d00d94039a16070380025220741022070101c03403038883d044402c0d4240b107090342c41d41c00f402a655130b032402481c95034400311102c030007080c80c240900036981d020388040f0b0a51900c00703020b07002c66010003816004040034000d681003180515940c0030440410490705aa0b6448020f0449900740307001c50700e039140d5203102c504000c0c0000401c640585805ca03520b00b0b01d5048a190300c800142529124000010f034141070300c452001301c880d198030000402c0180241c0c03601c04c02604c804e800140444440314040c0d501e41040e072a02950b809001e51040281c41000700c0100014007501c803240003444250911003000c65a2401180241d51141080d10f990710311404 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 247292302 1250 247291052 247291067
    0x10207020904080c0c010206010b03040308061c20011107060807121d061b1c020c030a1218020d080306030a051203071815030908090406090e07050102070b07030c03 72
    0x54000303100c02041c2c142858020f480e640064088405405220494800d40d0b001148290480e1520140603103940d0b03880d501191410b030002c0c00b01ea800420406d46d44c410345105043c40c4415403042c0d000149000820034003601d0a07800750340305070421800c0e05621180306008680c0200711016402c1040854562410036254182141c00c0d44681515144104c004410300b41c0c141841c2c3d00b205405c0e114952a1282051900e5480c0f0a40d40c0d00302204101620034a500032140001c1c0310514000103080500c10203505080d41d221001c6a000901c00c2441c855458100e0f2050301213100c09401d00030b41e905241c0d07010a49036100280080c104210200000b03140340c07000e200300c1881d1a0701005880110b40c02035100c0c5841c0e0400e4920030000380351411201d91690740b0800d42420b0390f03851020311140c101207100460203092000802c9070b410005000c03034803590720340e8010380380a418503070300114100c640700441c1d5251414070303404281158090306041040c8050401140d18090f0945894030952100382010390300031 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 247293552 1250 247292302 247292317
    0x9010c061d03070204050705071e1e08130503010218011209021f0e0906090c0c0a08030108010f1407320307110c0301090507051e040e0c01110105010f090e0102 70
    0x4007403580c2914001d5034040024120039100310740400003034441e841c0c01c8540703000e070314801031500040301881d64000907840106401548100c8813040c0348500c150420502d4001844c0448035104040b601c0350288004e403440c007018000582c0214106004810022a040300640785036051042d0f1341030340b0307082403213980000b00e0181d0040c00700780c1e0044504d20390850000320300031050300041010f0303020b00e5240b0b890251503003d500c0040c0003504684402c40c511a455000d03040e1102c0d5442115684c0002070700d01c20195000b032002c40000242c8120400002c81580c2010880c2a140504801000b8955420402400075a1200000306c407001181c036942e0703128403680803160044440e01100304111035a106908808212059091f00c0101d00f0060a250aa60303008000070082d400000051106050034203198001120480340a05091408030100302103078512060501c56400480c60801296000300c1d1408594600350700800481d1b00d80400d911809605008543d18141c8440e021381c0071107825010758494 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 247294802 1250 247293552 247293581
    0xc061206090c08060102060a051608190c091a040b040b0c100504080322020a051314040803040201080906072c03060a061406120a1805070621020a0509010c06 69
    0x4510a108020745000c008132000e038018800c0c0000a04034941030b000744c500407040c4514041140320412015100e81c18011300d801490303612807a00720b10b5040c0a00501c0c150b59066102d016281c2c1c104581c000075410307008045060301008100400c258001c40d01160101c034041006203413900e4000100c1030611030f600d1503901f074041c03c140500c0140048500210301031411108000ea0348088061100c1080c00041e0000e507014076961810801403c20f04000211034040c20800075002101485800c1002c00076101500d6201000c0204000c55810030203050700f249442d002059103242090000713003012803541d07103c0403a00c041d000f5580352010740301400040b03075401015a03010b89030001c02c41c4014141407255525000d4011441c0010382803040807144842c492183c41c035041e0f80c680f4107070005445103e294070708801c548018040807510900104d8040c02030350fa83d4030541680000c41e01c541e0386038419280d103518410054000820f40240031181c80c00000e00340f030003544050381000c03401400410108181d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 247296052 1250 247294802 247294811
    0x5090c130902150a0801090b011416170d090b06060408120906070c140406140307030609050f0d05190f0e040f0e030301060c0201020f0d2003070f0305120f040c06120609 74
    0x81103178100800c54141d4801490811403010358000440b00c03078000401250094808121000300c41c84920390005005000d244c2c0030000c02d000c0c0e42d4141c03140d40102d00d4145131a5a500b40700d020402c0d58248503410180403900941401d081c07425054aa07100004c040071491000140200b058540c0e0080d580e0b52a085000c4004e079954605440c0900e5490815061150740ba1081c0801c80309106c844034000f040300600142055400e40d030310302d002400c3d030345000e03111445225080e1000c40000c0111640320301d0781d51307240c64556040aa200c503104180c14620703028070100344041c594841e8032035450306007188119400700b0844604d0015100614880100b048680000400455031603006000c0707a40c818400e03422103c9010010035040d45401c408800480000c011284054003410f854115080c40e44541094a04c4d008950b521f40704a1684044210045000403da00c800c4040d20700c802039000140c0845101a46003507960902007200038010401403204081c4042c0c40310080d640b0281c090300d000340d030420 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 247297302 1250 247296052 247296067
    0xc060e0703060b030d0306080316060914160914060405071701030c06090f08030a0f05040b04120b010501020d02120c0114040c0e090a050a03033303030305090c13090215 74
    0x10007800c103e840c42402489080c5580d140305100b071003528100c4030100e000d1810000c0203818210056030500b0141d921503103d01041002c01d1602c40203159291040d0002d1021003503aa01313506426055600000e0a02d1404003c40700744011118030b40d5100f00100d900103016552142e0640b004446030751b903008220711200010041128144008054401c5901c0d03510f0005c6e40c03104c0e4200520403074046e10700550010721544142c42d0240300d142c4100c9200d4180103003081c0e1503010300710f1b264005500c0803a030703450f2b031004240600c000319050304c1c00360a00b80f002e802c900c9024180a543d588040320302c42048480000c0041000c1c030294020f281020380c11500c6001b505160800c000c00204500514141e2900180881c105010004403c0320b501e9001e0040c00d00c103111900c040d0028003040703140749070145940b03210f440c1381210380300d81d60005400012042c00303050941c2801411118000d21b1049540c0c00001c4030340b000d036a070803411440707100828030100c0c450350f803440031811140c1c00c52801c0d01030781004036082c0d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 247298552 1250 247297302 247297313
    0x103020904022502090c04050a120203010e1603020112060605090d0c090c0309150506010f0305041502030901021b0d1d0607120914030705010903030f020a02060c010207060b0a03050d0c060e0703 85
    0x7512602d00844038158140c440440d41c1e406e40c810343c07144540c01403840381c080115a0098401d00d40560004000080c9404a00d504034141031100b42414010b1841710300c144210340e088100e03602c44a0205e074041040a040c030341c01904d0792085050f92445804442411001c010a03e4030140c0586040c0c0d4092207100074100014001d425079100c122a03800c2c803a150701040f450140708261244805950301d541c0c00740c0206d400d40003860090400d44103900d03000380c3d403005041140011401504200001a911040341110f0300b03180c0e02d42d41c9041c03000c0d0400c203480240346502c00204107440f403160403250601c03d00c12000508a04c074100c80105000748113940030446a802009070400c65040080125444d039080c01019107944082c003c040c0407445a5a003072022900c9601034001e9041b0310300466904010b01d40001d60345400004c4882c410b80e4001510400300302c22801460001402030303030030001c10342c03c0d0341e2415151903010310131108104035280d00c1010310207607800c03e02d6483c0314003065641154890904 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 247299802 1250 247298552 247298617
    0x30a080a05040e060d0305030103030c03031413030314010803030a110c2407030204150302032e14010201020c070b0a090e011404060503030a0e01210501080102030108010501170c010302090402 84
    0x1070b0500d000c420000510345042040005417601d83c5030f51814034581c00d680c1c040d184440710340c5d0141c081595031096403a05011450340c0d18001c0b11901c09030365080c5081d1600078103a50b81d0301d0415891510240c01008158000419203800107103d80e404144008041306101240c000c1c0030b03000481d440741d46000d021000350b4101ca4103080d4000d20b10300a40d036503141401c0c3d040e803041c3e20610301310600006810015503c80c0e800355400c65051030101200801400c0c141c1e40a01c54411003540191501d0303000c00400040710494002c04601703000960a00c1180e40300280c644032184141601c1180000d640c0c00604d03c51755040000d080882d030585040c0d61900c110000c0c042d442011103002e40e28190001c039007445e002058590000e0903654203541c040c00c05004440c140e42408110203003031103c0120940e003c0d40b42c06040e02074156000010b860350324040150303094841c1a0322070101b07202c1007061062010804140c0c40d01e000020300300940c0e60342d20400401d00a100392070075a94400380010225000c114154803 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 247301052 1250 247299802 247299809
    0xf040e03030f061008070c03030207020409020402190807030c1e020111030103031812150b01050415270602060a020c0709090317010f0b070f0f05150711030f1602030a080a0504 77
    0x148132a400c030f52082c05072800142525035401281d058001c0c8000a0320030307001803100600c06800425400c0035175004c6010f0360040c1c011701000c401c020026548040e440600103900100c0c070301e014003a1080002016000c50043d400b0322a45064101d0300a02c2c00c0e000350082000c03440c10f0300a450f542d60f03590078000d05000500b0000407500e01110000542030f40c030302054140a40d00502250b06032030641440b0401030106000c6241840418400003903e80800100300c030719400c05882d403800d4000c10044112801da20103c83c0094008850030903c0580c2d400149180e00c91085100141d541014052051034001309500940c056400e0440303490805a0000c1d01014150240407a55034698071003205134102d007150f000741c4041c03010601900010401c0b41c0254600c5500a0303045038400704998a8013414458104203400700071035944d00340a40d00b6842000240c000c102c0750051410070020400c0c05050340f244a14094000300c00100700d4055540c10b0065540041d0f004117080d948048101d40a0b200790090320 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 247302158 1106 247301052 247301059
    0x305240628090e01060504050f040b041403040324091502090604030b040c0503060a09020616241b0e0a03170708040803030115031401050f040e03030f06 67
    0x2101c007024140c21000070805181c2e0702625070955000d5804640070b42c1c40c0000b0441510881c03a00c85401580c4440c4045850b1140c0c2805600c080900d4101030460000003000010850400104061006020180d60a40d2005a0120101d0b20401c10141000304820007040e0320002682c005c04060760010300d62424580c598990a649400444080700e0200500c501030110749010880180e0011540708280413000e450360104005010300320800413100c0ca251490420403100b240020000e654016005800200c00707558400039000f403d5000003481700070301c100320065101d0b0625a01c40440504003c54140c516074030856850981c0004131200c190610500c000039124000410041c44014010b40e141e50520b005480d840e80c98084c04402d0502e4070403d11103a922540c0403d0450701c0480d801121920b1801c0410080c1c007951745a5040ca002c00402c128603000d140380707128004d80054 = true := by decide +kernel

theorem cover : BRFrame.Cov 247122302 247302158 := by
  have h0 := BRFrame.cov_init 247122302
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247122302 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247122302 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247122302 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247122302 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247122302 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247122302 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247122302 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247122302 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247122302 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247122302 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247122302 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247122302 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247122302 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247122302 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247122302 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247122302 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247122302 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247122302 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247122302 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247122302 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247122302 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247122302 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247122302 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247122302 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247122302 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247122302 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247122302 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247122302 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247122302 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247122302 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247122302 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247122302 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247122302 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247122302 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247122302 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247122302 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247122302 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247122302 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247122302 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247122302 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247122302 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247122302 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247122302 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247122302 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247122302 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247122302 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247122302 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247122302 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247122302 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247122302 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247122302 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247122302 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247122302 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247122302 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247122302 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247122302 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247122302 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247122302 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247122302 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247122302 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247122302 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247122302 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247122302 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247122302 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247122302 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247122302 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247122302 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247122302 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247122302 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247122302 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247122302 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247122302 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247122302 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247122302 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247122302 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247122302 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247122302 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247122302 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247122302 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247122302 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247122302 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247122302 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247122302 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247122302 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247122302 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247122302 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247122302 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247122302 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247122302 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247122302 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247122302 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247122302 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247122302 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247122302 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247122302 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247122302 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247122302 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247122302 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247122302 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247122302 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247122302 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247122302 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247122302 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247122302 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247122302 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247122302 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247122302 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247122302 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247122302 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247122302 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247122302 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247122302 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247122302 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247122302 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247122302 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247122302 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247122302 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247122302 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247122302 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247122302 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247122302 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247122302 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247122302 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247122302 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247122302 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247122302 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247122302 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247122302 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247122302 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247122302 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247122302 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247122302 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247122302 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247122302 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247122302 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247122302 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247122302 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247122302 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247122302 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247122302 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247122302 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247122302 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247122302 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247122302 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 247122302 ≤ n) (h2 : n < 247302158) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
