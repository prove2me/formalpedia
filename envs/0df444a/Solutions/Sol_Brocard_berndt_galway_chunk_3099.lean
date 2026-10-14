-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3099
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:39:10.111454+00:00
-- url     : https://prove2.me/submissions/c207a4d2-3da7-4210-8ed3-2c61250bd364

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 557194244 ≤ n < 557374100 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 557195494 1250 557194244 557194271
    0x1e020c030708030a18290405150405100f0f052505013306050d090c0e010504060e0f061207120606061e08040201080a0902030303010306090b0717010e061206090a0303 73
    0x8000c0c8107441c03c0482003206d40c101292140c00405640c031582a4007403a1503960408079540113145c40c02d440c200507010408101c2c6040043d06084240303881c0c0f5000805e440100005881000040c9000e0100580400c02120030400c0c4201d0440300410f40844082000003850514041d144a0030816100001e10f4070f0401e20f4680954444108144c81900c00d503d0360501d1411a8190841c440743d05045031103014140c00300e0ba0188a030000f41c2078a034041d100a604180034407090b100564401c02d00ca6254400304001ca6034402209a001801103442402c0c0545003540c4a1a08815420603403210f44000a60382c200401d5900050485010381c41e4100c241c0d800c8201405210744401008001c00c01c580c00040040d072052110542c4a03940e000c000a00c92a184c001c249150000d030011204c16548401c2c10041c030420800c45070b48142e4614100380481c00411202e0580032040c8501002c481e0400b011400700d5403801c00400d001c003410402c81384540b8103140429500c0c1c0070f080065000c40e1500c0062020706 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 557196744 1250 557195494 557195537
    0xa0c050306070816200f0613020d1223071109090a140304091806060b0313120212070f14070b090114040302060c0d030e01020a1e020c030708030a 64
    0x258002c1d296580c0f9943e078401100112100107818504002c1c1031507510a61100c003004215058564500401d6001ca24400702481c0c48005000350707652000c0c80c805c2c88016541c0303059102c0540e9100d1030901580d000c1000a58080105a14142102e4180c51080402880c0c0c080540007a60081c4015400001c0907400e000d0b0315502600c0911141d044070304c5001c01300d0186007041e10701c580070404880c9402d40c0c2d0300c006406c03540504810380d1180c024100c0d00b01800740c0b601800001d000e039080800d2441c240b180202e002000b0b00003000f8004003e018040c82040c1c028403e03407080d4990010440d0b981c0d4003d240084040282d01011204290701ea003150b48440d000040c1c050175201c0c0c1007800b9141c039103040c0041d120603400c60200031001b0070402002c001030710b6560242c04c5909041b4010020309001000c041e05448010180d07604584c414842038070b11b1544503040302e40f419801c16401c044000d11081c124109503407405400c1e01031040c00c60000740020000b00402d0512202e84d1081011042c0c800740e0b001c00c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 557197994 1250 557196744 557196751
    0x110d0518041d3408030a1d06070803010602060a0b03190c05040e03251707020103090b251d010e061c02040302040b01030912031a120a0c050306 63
    0x440444680102400c00754440c0b006042c40c59040300009110507109468070201040078180030038942141040394490b2091180c1074901075600100311400c0440c2c0ba5540c0c05440482820031602070101c81e000b80500c02c03140d901282c0a06081c0c4d0760b05441c2445080742e4400c0c030030040140328403030024035418802e00c40c8540c800c030020068507150348455070400d80c010a042c0c058655504581d000101581c5500c68510b050610002a40d1900011106100030025524842c82d41c4200d5810901c0003402c0300d1000c10039105880e05d031644803c12400124010403200c0c000030302d080c1c20074040c8820250f10b5040005a1002607060b0600103521344000c40304080800491142a150a1052002d540c00752901410468000d00701d9030900c201c200720a25036130003a10440e40c5240d40000d0a00a5007401d01a40da0350700402c1c01c0501059440c0da07034241944d002044000209591795415490b2516072400d00c40c20404001d040201d50400d08041c25160300380040100c50303400c616140094203044c04242c581c072 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 557199244 1250 557197994 557198017
    0x90c0314010c12150e090109060b010f210f0c0c0203060a020702090c0a0513170c090108060f0709081203060a120b01060c03020307020d050f060108070f12050c060406110d05 76
    0x2040080820b0b20f401500d10908040301d21440080701090760840b124a180c0b04151560000c103451a80741841021206070ba45914104050070030765940803504560740e2030f400040f40d64120b424008405092004159101c480c0c01c016041070000309010b136018040e4585a0b008a040c0c503201c3d10380240031802c030701c83c1a1009410944000c001a40b40a43d03c010f0828040141416031600144580b44001400e15800c402030601c085050300407241c3c02006010681101960080074550415643d0399581000400000020340058001104144110003090003000103104991680c1c1859019610603002144c840d40504581280019404031420440c1400c941200100b1300303590801108490159022200354198801009004010b80b40d130100000b030107001e800607140300b1400f0100d460901c01c06074090f8102e90700444007409403110b0010b004080b12408800103211042030f19209003800303600c3c0e6217240d011901042c006070b143d4010940080099442c0305442c61154900700a4038103005644000381c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 557200494 1250 557199244 557199257
    0x60e0d0810051302070221011a0607060b030a2001021015050108070c23010b0d050706051b1605030f03071e0f0f15200304022101090c0314010c 63
    0x219040040d1610b03e200e84440002d81303024001d8000c11000007115070000413440c40070f80b484244050a101c0c196100010816041c1c0004105c8002580e0380036441026104aa60340c40035035030780d601000201851607000031444c42d40c40048102c1012001141a240c0c058003400351114400c4020344100000148102e501c9001031341040011952490020950b4040c8116008848003142110f0071040011407008103c000708003206a0050a45062012550085645002a000081001c0f8001c4152106480e0154035176588468442c03c0580c0b2191010302e50142200419a00000010325000d6481c00e9080311029100460f880390740c0e2040940207404800c2d16051030760309598440c2c1c45114140503d505801c05041900c0e081d41881d440082150352850041c08030b000f00100d80a43d8182042e0381500701e6a1450901c0124010311005000074420000040d80d031004c41c91660300781c8100c04002d80208140d00301d5150030f00c003003145030000707490040565010030b1800b04140114180710031142d07681c4 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 557201744 1250 557200494 557200499
    0x30a15150f020708100510330e090f06011106100b0307030b04021204020906030106060804080d060317120a0605010e0f130f0207120203090d2904060e0d0810 69
    0x7200c0540c454903030601140986500082e40308010001744101942c1540c1c001101d08110100443c403180603403103215003490030149202c0301b4413a52242c200f04001d0920151401d200d6080454842001c6216990b00604c0f10303060086240c28000100c0c8902c40a80b200041031500c0d01c035440da10982111802ca007851001400e11007002d18902540e042503581c00c000c28072480000004007a40c10882200401c42e05040400003586000c0d1001e5070084001e070020006141005401014400020409000d400300003c1c2180a00072650250000f96001042d040d10100d0880c401011644140c650700c490300c8030340b000b280c0c00c40900d108840803208140c41e48040075030b50b4414003030303083d001c454070356030003003441d400c18046016500030301001c6000b800005942d40c0c040d01e4201412110714024508540c420b00100f41035480e200e1b40d40b600a0b810401c1c00c0840100f1b500d030580200d050301902e0500c2c0590390180000c000c0d20350040840221643c0c141e40360000342d00000c4071070041c01c494882081e407204104 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 557202994 1250 557201744 557201747
    0x60f0409023304064a0d020d03050408010f020a27211b2d09020d05090c041a01030e010b03160302030d0302070201050712030902030d0302030a1515 65
    0x282035022281d00c0035440140c03007909003403083d80140c0e010700003088041c8500002030301d6518013800c0d501e1000d0b6485001550001a100b02e4a04030705942c1c00a140328112248150b0f6280300c070100065008182c01c2c408030042c6001000c9410a2260700450760030300104801e060424001d03640307041060b40c0c07103011010b80800c0c5a172a03844000501030100540310000308007062032018100d1008404820fa00032030704a842c01c1b081890001c1d04401411940701d070240005000300078505c11441d0103140c0c8030005844074bc00c81c1110704056006002440c800039250010300001e4208034400e0508106442400201c41d040c00140c4050305940440e070404e04508061646c065880907680428003000050035855041c080f030301c5e0140210a0012411074038808104518080003c40071081c51441c00703609010060b800600b072070150072401050322840030b0344032a43c0f40c820f62040150540060032156032a1007a00060000e61060b140c400c046400c04036500245038018ac030701012200442c14000d03000c2a180e40 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 557204244 1250 557202994 557203039
    0x905060603061c15061401030203011a0306011b0c0302090a1806020f121801051b09040c17041a1b0909061507050d030c08070c0b22050105060f040902 66
    0x103c55200600c112180d4007040c240b034254150b4211001001485900b01030110003908500080c0c6410035004000501c03040582d410014410900d2181081d140c0d111701740140c440c00c245008040d8080114a5160305001440c503441d02124020307030304101c190700d4401449040d02d6141400c220800d0001c2a0180080c8880c0c1c01802c010b40d080182e58107001c00c00c3c0c03542c40d05d89801c0d81c00940d0301c0b240c400558450f01c4288201e0340c0003d110030204406020401200002c2d0084c0844244100d0340e6078205090309029041400b10006086155203007441c20303140c59160410948807184210104800094001c2c065040b11031000c08402c030074a042120090070040305185c001c06e50f5800c0350544000e100c0b914071040140004a10a0300900032445c01100c0080c203d03042c0385040000c00a0301d00a01642c190000c2a10608035048070140020707960304183d42c6000f60418240c030740b01400e0751b0b03800c2060100660145005500841d01d440c0c540d44890200021380d002d00780081e41c46841d4401c09991141c2021 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 557205494 1250 557204244 557204269
    0xa02210403090503010f020915030106170603011119020709020414060706150303020d260a0e0f030f0a0305010b042d0810020a08070c1203152c01090506060306 70
    0x40e140030b2003519540400c0c25140200b04900c0c9058001c2626413141c0307400b00e0700c914600030b0710304c60314250741c50560000c103070501e018144a805001c0340045206510203400c1705a02c0021080b10542e03840780c01e00001c03003034100140004010b00940502042e180303c03074022201140e00e00001d146c0303004181c104114041c0d02c640c000f12281503071818041d1038080c00620450007107000c1d4001c3c029a2002100280500410800a40d081c85d0700040182040000c007032019040300e028200040c6860b0b02512061403c556212002c100388070119000c02400804c40082007034151130307076050003503990700d010300c0240740207501034400c000e0002101214181c58078080310101050399003039031008650300c402c0d02c0d0404158441c0740720440d400003480b11a480c0c200c4110380d044416480e101c80180459124591803c2d01400303510105616a4441c8031200c1074440303004041d100c400c1241c9250808140b54888100c416500010201950b500001d50f0001c284142403040e840500010b01d10754400042000d0343d200340c2e = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 557206744 1250 557205494 557205497
    0xa110609060705100519050709140f04060f080111040b0409020c030706060306020405040e0606090a0e07050a0906061112040e07092115090305160804050303030f0a050a02210403 78
    0x10b102503004108200134005050800c40000034003414507080c0c05d24408101e40403050028205030910041d681e000c039140b0100d800c0d440000810038038590025000300c0e10114984d5105040c00400f2900100801c044030459803000c008011032207000400840c103009912450041441c280700401c102c108070340082c00c0480311041500d103404915a1102c0c22220150410b507511741e4041018001c50500d84180a4103400f214001c2c00c6914103200000c00c6481c00504120800742c50710b10319404040100100f00140c400100a002c3d8640c0750032079030b00200714510503c000107811444050101e0404600c444c080081c0e00c2840d0700e00360030a86200746112001d4140010480e58800004441e82c40c944c00300a4201410303662001044903084c550044401910440d801e1840c0c090f012000036040802c130398910b1021004854044043c1c202070000e0301844d8004d13500b40c040081045011051508814031032880c81d5010040f40d1a4010104224003030410304050308034888981360030b15a00d119a699001740709 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 557207994 1250 557206744 557206747
    0x30f180f0203031b010501080712050d032a0806030c04090c090c090902070515070e0112110c06070807030608060f04081308010c030905010522023615030a11060906 72
    0xca00c601d5030902d1381c1d0010340d20b141d540c1c1005011812050100b01c0040004018140403140d1545445840f508000c0c03020060558408401c0c0980025181d80c032840c1e0401c18045540c0b142c040000342c0a50310407031f100c503c80e018034050f103074083c542841640035054001c0c00106a01c1e0a00703023200010321442c07101c0d00511a20140004031040340f800140101e40c8548080d1946201c9410262481d00d40544a0400e008050340140c240b641d2006c001d9103a00341c00b00c0b01262500040213104650700c50f0701040320060160744100600f00da042444c83e400307404290740c204910b90765000d006d0384501042e2048480200080e0100e008518114054011507601e21031600c0003903640c0c1202400c541403e06c5e13803070201c1e4a407412802071010170701c0794552100401741d030011644407256a11980f00c1c02401c0080c031640714100c40c05101d4103c1d55480c545040d440301c40c01030300c80b100a030074141c03042c040300d500c18141e010080f02007903424003003001c8440692003601c03010101081d004001c1e03035402c52803115400060 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 557209244 1250 557207994 557208007
    0x30a11120703050d0e031608031c0608070b1201170c010e030f0708100b0303030108100c200601150507020a050103180501111306020d050909070e04020706050601030f180f020303 78
    0x920071034050118584071440c00405c9481072600307149541c0b881c0444a40c0c1c0010801250001004582101c0024009443c21442d80b2607284010040ca8101035164440c41e0008982d1b4851000203040002d0901c41c2500d151703a03210342a1070f00c40c03881002a650f0340c000541c01a0700c2d5005180d1101c0b10b5600900741c034080e1241d1030026252500c141e000503407941c800103e0700b110641c0d42c450312400720300503070145146604020309140c2d80c07003032036004003401d0340c3c0c6008109155104510000b45400014510000c00c2c03a4441043d035904028002e410340304846114003841a400348080b18020b650241202003003c0c6000c0065000f0070082c901c3c1e44284100048030400504284200402c0c403052010654444d00b9443d101100c82c52140c2148041d548411100081c0903003040640c1d01000e03044a03440c9090351001c0d01214000031210381160080d001103881303005c101c0c3c140c010511981007030303900f0401c800941070410292891020841400f07441c1141c1400825103908040324598005411685441c0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 557210494 1250 557209244 557209253
    0x20409020703030b1c0b24030303010603061a0304031e1e020a120206090a0803070905041107030212090d03080901180b0f0a0908121312020a11030a11120703 69
    0x280002400c0b00020b50341c94054010389426001042c0320f40c09002999800000c650b176071510024094958500c0c0f05040e00c410700908504494580e91038806401d40b5200d59403a080a409440c480c040c54441000d681c011841c00c01060301900c1c421a01a41d680c001c5104141004000d41c3c2401445810000c0c404c400032102d0301030341d5545007102100e0780140f00e160441d0074080c114418026400c01150408000e01c00d0600e000a07450900c0c68100c0006907913030303e03009002e60740d003059a400140c000d814009107050310b1868030003510302c9034001e40949602c11840d1200e0400c0344925402258019000390070840480d2042c038a15034000c0c04400001349410000c0e039500c5444c1d814510840d04004240d08008050080c04c4805401c920180414040c520880c0c0e0f4001d0907010701201480b09c401040b000906504908800e00076a0380c100010308580720020400a460f0404c0484c00c2d01e2400030200101d000d41400541e44980a800001810403921a1800c0100c407098005025456108070040880032030b = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 557211744 1250 557210494 557210497
    0x40e012103181e05090c0403050a3c03021501060f03090302010915050412050c0303062b0c05010f050c03030403050f04080f060f0a02030f0c0a050403211e020705010c0602040902 78
    0x203440f840d00f0741008601c1d20341042102500142044512001400200000748000612002d6240d0000c400ca09001d1111a4402610310340c42c944240200c140f034201d010201d0a007000c5035403500990a90300a202c0e01003000007000c10a1040e00001100104956292807003948002440742c801d10000c241005e482d1110f0b002491342c1001c10419559400a20080209022822180d1030450428505080c001600d09840380801828507000e0084403101c441a40d40443d01034401c00144010f07000b410b0f61034213000d25412520700400b408203913020420075916019100307036821704050304000e51450b40c0310350301180c558100c0302031010030100500021595220034044c405c0e0200c4840c00401e0f0a01e4169400c1084a10180c802a03a0302e10400078001d400e03040036401644100c010105680d034601d2210b00b22070910581e4005420b0b4025040111821203400f201900e0700c3c805640c880000003200c03c030710700308520101d8889000d42d1080c1020041035010f1b190f80c0b40309502800e4014109661001040160b = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 557212994 1250 557211744 557211779
    0x6130801021809011a04030f110301020c152838040524091528050a0e0a0f061d070314220f021005040e01210318 50
    0x2ea07a2450646081d007810001a4010040c01380701e001c580c1074800c1061424401ca0102401483c070381e02c00c513414844c103c800000e005001800071907aa0f01500c103036075103600b421a441d601602c4070802051400d80420b000c00024854070307580403104448890b041c40205800700460340071107120039000314402c42d0380542c070854002e14901c0b841803c3c03030801084112140102032401c040c0401c4411114403503231500c20901024107480818081c0c031030f2006510200c10070b6402542c42100a40401003120b01d5482041c0d84049003d1071010070323a01c0383e04004407107080e4000c00074550049030010345080350a0f04000da0200d0400400556079032a4511007054150074001c030f10f05080008240b03c4a268148600c9910000041d00d90680741018000703010345607030140034502000d00481d0441e0601c460490078000b055401000c5080ca4055000302070a035400c944980500340803c040001110074001c42d0302240788680a1508414410365a4241d41da48051400f240c103132000d4005c0840c01480c0320009040 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 557214244 1250 557212994 557213017
    0x1171005180a0807060e070b0f180a0f030209060306090c091306050106030e0609012d1107260a0f050319060e1501170106030504020d151d010b0a050613080102 70
    0x10303904c00703908104042c0d4801d000011500d0380900d90030424020b5501c20350fa100e2502c00c254580e6004c19184651880300030541e4650700101c02d01d800555010403802e424103c9200341c0d40c0c0c40b06a0b450904041c0c40b0b2008a9070b03003650742c01002c0701c0c03416452b1040722245c0c041207020550301c5040d55030311030100300c500980160001c0f0b40e0369191030071201030400985502041c900000d00c2000c500042d59400703101c0d24100e41a46a10000d00352168032040d411100304040c01191154503a900f0b4101001561105444c0d103140314001c21400200411030822200748141c0c940b03070a01070b94000c8400311140d500040c10120001540000c00441d003446004d03180040c03072521100c54207400e100c01c290b091100150070305410700030510b10406c140c0d104074424504444884c20002001c3d5618008202e0346580000c004140b207400802142d01c0c1c240940c0030f4485428520850108550103401903402c90300000c1175682e2000310100208035900e44513004054603003011100010f520303541e0303040500b60f801060003400d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 557215494 1250 557214244 557214247
    0x70303030501080c030a0b090a023f060610110d0f1b050601050d02030a0803040506010e01051210090302030d060803120a0b010906050903010902180f01171005180a08 73
    0x51603414060280940700540141c03807492151400207070740c0c5400c0f0343c008004200a07000500c1901c0180000b10f440c9802070283c54802d0031500c560002e030b5200c2e040c4010104102c010851076500c00300180115905500000c0103651240b40401001641c81e026a50412203820000381c0100c1062101d580c41c41c3c040e40b01c070155052012005069407803442c0881c01007400103014500072480c0003c038070381111419250403940525500100c4e082c0340c01100003915054000007848100503001030f001d03040301c40d60441d1481070b90b2140e0800901c0d03440c414913010241c0c01014810b40c40d0856a01c0b01000c58801d00440f440d0540c24400e4400b50740280c0c3c0a11500c1d01301140c0301406204284019501141c509070811840900d00c002030b00068080c0906010800c0c0441d015030551005d50001d560030741c0091122040381090f10a440031002d00311408e604042c00c000c0005820408a20800c101c8000e1401922103051681e50440040c6002000d40a034249160301c0c4110f546024010009818040ca2545 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 557216744 1250 557215494 557215499
    0xe060f1302090a060f0c0201030e03070b0906090606030a02131508010501140f040b09040f060f02040b030915010605040b09130c0c02090f0601090b0d0b0907090617060906090403021e07 81
    0x4910301c00705500501c188145d20000050107644038500124040e82400d0005125010142c110314600410f00010100300c840414816203060014081303100d42c8110040341d019685c0d02061548808141100030b401001591a403011304556030040d0f040070301000c0004540d0340e0344010703050965900780c0c040102c0c00d6140201030000c0c10708400d49614084151030500c0b442e0135403000304003041d00007072025045a0056a00c00b04002e8940c12600070f40c406014255113464850410511550050360490024840c100b0b603031004002c505181412035020343ca5850410b468101070141c11360042e5201680b042c003c03810b00c010b042c06c601c00c03504020119580c140c05880c4c0351040c4094a4000707440c089000c800a0108016a82c3c00340006041d00d03254611152180c81484442010707041c0054895440601c12080281ca254882c218200325140d550344c0507100d00da0408a07100088041d5422a040541000011030a052540c107842d041403080c41140c0010034213a9601d03030166044003008901b81c2004104 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 557217994 1250 557216744 557216749
    0x15030605010527010312050708030a060501081f050f01050c03070615080a0c090902060909070e152a03070c03030309110406140d24021b0d090e060f130209 68
    0x101c0d5204002100600402c1c1a035040281841c2c0b05100041c892104001c1c0d001215108900307940728149d0003120244c03279003421030050002c1c000c540280ca00181000000849203800031042004120305c4080c4650380c2414401440030503994410700c181404020400c4006e0200200002c268440c0158400140d50304d2001c030503d01000075600090340c1d5445450050049041c080d0710f081190b440c0540010040501c0c07000c80c003580244400f40f07602000540401080d10340000003100e8003001220318100550681c50f0310140ca010314142191944c44e548003600c021806c0071421010850340c1002c032824140c1c140d941c90508000d54100b1800640c4940d00d804c100322041d001426030302d104881c14001c15080038641d481c1c00310325050142c4a85200120b410501034080d00700030b241119016800402c514800c0b51101030340c00308402c180416505006e003207020801040b1040390030801d80e03e11071510300d091002c0d001080f0150265074801044c030010107403a0b685a0020803000d17a02c020240c0c490405008 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 557219244 1250 557217994 557218009
    0x409020405040b100f03020310030807030203030708061e13092f030304060c260c0f0c03070f0e041a1003030201050603010b0a170a02130b0a0b0a0801060e04150306050105 75
    0x124a0150000003200341d000d03504964066141041707032030016100d40e2241c0301e00e40400c20b141d2001c4c012034030025052080c07503404801140b144070f858030f44c2081519044280720f041c9810071880310750300800c002c5c21043c52820440b0301a052041701c002140482040c2c4070ba480400784610851a0030360320300020310030301e5040c1b14142e006803c02c4000c0d40c100740c83c01001818000031900300900c01d900c40501c40b010001c0e052161182c10384183d10064860070301035441d560700d8911aa074186140705200d44400e051900280f080b069a041c0c802e0840a5490003840340024080a00200c503030000f849041303100d1030000b01043d445003190b08000a0024550700b8080e0031200003902480c0641d0406910a0054844801a4044480148800c050382c00070810150800d144158001e41c0f214500d40700181c51515900031100042d801c6810451aa68400240b020b520420400360007290140c0010401103020b400c11004803000600042420342c0301e54103440c01440c4a4008460580e0740e08010301040c00c1500 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 557220494 1250 557219244 557219261
    0x403020f0304030803070509180702010203010915030f0212071d01030b07020607091401030204091103090d1b0813080a05010e010f0209030c0f180c120c09010c26040902040504 77
    0x40c0070714036140c115103c400d80c40c0300040000c8244040015a0142c50b12460700b68214004900da8071045400c003410001d0103940284608440700303050035844590041c021011008590b072084480c1c500090a9007400b074442a26200120140286800040d801c4a032403400038026907000d01c2d110319981907141c0307040c0d8881c002e0001c004640c489010041c044e900300b5030000541c0c9018250b100700c070700c012004034060b1040390405429035040c5a0000074071f51100c000703940030320038500a036003840004130001c44002d8000321744030600490b221b044101003117030794000b0141c4060301c141740c1c00950346800c103040c0341800840003110641e540d00325200b0880d00a02c90503940d05440d010a5107081d550b040000c4e503525800c0c2e19135205209403040c0c240030344e980702480f10401481c0c440d40310341440d0003840d0210039001150308002480761400010040c25070071084510600058440d80d80801d40e6440340b6201c0b40c2d03208a090307c100900340c04c11401d952180301900007410151005030b99035040130107100a541c01d18 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 557221744 1250 557220494 557220523
    0x703091a0f070e031f0f0b0301020f0307030905191415060a05060c010f0e07030c0b0913091703130201020c0d0c23150304260906071109010905040302 66
    0x21810310049111204003903810008903e442c08010f0010000203041009034a000208540c052050030b4203880c05401c81030252030481c2003000038250307910516090344074203c0050401d40c0c08000281e800c900980c0480c111601800c200c403460300c10411040d0303000c520010103032000d4140165482c0640e904005808515400304a01545410140701040344200c050003450711886011590071084d41095101c13031070340d000101040c0500350b5203044c0c0d641c40381040e0000751010b03036804c8000709007940c68030101d6446d0390028041d61103c1c14200c200000601100100706c480e030000c01c001613021040341000e14019007800a03441d81c0c10790345200280c58005401c6245016400b500494804036210403040400ca510681c40c140185500e20514204c1c04403210380c0903400224090051850722008000e5441140305010950051a8aa085030380650740018480c1c3c4800d01007200071041c0c1040d0000d802d0981c030642c440c14625191800160202c1c20907002804a140d40d0340401041c10b178100068007110262 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 557222994 1250 557221744 557221793
    0xc050711040b0a090f0906050c0309070602010606020c10020a05070e0108010b01020703020d0803070c05032205040207150c050714060703050f09060402040c0e100816021209101403070309 82
    0x381808143d140096110785155160388070780155807144a03401c11100e0f5544101c080000780b400010600690b0000c0d00d801243d88038506011510314014424101034842a80003440704a0003141003040400c9034007500801c6020300b092308030000c0c000b0045035018120361680f0306801e60402c210a07007103e9505038202c1c1150f00c10402000036884040403841c0460300400385d503a0707a6642d40401d840341d03004040700810622001928240b000690545080524000c0c0103880003682e544080105a005026014214a00c04e0044450b06034050340001c0140241d802d01c1414041d2544402c1e50880c5074948040341c6820890800401c1c60b40361003140d904c03004043d0000e00d07a0034500a01540c44500400c024040e40d598103020410600440d07040c00d081800521169411005200042c60600f041c0d5140114030002c11800d0007090000c641021503269840303000d81031500310b00812500c24524045402805000908402c4420b040002113200d500d5503100400c190091385400072000e0359a501d031107580f041 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 557224244 1250 557222994 557223011
    0x20c0301140a0203060f0904050109021323190e01060801050705040f1403100c030912080c2706041205121801080910020a0e13020f04060c150c05071104 67
    0x10001c03050b007200c10804010788070764409012460688000400c103a1118200f000c0101f00702d030540126088a2096030309072078002080c150b2400b5130717900c14007504403031140003005c481c2c50341c9603485594072403d0035200d0101b2061140b188003c540116500d004580d4550b041888505424010150000d05d03500d0154a014a004041c5810208a006405426060341d2242503655020016450481e125840130000c011040d02d010b0300404405404641e4880403d400144190003640c91a2245501503a000d00e411185100d021911800c203080c0b07840b66120309061040b6499000142c006482c2c4111349002d18480d03420860716200c444050000410810000184000c3d80b82408920564003800c0c4410661034044104e4141240314160203500d61000c03501d5600c1c180d202c20b604441000644403040f9446d20403880318107a1044802a54420404000030000c46111b89001d6030329601824002e411505c00400780d20a8544692200000860118080f014001120005000c0c0e4004540800201e10b = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 557225494 1250 557224244 557224271
    0xb0a410a0614091509030c0907050a05070201020a05060703091a090a0f020301140a021c0207050a0215120a050f071b0303020d1503080d051f270c090501020c0301 71
    0x8a40500c808100301116603050000688043d00c041140082c0714502c2c543e141c0d21011002c1d000400210b1281c8541d00720854141080c4031031b2030050000f95542840c10541c2ea030181c0702c3d130b13009a8007281188641d01805012030400e203e9a0300030030707040d6001700d100b454a040c01c03200d4003807806001429262034400d02034219000503440303503065848105903907103d65130300000c0e0060168000411074202c00c5420400c0d401d40e5075008204640d42183c00c101c49900c0b0340e03101c504030b0140c0c800007021580070600120140c90003103000074000514010107454504281e584105540303003901c4d01c004241c2c0b9070b81401205082d028a0507807004061401540104401039a0750040e003262001a0500d98001082c0501500326081100b5100300070175000c0d42d01d9030b40c3ca0b110615034040003a00842500d440042a035440101000c45244a90464009180350501e64100d503004001c072490181401c241a90040b0074a182c064000c0a000544070003009500d0300002a040600f1828032a201c2e0749480c15412201c0c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 557226744 1250 557225494 557225509
    0x303270303012304021c0c0207030b04021903021309050d0f081810060e060906060702100f020c0a080105251b020402090301020c03210f0403030b0a41 66
    0x15804501a03c1182d0b0201c070a1904400c100d0940702d401a000080c0441080b003030a01d862400c4080c0c02c0204118240c1c15400c80e151030361800018101c6002d00c01160242c43e1600207100003105d0500c046c2e0080c2e070381c0e034008bc001860802d925030b0030316251008503007484803e00400c81480094180300c0041800707404001c0203003000a12590b800240c244040d00c2c090010000c0c0c503440f2400100801c80302e9214a18542c9041045502034803ea1070200011040d05001d400c1e40d0310715501420041662441c9402925080020910740341107104169158a0650b00c0c40e0202006040d40d000000e101e08181c00d40301001c6a44c2c43c101001400c290b190941c8603648140e21090034441a190184c860485100182c007901c07464610310340c158004989484101d00c0407008001072402000250071154005640310b03800301003120000310104645000601180c001d8100c038044050080c02e01d0760594a80e0702e0b480400c02c0959102000b0386803820282000c003100e8074104a80241c554501c50301480020008121 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 557227994 1250 557226744 557226749
    0xc02060c010902031e010513231513110907020721020a03050610082109130c020c031e06010308070507031a04021503040302060601051c0509030327030301 68
    0x54000040c544018500a6001c1411254000c0035070394804045180c01c825620340a081c0b10295203800041074590382c00780c1d080c2000b04ea11550303041c03103030b0510182c3c0548102e81c0d1035100321030300501c43c206504032407021046104900e89540344161000381c1c1841c403000d1004458a034008c594071824410040c3e00019903000b1980e0b41d101180b04030401c090801c40400f10160000c0d0050715110022040080125025201d010002140c0110982c0c2e926000d41d160000034452400e440c99000199216074410300400244101800320b2058550105035641103804000d032420058026180d840c17954a0203000c101c005600d0a424503400b815090380703403601c1d04c4040c40f0040c022070000504508110041c807981d03000710380094188043d2840303080144041142110128807800b000300800c6071100c112400c0e030f40035640541c010905a6207410054485034019a1590792004040900c081682c081c0d02596109055a0000c1c6440f401d08402c403801000e003105030b001d00320003102d4640000242c00401c0e0ba04 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 557229244 1250 557227994 557227999
    0x3090f0605090a060207291006030513050d030e010c030b130f0e03030103050703021f08161e051e04051315150206340e03100207031101110304030c02 66
    0x1030795198651107518001041d00d00416a5002282c0c250174080c0700c9040314903c422000b80000307101c0d10412980328621040b00c00d0710604e6210081800820b120350700480d40300c083d00e082880075002c107480d8289013000e4035004200003504e4001e0000008000c2c041e8105807034042c2014000085004006158010302038010504c070340d600c1c03008480c52480d03a04001c103071308000c0065958a58507800c1c00d54545016000a078002d4111003c0940e80d40011640c0500710f11a640d10305100c0e84a90200800040d55482c60008001c05590000d816400889091803800d08586800b942e4550b00d148484402c0890030605d05010802e0004010795190b507441c0c0b1040f5a4400400211260443c003006031428003500a1a0500c89481c0d1a0840130340000e03849004448101440c504032842c5416940c9460400b03c0040482540240409460340036404a610342c2a0042c141e13868040c16681d500c040340c01030310090b000106040b0440b00e11600a1041580304403074191283d24500e080d0302c0c00703070645603044c130001d0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 557230494 1250 557229244 557229251
    0x14010c08070c0e012103050304030c030909020a0f080105040905033004080c150402030d12020c120a0f080714070501151806050103090203060115051b0d0f03090f06 72
    0x24100306503a811198119400303880c0105031074407050003036882c610034011020b034501085140381000401c046010b403c144d01d5a5907915555859400326400402c0320000c0782405020440070a004490f07002074034203072003e03581c1c88001d1403124070010100e00c010780c00f060045181001a002089000c821103909800400485020350700c6a03001d01414003d070b906030144001d0700424042085040f07070003401e0048241d0202e0355000c2115030300480741d40040e20006c1d41a0b01c0509503144441c0590030102006596460060411003a01103031780c1040340032138a4500d032840020307051150f01c0d00f02441c80c520352030a16110740d16140880703018040c0302d4201242c10302058081005000c01000f50000404201c03252030000c50140c1d5503000c0c02100710301600b07641c43c81c0e091010208083d4405d10900c244580c008005248992a000107900c081007240042001c02c0410880340240f0010300c0e481c0028417090700020422a04d0440700100940a05600d11040505088030300004c03449460303680081607040080003 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 557231744 1250 557230494 557230517
    0xd030807110304030609060b04050610030515032413030f030b0f040c0201050105011d01050d0f09240501061407060b0102100c0804020307050307081207031b08130509011401 76
    0x54440700380c5003420001c0c51000240c0442000056007119094034031030b0406000035507000f000c01060750300031207010ba0024080740110b000c051180c1c04c003603000443ca0304405c0501040d280420b0078945250880d4200400282a80320741c002c1950116620441d80030411180e010f0a5034000c1002c80003080907410142c81d1040d10101c0c3e035400c89016600200200104000c03400d03208003a018107424425940851030312120f54011124540a1105003041650780520f440c034402400c40041c10b5900018007150341d90400c00001810030321040c240303038410001d060700c0c0c203800e50341120a803281604130004010111580c082e81140d0b500903944400d600c0070303000c5406503459004030f04d41055001c4210b07641342484044d500071074015803043d002d280240c1c240c8030225164014076560f40312a1045902d15400f91090041d40840140984642842440c02240c04a00e1111030640c034030510905540c080c0c0001040507807284540140402000280c030000c80b00d40c50910301811500f01d4001c0310b0b05010955149 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 557232994 1250 557231744 557231747
    0x20d0917101b0e0f06070f1a0705180402040e1614040f03060f1404080304060605030d2006060f15040b0304060902010809070b07240e010209030d0e0d030807 69
    0x41a6401c500500c0400084100d00205140c0d990020044004242d00b600580c03d01d0401103421000c20708064116850514550f40b0261030203007040f001d503a88103186a0003500700e0f0b500b503041c4e401081c41c0e507209038403a010151021a42c1301c1c8401c0301031040344100402c201d1201a081070070380c0a0b562426984400710484800d940442c041c15400b6902c0c500000c0100d0340d82c11a00144007928000d4a04211403070035146284121070400808140c402c01c1800024009030780d5400a40c1d20900c01c4c88041200747e52100800d02e003810185900c001700d5240040c0d81b00c1d07403071614a03402000e03000c80020140b50401c040850303050220701e003009008101c00c201c46801944071008480c01400c4046223243c2d28a402d00b041d200905103400103d00203003440c4045441c1a0000840000341d03408000003134030308007030707591400d80c2120201124041c0f058010114960a041d500c5501d1524250b14005681d030003081e0101410301c044444850300703000311012101203980b03030360139010801e5516040c0000700742c944400 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 557234244 1250 557232994 557233003
    0x8060a0923041b0806011404020301030503090409021914010809010c0906320306010320030c13030b0f0108160311040207141e0105010603051302040b150d0204030210020d0917 77
    0x45108160b084000f0001d00144001050f0b412601e907080c0b0340f60024503610401c8141d04c070030301c8084c000f98418003215000e4a40303648204d0a451009050741ca1310304a0030721020302614254000c1404e005a00d07034510841d6042a07600754000e089000801c28050ba0400280c0010503a003e820200061507a100610030800d4101c1035901e030490081c0a100d0803041ea07010481e6004030707050b82c00603050058001284a120451081d065948100e80b81969240188182c0079000940080c03118861082c0001c0841c2020f00b90171b02a040000c400941176040001940c6170000309a10030650403100344040011075040d0716041301c501412074003da42c5180c9030515090703030344403150480000c0c01034104c04480e0f00155520010b0084005000313001503030b84c0e1032040e004c95104491242d04509020340301c03030061406c0e900c2601c0c0c4120081014000d0680c0341c1d000d02c49508100c0403a954a0740c0001d0900c113501d0645034030311403941188002c0c8100040210010060101d038480c6032a00d136400f40458002c58800e00 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 557235494 1250 557234244 557234273
    0x170c0403120c1b08011b08010503060708091c180b09060d020304050f01110304030e01030c08071808011e1a01090302151c0209010813020109210501020a08060a092304 73
    0x140c81040c440d4803403140c45e0003013610a64110b880031000000c04441402980004c3c1280e00007070203400e0325550f070307502680ca01c000140140d044e0702444000c905441c820114070311805401c3c0d600c14113414064a04c80c00285e50030b8025a96410f0144214441a91b50f40e04841200c000c008001d61039031120b10b4164949610340100e1201942080c005144203801d400103940701d9030207a640c00030200d4407800194204e5103040d03e03c038001400c181c002201c460250803981503480c2c500416450103a66a003a40b404c54881c0c01d40e6030b801041151600e8006000c60207280c0e04c92010a80501424400b00700107815001c00b484000d0040707040b000943c41c001a100240d6041c40c18010341407000d00c20541c1420f000b9804180303094041659076000c03a00d400039000c0720031380184d0f060f165a0340403410b008160b40701040f4004a0381810309203070750400001c0d400380090082d4249035220171415003415820450700038074079000300c0007051030501e00d0015583c1c1c07042c00381e00f80f50019413030802545490509001c5200001d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 557236744 1250 557235494 557235533
    0x80c031b090a1508011a0405120a02090702100c05090f0f0a080d0315090b031002030a1d03040e22030c1106070c030210020102180906010203040503060403170c0403120c 74
    0xd60b4000f43c140031401ca040200601599902031076a00c400c68941d00b40100480400b680300c09004c14411810700d010220454103a00c0225074142035140d001940c03480048480c00d00580210351080705035107071809410061045400c05034280f120031000706500c03900c2c47d00c00c1031191040c6140d00c0ea164840311818000340154005071800407407040780144c090031003243c0390109050b05440024244c0c409102307a80c018031004020309a05800f146008000c0d400144c41020015516030007827200310003400c0410305e56101040a591540d2405040d0b100611000b40083d280e08004d550300024005460300c3c61404547c14100205c0c0d1082d1402c00301a4103000c1c1054130342041001440701e0a0047c000d2100003140d208441c0c40183c1459084201c0c01d0b80142c048106602c5141d8031310071070301d1030004d003040d6000c1018412030707007010707034610000c0c0c0390071800d40b002e50100e1056586580d40c10740c1c1a402a40c000d051600c6645803074690f545d1840c03030b980116910b004021001c4060400c00c035045482d541c0b845402c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 557237994 1250 557236744 557236759
    0x290415060b0f03060102071a0304020d080d090605100e010b0409020a090504020403151109060912010906050403050a090806060109030602030a0f020a030b3a050307020a0609031101080c031b09 84
    0x11002e0b402240c3d4015142d65025100d4000c00194050540e041c05400b6000c2181203411741d1250740c20720440031030754042299200818862443d06050f40c0c49074201c2c9601402c030104070307801c200904400604545c0c115450b00b440c490014451103003880c0803102210035444005030f8600c0d0109048640d440f0326001141e1042c0006000803e000d4200740100581c202c10008200e111301d24400e0704003c0c8103e42003a40c00410030b00c40d440c8207103861200d2200c4000d8a000200c3e0781c19555a6050448000302c07011804a05c0c00314810082d80d900c841000d014000d100010230322414460006000d0910612009080c50340002c00241c40200300d420461380070b010060300359101c0c40d000030054041d1040300510307405641d02c80078000c00c088a549010108070300c41d080c61001008014512090201a06420303903c51004000001c010303203a950107074000b000d1a03038070141d0980c1146030240741c880c0520754903810011070209020030920b40e00c0480b5044070340541c0e060124245180310301064000c0700c008a510600c07 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 557239244 1250 557237994 557238007
    0xc011e12050c070311010e070915050907090f0b0a0c0b060301090b0c030702010b06091e1c150624030506010c05100f0b01140307260a09290415060b 65
    0x102c41c080c04400b846602c1d8841358440c81c461060072544202e915500b1780e03204400810140c082c95000e00781d00d41c04506c034001c0082e124408200d0034072060700c02100290750102d04110050007205070b0009003501c151150304e00100480c000b020b0a10061020309000c6405012601c2a40c0035030001d0111075000d9902c00c000d00d420190358901e03400449120016500701100601103240c480200c8805000040003a140c07990700da044001841003101d803513600190203e84d90b032501c0044903004411f442c880d07a40ea204c2c0d0044102c100090f2100c5034403407843d040c01442e22449580d82429485540c0c0c90f10314000540d551800d0040350301120319000076205000744031003851000d402c3d4000c00f65034910050188400449007004580958044112039440801070000c2001c091003418040d624000007001561011400341004841000c256480e10f41c05a484203903004100c42c0d00303242c503044240c41030501b0300c01508a101c00080c0d000101300400d4038401115190004400c1d0340004c001c1d11054131000d03160304 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 557240494 1250 557239244 557239261
    0x30a02270f030c090a020304060209120c190302012309060c1c020607210b1206041a06030d0e030322030302160612360309080c011e1205 60
    0x80e2050301181c00340c180020412154240001e0360540f180740601401600e03590a10190025003025004440d22502081020071680d10711008403241c0002c1005801c8042d070b07002c10001100c1d4248003000d01c0f6440c1a9080000d84c3c4c00c5070142442c14004048201d2010131f15070b4901180c0b15024159030300801c08920070700c45880c001032100100416414001660f240410142d03030742d41c02118003100096400011480105070701c8665414240790304000700d064440800050080845e00c0348200b0316500c01403c210500070303690081086060011080d40c05400c040c004203032520301c20031004c81401000f102c0300c0d8075a2010030860f4407000207081c0303c5000038402c60b0b900c040c902d101d20090f801441004602000d01c5d13000201d000894509482c0d1403031340d4a6170340540c0090100c010034000944941d0fa8041600d003030b2031601c0041200c0019484c04404c00b02c0c5406003031202d10303810400e0310394040030f604145641c0100348a001c4141035000307130040caaa210b4086400c1c2c03440490036840c0c1810941880b0412 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 557241744 1250 557240494 557240557
    0xa06050306090a210306030f0602121f060c0804050a0e040512030c0d090305070c06020c0102160506040b090a08070303030f0e0604020d0b07181203030c0504030305030c030a02 77
    0x8a004a007521010b844030b642103030341c0d46284003000d0114460040c0341d001d03401540d590052407410714200030031040d5480d110380c0100048640309543c15a00041c8003042c041788100340d503500c4602c080030314071420f0344070054207040c0e041d6001c1c1c0e030f09216038000d40c0c20500c1071042c1076030000c0400401c8a40103507106c50305030719511800e6a0444040c860a80d03102943c289c0481039034401e040c0411494109000010700d040541203015064060210802500c0c011910300740501029160360340040001c291a240020700e0501d1b080c046103401c450075041030201d561140c0458007250403003907409481d041348500003135031a52240e01c03a076a2032060b40380000815405410040c0b921010507020443c0d1512031071040c0d1940411980290b0044840721400005071403605442c0d04000340b80b401c4030072410051010792031001c003030300b002c440207015040410400d640350044005501c507074a0184d0606186583c060150300005e048242403030070220000d0210170007681554a007802c40e1148003000c1c070380d0b4405403d44 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 557242994 1250 557241744 557241749
    0xb101806060e0114030411060c0a03111603210521010509060f1f030e1905160605030a09030c021810050a0b16020619051c05060d080d060506030a06 65
    0x4920b145200614941c01440350115407002d0a81c41c82c6180c2d00d580e910808603c4140710113a1010060081d6603105d04100b001c610410312036201d14640e004540d004628010783ea0b6141d6140b605461828400640d145184540c07030403501500615101e00d9070816030751801201d041942c1211840d525800300c0440300b2001c0d0481e0800e0300c52419940b130396070a01c6110401d031500300350040344441c42582c0c0441c030f51400e004803000c0d07450300044204080303c80505200c1f07105051179645080301401400c1c08000c0c400c100c1500c00400035080428030b0083d024009010040001e00280d50701c1c0305c0d08040c1360040c6030784221307242d0050802c40c4070720b00d0156070030030304a05031105e00c50444211004521401e28411480a840c441074480c2e0809003507811341076641509820807070b0030400c180f1008a011401484008952110b03864468840070200400081c940c3c81c281141b001d2070030582440741a0b00c48000c8490480d422007181f696903501252007401030881c55008503040400041080341c1c0d03820ba944254207 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 557244244 1250 557242994 557242997
    0xb0307080106110d1704050c09090a0309090e0d0c0314030c0316140d0b1201020c010507111603020909010e0d02030a0239030f030403061505030105070c0b10180606 72
    0x180034181e20102c0c0d0350001c032095070000c6000b4464581c42c4d17400c0110b403144e00510910803a14418034010101c2d440f080283c40700c400b154042640300042540020130007010700082d810070000d00e405c00316185c0c1d960300c4410240c0e041c085084101000c1c075104000c100040708101a8460ba28117004d420381e0400d5008039500c8040b440d00707005186609114104000c01c1015400c5c00a00f0400c407105a00010005910a00e900103129000780d8200340c400e0000c1c02c003000c00d0100000315403500240c05407000c80f4030300c07170f5021a801810358000c0c2c100360301c45028152501550040d00d2640c1d200002c078010f2085008001540c42001c4088213043d60010041c00808555403e58400e004035200349001d00c0182203038640708001949840704141d4400200000b9078200404a0b581406400110350940d4484d070800d8405075203e08003404001100c101d404001d01042d40200a20303c0d2549004101844ca2200148250100e80110b52089e1170004030902801007401744800c078070307004009080208a02c0c802ca80 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 557245494 1250 557244244 557244257
    0xc090418031215090608010504030801060918050c251e0305091207050a061d0a0305060406050601030209180109050106110a14120417070e010503250b0307080106 71
    0x540800c0000011158598561280c0d0240d458008940e400350102c594002c120b000a07081c00541441d06006800050540d60b0002a00317041c641001130005905030082814040d8982041041104243c80400740300d59004001890307817100b41110049100384203416083d0140881c1a540081d0101c6407042c15600c2203110400f50740503600030403040c1440c80000350100703009024641560602d2543c603845502c0c0e42d000d03180c00d69102c03000150b1040313003a0004000100c01c51107071300c00404074255192403500100d0311072010901d555205541c5030340c001d10051926448030f002c2886079020381c060703681d0300c1001002648190107100c081c0c1d00d184401d02c2159035180c00c0c5800082d06502840f81040c0f185a07031009000c0741c2c80b00b5103d90081d0f003000c500115091003554844c400102100c0c01400150900036540482e50b2000003580d440e181d02a0071808610f030340b01004001c00e6070002064000390149114825101c007040380c0c00130341d0480a80c011f42008200104007c40ca50b0f000542c58140c40c010345038403 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 557246744 1250 557245494 557245511
    0x608040507121b06020c030a0b1008070e07080a0b1c0f02100c030314011224052418070c0203031b03032401080601141b010c0201110315040207030203040e0c0904 71
    0x22a9201415003907590103810900302803012070b00c95900c07142d210f1001a42ba00c0e0780360355441130a00c0c004030f83c4d210881c00c072820b2080c01001c1382d004010a8000030400c41c01d100c0001840c00096205000c0150021081c44e01c1ca0300604204c3d6044010105940090020075405160840500b018001c5c0400700c2c002443c18000001247d0211071607410b0325440178002c003180b901030f038034400003c410250075290060811811100c88134603015242c49030a034038003080941410001e03c9405d402210074442e00c501d2490b11941ca92100300314209910401a1420b03420003010350002c2801c502c201301d0549070008400c4a41e01c402c000000c007c0d0b00070499950294005030785100e8081e81c14511401d81c070300050414002c40c80b190710403400c0d2010304590030070180c80c0c000241c50499544001c511201c0060351600d409207501502841201504040c0303d040c1450b600d07000e0212a40100c20300341840c8101d80c0414043c2c281482001a01d01070f1078803441d0f60100342000c51801443c0c2c0c001e000203070702c994202150b4 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 557247994 1250 557246744 557246747
    0x3060905040f0f03120207200103091205030a090813050f030601080c010503040317090715020d090504020a0315090203041203020a1209020102010b0d060f1103010f0608040507121b06 80
    0xa8910aa40001480400b0481c0d80d032506024081c0000680c02c204160103000103414862004098080c410f002030085840042d1503100411419018541131625000000010410340d5180112030100d918000e9a20f40d80c2441400c0181007240b805005a0ba002c990301c8090704030560010181c8104a0f00140a51038020816a6591003400f5030780042d00301400708a60b650096000d0764010b88641040850318150711a81d11900204172150040c80e40600d0f001c011035100d500840e00200101e2010709080d000d2541c016200740b02c948074150056130300103550b0000758802c0d400a4407503185207042603c0c050350b40900e00007a4100ba40c059034924200c1c0f0a02410340d00030b108446480229032103900b840000e84000d48018648642c099040d5500c130024501d455817010990f0750f6603803107500c1c001400020110170b4000c03515401c40720f2503080c0c0304100500c41104149900c40c101e8441e0f29101c034466640f403904c0f900780350321944821041807102c5403440401110f0540104845a82c10307203040c1507a0344100 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 557249244 1250 557247994 557248001
    0x31d120d0b150f07031223060105040501021207080f04120c090b0d230d0c26070210051306050403112d060408030c0705012003030c091309060c030609 66
    0x318034a018200300303440b83d074610100540074641c0242003007184611411090b5090300c212403600d46503406860301040c2400034180425400c0310082c681103007858100710001c1c0d6035038038440b101c008410021400d1001c101c180d07811601504040e0f01119203481e0388071400421040224401c0780c8007080c0309004600011a84204802000010b2043e0782d4002c0c10f80340e8100d400b8201070903600100c0c1c10144031450b040200214401c3e0800317555101610300b41810710780d60701c00f626901d0307000b0810030710742c6007030440c0422080d621065012611032005024441003520b46204038206c504545166030000204544c001c2c015008a0b03000e0010044800080410015940040c04240240801e000340051262205802d421a02100606010300d01500c03401d0350b51564000c903031076001c681e200c2d54042c41300e541e0181008500c0d20034815010b880800070800181c5a000003000702c004c202010401481e26580d00074035601c03415000c070080204880701e040823805000c3c0f015820700401d080c50350000e6003441e0b620 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 557250494 1250 557249244 557249269
    0x603060106020105090c04181b17060c1b0f160f0b0c0604080c010f050109051b0712051305120604051903090e0403020120090103180b0601031d120d0b 66
    0x1011b410320101034401c0200501038501c104c9051350094000c800000d2104c4d00ea2665401301881041055103460700104a812450f14034004e150009002d014040c9113034000d40315a07040b4034640161280154000c20720381080710040200510540c5002c00c01441d01d0130200058400c3c0381000761504ea12902e03412403500c1812290901039009000042c04505100d01910584411000104000c10140c1400d801d584084e00409801390359041409041d66160142ca0265034642d031070213080c07036419124581144004941341e02409400280c03402144203910640001d480300411161030f0005074105940e84100440d0100c0e1180302d1421200e00c61442c0076203103070285500d6a150f4940ca030034508140c07410a0094011020756403105034829500710390340b60461090440004090b291060000014140c82202003042c83e080708610380c502c0421004255294404005c0c00d000c9500c1c0a020b6440e00100c0800301c03800c2c2140030ba0500c900c0c248100c03030020070b175542c0c6120051041c00540c40030003100e04440b0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 557251744 1250 557250494 557250511
    0x803091006150f0909021c0e0c3703140708061513060806070c03030b0103180b04140f160e07091509030c060807020d1d0d05010906090b0603060106020105 68
    0xc4101a009100d00300c03d208226491601400c1c05907541703000d405030303004184005002c54280c0700780d00a5030602d1040d1081509610014204880c0344008103092016100c64841c0840c2c400d110410034918803144100641d82402c5e01004503903403030804115000c030340440c011050250794000a0404c8000440a0103020619110001d80ca0b04404000c200d10380301c40742c2e220ae651680f00000b20034400340040b511807120361311031040f5080c6524004088a269240003418140750401c00554001110031009050351b005001c0300c501c1e11035081102060f09446404102403003001002c0903c01d501060005004074a400405010798031480d80900c4828100c1d00e041c00914010b1040041180041443d155411b8500384140342076284d40311191a2400341c1c001c0404643c12801f40402c066040180140200491600110362010700029500841c0942c00300391042203900100380901200b94050310603d64006400c00c580c5c0940c2c6001c0480c60001c8540c03d11030b000d04400000d8603801030040a2180141 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 557252994 1250 557251744 557251769
    0x30b0705160501090c0e011703070210050c06101a0c03070615030c080106031401090c0b031905130308160203120c091002150c0421060b06070803091006 67
    0x540104440e25040680001c01c212450030380d000c0450802c0c410303c00f659018101c10120182810703500503800344103900032032644030305c0381101460b51130110540e80701790742c11103803200b14402c4410b0072206801108030311074082c0144c000348460741c03019401c0581224400c0800e112205000014814030b8011842d1804003504100040000a103659000034800c003030840c4203500b1152a5120700a840e41150460450781c1c0d525a014014456400c05103000800084000d02c2030410740e543d0040028030303a01c101c800c640c00110200b40f142001d1500c0c4000071180070800c22442c0340c6040c00552407803101e601940070a54510110300100b40405c0052142c002c1da800962401600640840040c58020f0041c420030742c1c14880ba880035651507001e445030490944c0108100d200c03018140c5403103a005400c07a13458050402c01085009051950701d007041d142001207069150860400b94042e00151403020f5200030f0004051007004034074801745024135440c4080315184004910b0b40b00c202c4800d1301503d0b03000c405 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 557254244 1250 557252994 557253001
    0x1e0c02010204080303011e120b0a0f05160c030905030d021c02010b06030103080a03060b0c011b08060d0b0a18080c06070c200103141303020f0a1e0602070f060203010e06030601030b 79
    0x154500d80081f0100717010001d00310726695030704a0005201030001282d1103180310041c019950401e01810151204140d001c0041e0b0030b00031201018078042c610440c080c0030f0a0820042414001c0d41d000000300000f5040d90b4410f403000c10001c2d00d80d102c00c2e0300c0548984503643d20700784061051249020400001c0c1c4454236503425034070340703041641059840c401015225035011801c40c85440150154041e210001328084a141c10484036040b0200050410030101c901041007c0e52081800c15105400623481c0c18a41c507041c1e0740201074510302c6942240c80740f48514860420001d2070003070095501903000d807907450b110707032404492061045202030105503000d800000e020950f08142848982c05040020b0603040030340f80643d2502c02201c0c2c403070a01c0805003420060540600c421404c244940d80a4150aa241d80c0c43c04000950503038103081d03e6880091100820085604032144540c000ea2020310080103071806a001c0e40c000d01a8450041a80c00072500900b40058098182c03907004900700c07203554 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 557255494 1250 557254244 557254259
    0x606040513020f040b030f090607081f05280f06170703090f060e010c080c19020708010504081e0a0210050604020409060b0a03110412110607061e0c0201020408030301 73
    0xc41c610022185940d08011a603810a0800010b000420740940280d40364580b66003801220b0740018034001442e000403040029841d07002440942c05400240100740700d5000c40c0b0780010302c0c040303600078503048050140f034070003141c181c581c000c441c00d0400c1c4c1c03800c242e59481d00040f480ba46058031941000c84c0c1324130840440b03212040481075000e069840c001482c42d141d5114584507031100503003600c01c145c0d01d200310501c0400a01030302c00c40f507825090800d000c0c1000c071b0400d40030388282c5031640503040c20503206200e554400d20942c8020b0120740001d004034206401d0201d040e41c045c145048511070081c04000d942c48075101550700072034a6402801c078109840c280d0001910000f070003980d01903401c10001c00e400f001e07480740001401d034200c0010b031101821140a0201d44554038034804d001028802000900050501c101d08254003401c0708103441c031136002040b6140070321103009000a0401041441903010103003180300007035512206100015a040e802da00701e1107103018083c0580c104200600529 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 557256744 1250 557255494 557255509
    0x60e0708030d270f15021c0b010305010918060f0b150307021644060f0711120702040209040c0c0c05040e03180a080106060c140c010e090709080706020a1a06060405 72
    0x812020300d0140c613201c01c841001f41200d03400301d41c50301c000340d4032003d40300c0c2c9581c10f100c3d180c0908400902040030f10309140108070b08007080000240016225010f04d0140fa0726074110040d8200c01a01e1441d05620700003082c21640c0085449000511518103404c00050300034841e6030440e80c4240300080e40c0c509568080c090350800300c180182515107654184050700b03000c84507599450317501c00501100e003801d22595541105c00707040c00c81004242c40b180300c444580410b80e5081c036010f02c00c080791f0390041032000c039000c1d00a641503154001e1074070500c170f400c281e04826200041d40c0f0440310740b010f11b525001003008550124bc400140c0f5070041c071000c08a03401c02e601d9039294082c014000b042543c1d4504100382501c8a5030807246c0051a82038810303081080101c000100d41500801900c808400700e80000e200e21045840c1e01d1040f540403000c240e91070b0103444d00201410400040d04c03504cc0d111000030756200400d100443d03074607900941020b808090040018090600213100c503181500d01820800c02 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 557257994 1250 557256744 557256773
    0x17030f1914240a15020708030304050d1b020d060b0909010e0601061103090d050309030f0106051e0402070c06020c030d05160308040c0906091d030901020703060e0708030d270f 77
    0x80d0015080d01885640c800c000c5000400c030400d0200160200c1307000090501800b0760101c04154024800e110004001103242c420040b10740c0b610b054210440c90b5040032402e4444006508030419030b421074103001140d0405030380c0050035070700c100094a428404900300ca00841101a450b080000144909403203400b00d004010f425a0807a4209031030003000455042c9961021511070b440020501c4190405205144501100c0390003004584d24010101d00b40c001aa0381e02942114907400c10395450366540d0684040c075401100b4520f0302900d4000c080d64811414810078400d10801d1411041107208100310380c0c6070380311020940a41a8070f50790a49907460702400c100c0355400014000f01c0c8011a0b03106041c000d0404c52404148214400080054650544103080c0340c0c4c0c00404c846005640c0025001040729800300340058055028811141040b8054200d10014000000d401440207410b8105000381d848440c401c2600040745c4440c0101c1000515005051640c0245210003040013010806038 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 557259244 1250 557257994 557258041
    0x13121104050a02070b0c030103021f0f0f0915080a1508070b0c010e03030f07080a140f100b040801020301050f030c01021207030e041418010605010c0f17030f1914 71
    0x1403208596a0380c228442c2110306c94021800030004100f580b030400c502d03842020741c0b02e00c0c074101054450002044803c0c8600d0039814408100715000450b842401814001d103010900c019280b00c000c1d8004220b80402da070741103800e0f428066150154004c0400340070854880e0b03402012170030301d841d041c0c62168000d031f06444419541d4a21905100c1001d200840c03143c5005c2c8078500c401d180a2030060302401011b8140c1c1c02451411028001e00d01e152079507140c1081804101d00100d130313034480075064070328660341001d0558840800e0010f411017054010754180c0b0002c0b03c0c60311310851480f051607a02c140e200385590059218034040c0c401940340c40010014180203240a007805d05114012600b511030940c4034051041d40c020800072840a903025001111041e10001c0c0161031529000800f05d0f80110b03030240c06180c0d81b18500041003104100c03000d4003400c0302a0141c80c0e103031500001060b020110b1b480042c08040c100206000d400a00c540500c0022004401d9525107960308000e1078400706141034203 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 557260494 1250 557259244 557259247
    0x20d030e07050916030608150406200c030c07080a08031614040f0801050f09060c0f0403200316030f0305030a02070606151803020604091509050c13121104050a02 71
    0x181d240c49280f81107209280100d000b03034044003000070041c00c0b210b1550040143c0e801021110408115405129400a401c5440828112034042007480d4140303401340c000542d0500060b00007100c14002c40600310f83c0448105652645940d010747c20f41320907520038020700c00c040400005229002000202907411880c1c6001c5407403a00401a01c059580b00e038001c1d080303600c44174404000c0b0880074007960358400d100009a00e0b2078205007885650715200548507070031a08020541880312525117090754011908146e0380744240b04203c1141105441110241c0c0c0680101754808402c0310316000360404880d13020076828000e001f940c40c200d40d990005071515102c80e400300314003400300c2d0250089602a105010a0351294a00442c000c2d2a00c65511a50780200c2580d25007000943d488174251411111495808501c3c070710031300e04c003401500ba0350300180126803034807040c0040d20740404040c00c555000c03242c0c03510a0580b1014002041d03517890400421034100b1301c09504132130520346c1000b600b0201807903016 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 557261744 1250 557260494 557260499
    0x4050607180f0e0402210c010509010c02130603050c010f080601080604020c0d0e0108010914040b060f0306010f061701080a030c020307180b100c08030a0b0d080409020a0806060a020d030e07 83
    0x9803142d40c010f03484841406402c000f44070551034201d0941080c01201c80c1100401156500d0803034a80b00395820403418070a012512132160703400b50101c000d901c2d500500b40a0180c91102102000304054001074410f403160079403d034115401220800040e2525458040f5074be680ca000440c0c2068000303103000e400c56001c0c070420144a00410121486030295260031388100341a134001410721070168000c0e0300060802d05e00545c2179000f4500c054003d030700145614a41e43c1d42c400400c00c840103103081103030140b0a107000001c0b00d081a08452094442d1940c607070030642c0c0e107540300321070ba00428055041d01c3d81080c1d000d80d001900500e40c03800346510103001e07214410382d0b030001400b00c00c507860040a41151202d8243d4418903002410a1180441e4100740074945100d444900e058000104466802e40d611011406180d55a42d2120b0f10940d10014403071384c460b100c103203980c00b075048130341e4150201380440049a0300b842d041d82504c1c10348566500900c0488400c1390300310041d08540c0340442003406043c1d0003 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 557262994 1250 557261744 557261759
    0x131d0f0603120a0509030607030b18040807080c0f060a020403020a2913081212070503090c06040b070318211407060c05070e0613020a120c09050a06080405060718 71
    0x9041614104e840d519201d03043e0809140c145a03000b0151410140741c0030200c0a551760354003160503c84040d50481816690381d1904a5443c403a251029151420108071016004030010308942000300308003c0d500c06454003110342040e401a40002035200d0089041803058045c50074543c540041110703400c1102141030500d262490340044d00d410105020341c90180003e6504100301d00c00e100e940c41900d4030704001e03910a0f00c805040034000c041002030020100f040c0380b0081040b4031402d8401802d0380c1d40c9560b682c5c07a05125502000d800c0700400c4600080d503254401040c0c20400710350b07140503a5100d2103035801805080d01c1c00380800321643ca210303040d0060284020060200070303000940710822a1a00350801c0c501e4040300f030b0310240a20314000204851622601800c40109031158005038a40300c1503501502c4000b09613120281003440c3c00300c203404c010b900454a01c2260781c190785042c41c0503111102220001003c84010f840c540c4030001044c09540708105210f16130040d00e61200e0143c0c2c45a19 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 557264244 1250 557262994 557262997
    0x150603070309020a1412071406090a0911040e09030a082d01080a0c08060c0d02091507061b0201090b1302010e1507050c0d050a0308060f0402070602131d0f060312 71
    0x210844d4824903a0402c2c143c208500039146c0d21b400800244401c61401100001048890032614016030b000301e400c2209840d10a01030000d803038828024011906c1d510f80c0e17600c06400511030711103030380c5000c404581c0c00d03039000c81160000d0040ba5205196603807402c5041010300a00481c1121000160385540b4061189454070380c064244880075020b103240328109440110616040220b542c1c000a040c4401c140c401400c842d0745600e0250050b85501d840000510a0a071000419144450020b918400c0004640c01048400030792007080d00f10980d4058201d080350b11a1200a11414403000800d481194144940001910524001c502018900082102c250340701b103490b2203102c0040b4428081090502c081c154a100540741c0c11030401e0b941d1281039668015450280601c00b4250200344a9101d00c2d000303004000018000f95640c130081d140c014002c0d070101114121034000004081803940448a80904201c607000d030101490b110b00f18a02151030029140960600c501c000c100c0d0460300c1d040 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 557265494 1250 557264244 557264249
    0x100909050309040c02070501170703140f06150301050f06070c0302041404050c01080705120405010e011b02010e19120219081801080606041e0807090509070608150603070309020a 78
    0x7640c2c8450a1809002c107484042c5002030a41d0080070080c0400d0345c1c08100d015401284400701170054403564810f5000f01031120340c2c1d80f800c0003000c0412440102c0e40708440e00541081c0d414008100b1030000180132800207001e000d610030082d070808a0a8540038001d4102680100008640c1680c0c1c0c2d4001400c4a40394100360206110850401041c40000d03c01441041001e0814100341d00c0c200c0c01c020001c1c4160301d507881101c0900b4000c00c0a100c0d00350300500440d9200b10081207000041c032006203e1044060384080190709104154103030100c007060682e20b0326403500a1525203400d558613281c102e8110301742e0a007107108804225400301500e04030a10014003030310300956201c0b41040400003035490403602070b050080001c213121040c1c0350007040300d08507202074030300c0c0300d00310340c03856000f2810f211036808000244500c0a020540100c5940040e004171101c0c42100c1c0c92a83e1900180d600c204119081948405503440d4034000382020001194401d8803840c1c001082c560f0303a80068901c0c030b402d4 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 557266744 1250 557265494 557265503
    0x1e04030507060908031c1d1e0f0f060106050a0c0b04060504020f0d020d03110a0f230d050f18090405010e0d0c020303070204090f0c15020706050a0203030708100909 72
    0xc0800b0041242c11240c00c4000d13101c1580071707501d0080c0d00c0381d104068141c00341d14182c20642d280c91516940e080d455080c43d400801c0380c1500d010070355100351030100551030100d80c84607003d03069440d4148003001a4030b18402c1988000713030109a10f88002a640c40e0049441681840705107e15580010800d00400e403107030f4461a00000c007402c1ca4014031003042d01b46040c95005000050b44440544d48007200aa20280c3c54034120120740c482c0c2e4052420709072404d10003410a100c4218180401007504006203402c616002c64941d0341c0007031035100c0e030354031034405986000c10810003144c00c00184407002089641c0901059a102c20500740124040580480e41901c8030707503540e451361244000c280a0100403000c2850300300c14400003a000a40c4a100c2e00304024401c59692031048100b04500c05161a20758000b01e01c00010399484800ca40c003080c5114006005019480001ca841401401519080c00b015801581035580700749055401180241c2402414511030800140b61900c501466550398402d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 557267994 1250 557266744 557266753
    0x20a140a05010c050703020c0910081203041b050a0b030702010209100201140603070f0b070609080c06070311041d150a0b1c021806031801050403031e050403141e040305 74
    0x12801d280b42140c0b00802c0b8901007003c20440000801d500003030070348503c0c00c225110341c0c581d00c17084a1941c4507406541705846500a0f23001c02180803041c0382c050352090b4003030340e01585240840350400d903040445000702e940c05481c0c49014070218a030103020310360007112400018136000b4070000140000015924010042c5c4d103545060b230030030001514940d00108103400401405080000c020420400e078001c030450710501044907030502002d070704920300442d040901742d51b440d4490a207d0f80c40d1362085440304046400d02c0c0c00701d1918020030f400ca41c11124401103182c0e802c6007100d0904158000506a4654008020414038480d030b0303a88030b918010841142120307039400180460702c01111515142c807038044d00c107100009080e105060f030500441c030116400c668075982e90000030303040322809400c400b40750f2800d0704100815405034820b09402200ca40e02c4c002c40c2480c0e0700d0040c15103908840040c00100c100780507180310700092028050892600c001c00d03050000810005140360095401950036510 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 557269244 1250 557267994 557268013
    0x305070b1c051005040e0304030611070b0108030f180301090c08010c0905030c060d0e0a17130e161b020303031603061212081504020a030605040b0f1c0201020a14 71
    0x10340034030420000e030751500d062280d46090700086007030321114440e0500494a4842180d2000820300460f40513681c84030f02004000b2907a1901815508500412103114410704d0001c104414008155400042d07084105458680d61031040002d407080c9203085a0199210030789140090118030040001d400c26800001e426140c549004188034040e0340503901a40007030010410640301c0794211031000241f2200480c0c400006100c041c03801414002c054890744217240440030740e22078407000b804031210700a00441041d03164444200481c0c4160b900941c00e00e03642400e442c20b14010003d1140100c500c01c42400074031070070b40109081d0303030088031118043c03c007001403400140d806120b140041c0c003034220690b1002c00907686e24540c086195074241c082c01020703000164801c061111003103030b070b00b0081e00554980c0703045500980680070500545208074181704005840d070902541d450f100d4940280b900c00a0b58034151160b00103109070074168118011002c035400460b40c1007000da164007140100800c02c030b20 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 557270494 1250 557269244 557269267
    0x150616120e19030323120103030c1502160b09120c010204030b010f0323031b0a0512090a120204020d090506010f080102120606030a0b030609030a080a090b1f0305070b 73
    0x50070040c0d402d03034084a02e1400d00100343d200101c0f01ca81c59058414406a003030300c0364000e001d40286091001b020312440004010140c1c410198a55140b1880503000c4e59072801616070140d0184044040f0700742ca0180c829400b15001081c00e80c0c00018007015a106102e0301034129280742c0c400b004c03010041c0e40024080040100d442180c1d07006151440f20380e9041c07400c598400c405890007025541c60420001385900d8039070300500444038401143c0350810b10f4450954000c07030b1a03038540d100a42d014000e42045842c1030381502300311108550300804080d015420324800303403042091103405070b80040e0b092280c41c020b06d50034400c5040c0e4601400080c58039603d07000c0224294442600410800d90044c80506201b10013188201d80244048406580b66940d10241c10010406540784503071502c5840148040b8a4022004040ca09490742e61016641d413080b07004429a14001e10003000050314200223007100a400d281c102408402e652502c0f40310780d594844500c2c0c00e426800550400300001111882107 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 557271744 1250 557270494 557270509
    0x607300912230301080d27060c140d0504150c080d2a0c060506030c0301060906060e030c0306010306020a230301090b18060f0613080607020f0303150616120e 69
    0x240804111861581400700c071700e80f01c02c881a80032080c4070960401070f041002203426466a050041082250f85a071007100411882d921300040d614004410100400380c00d0104c1c0c05602044542c880c07a280a20f0b0a9222100b1800403100404211240058900060200b0024000821144c030b011034418140c02103807592081600a14003558001280c5e940b00340e03001302120a5254001c000017074aa641e02c008203040140d030039401a415442c2181c04111003190703510101c01d4400651302c401000b6511010b155581400502c417550540c4410010400184039030001c02c01e2440b60700d061800441c2040350107028085680b0aa541c1c2d101c08401400301c020700e446142d40c11901151001ca1000c5180011030361604045c0038070f4060410068050115141d10007200c40600500c0c10050794140c1d43d001203900c44c14107444080c01401611a550520b0310000181d0b4011850381289001800d28442080550b0740610801e44000c0380c11203c880124102d00e00d041c901e882251245804180d25400300201c2 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 557272994 1250 557271744 557271797
    0x6060102070f090b060d0f0f0b060c060f0a09020a03080301051c081b01021b010501030c090203010b04120515131a010b070f0804051f020607300912 65
    0x1158450402001007002e140414400c407408020b0001d90301c0301e8800442c00c10300c107220608545ca82401c4065a100340542e020f80800d0a64a204200e0000d402c2e080047c40e01c00da03100c9421503444a03002c11954914041c03207680104d00e030340f0000340ca8101c560105402c03c15592040d40c243e003002c0010440340c28004d01401c0074200a0768440095101c5640ea9074880c010b220941c02c54aa1640c1c41d0302e000f500940c125542e14211980014081da20040c20303074060700090004030744500e041d1900107594500d500940341a120403841da42e0509044c54180e8402000300c0d402603a151241c02c0396184c84064aa4805004941d04a0486840f00150901e90882070030b51131106504032a58004100c100790900075214669404000780084403240d0408200a01850300045d910040341011212188280442c0702c1c045401602980c04c550741e40340b0192900c4850585c0c010210310799075a00c00441c030000c500302540d0b107007807807000981c82d09640b10000140f0a40391254041102840840c602d00340018000c0034 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 557274244 1250 557272994 557272997
    0x3030f090603050c0421170405040b060c03090d110d060606110a03020c150408011d0d020105070c0305030a021b011a0f0f010318050a2306040c03020603150d05030c060601 75
    0x24a00300b08403918600d1081b445100a00c2c143c54080c51102643d10385c00402140d00115403140360070341908038140e03d510a10810344120f207804400619802c140c41521b00f1160104003460420310003800740110b550514134200c8030440380030107440704c80c5e0b542c1c00071201483c0180304c006101d5003440c00c0901881e00d04d0001c4841e9910150f44400025070010b101400003d065800911040b0754507021601409541c0000c240d550034102c50308210326403c00d03036020743d0440c242111031000601d84181c4c201e070015643c6c8000a0411803060300400d0090700211707004082003100600d801f85442118440c0d14180d030600d56165126201d00c0d10001409100c0c041c202c01c1103540500c0d03103644000290441019031212814075459807287e803e030242d000180491903410000382c404040d12403404a82e807507000c1c401500004842000d00262035400605c144c401d03548454181e01250941d020081141c100030305044610700c480901000603101c80140407440c82c0700c0c0700155201c00031542541e0808100906050 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 557275494 1250 557274244 557274251
    0x2306010806030715051c09050c0603090601261603020a06030c0203032a031e0a0b061602040f0903021c0203250f061109031506010c0b061903030f090603 67
    0x542541c002c10010104ca2181840502e001602002500c80b1300070700d090810303201c200c140c4101e44140140c11010b106440f6000b511061000c450801503103000a6900c803504e0b1340500010700034110421019a21150460103000140a4014840346080c20007001840c0402101c4c1081045040c840305c0d50b8080e050f581001d0002d8500301c04025643e001c020b140c58441f845d80d980d0031401c40c015035281d01c55a03c00d107034144c1d52850300c19040010906035006040200745a02c0000d0380380a02c0d0b01ca13040d500c6d00d0040103075290500805c5540c03101071a01c1016a4032a580780700034500c60982c0e04c80c0d40405403003a00034045241c945030310549000141800700301590001c110220000c1d045400304601c0c41c0140354010101806414022803040380c881004103503074940503041c0c07404510711003d080b1400e0308904680c03c0070302030754043c480c12000b41d40c44c83c0444c00749a40000019800f01151b580030a016100c01e0050400e054050004000340d48242c0114602012248070554011b0160000c4e0400e0305091 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 557276744 1250 557275494 557275501
    0x415030501020c0f1b09041a01060503100f060c060f0b190302120304030203212b0b0d260904050a02090913081b10110c010b220b011223060108 63
    0x8221048840e1402d4071814a0350006000c02c03212000050307240323080040500700c943e103d030800740c034941c41501d240e40c0c4540022400607522006040d4042550540c1c2d466200400701c65031004040c0c01c0c0303a200c50542c242c441c020101291a180211200d2241d22441260014514014051000e074076002c600401d4204200034005a00d001130907550f02d5001201c030701c0b050380f0101e03042d82c458010121003003c03501000e24089426403890052400c4550b00800800403030090604108034074280590081c03246030b03008044008580400044004005141c1800b49013042540008088a5084400c41c1c48190302052160130790805106441d484501d42d5400352517042c85485410180c001c0c603000b0303001104001a0340381115018010a104007a01c00401e0041340154200321032140c021144050b011340c0ba0a2461076540741081c041064510600c07402c24000804a40101c080d100340340d95241448428015021080307071920503400551503400007000307821102100c03801840742c090b011604000400050 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 557277994 1250 557276744 557276773
    0x305071d0603070f11010212150405040c05011404030213050703150303050d050627061e0f061b2505010305190c020106120303022206090909020415030501020c0f 71
    0x2c40e900010a4206001003071140a411140700000b0700c809500e84d4004a4601314000c407080d03d181c0100860300c0904080f00b1540300340000c03608111805000d40c06240c004108a50250010402080c2c140b504c0500c0d254494011842d04695843e005000360b9a420070820420391610035410b8052403114840c100a1031928010304600401c00c4880041c2d54071000300c1d404d03541d20000306000c0c80744044040e1070791544c00c0945000120468895002c0d003001868015902428145001c00590080c00041415010024031109412076482c00c00010310000c00c80300507841c100300c0c070350156012500a01040300340c461005203804d044d6202034107150500d01884820945540502c0c41c1c100016000107054180e1074040b0f0150000d98440c9005480c107000722070501d9455001420f400502d040600307800088814090000c0c0700381e100b00b82c00124030003018800e40701960003090180d40000d00201e2a03030f0103900100d40d0010964800c5901c0da50001c5c00850107103040c443c480c5543d0b4800044c01b41c011500c0f00 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 557279244 1250 557277994 557277997
    0x1204260304081b010504051c0302010f061a1303140f01061a0307030e16180506120304050d08091e01030b0901060e040c110a0b06092208030c0702100305071d06 70
    0xf07412500010300800b0110791083c401d903001007a0003444071280e4035000040a2551203000001c0e0015401c14221810740000da000e00802c980c400c00c0c4164540c1070446088090350456844d4156030f10401d071000010800ca0b4052810046205c030281985000c03124000c0d00711203569000001c02151001c1c0d2206183d00c00f0705480d401005424042125080300603c5c605000e00c84900c00340c0902401c0c8086040034001009860180520314108030f070351101c00c2001186080142d410000c0d5004000a0000342441d861013000319118942240c02e03c055000041d03c000b00803070110301807069000038401d0715030307150041da042d034003040c3ca100c3c2e21035041c0722004141d451a0442140581c0d111400d040e42c051040b00345000160029081d0784000e8500d28051070f45134130030341c0d070035200c0d2040002007a95410580080114041000b070003420101b59a0ba0b040a1504014240600a10b0138044200543c9900729000c00714600d07560002864a08079102902642c820b00342100200407158018640d0303250340c030 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 557280494 1250 557279244 557279263
    0x310090b160815090a1b02010b0411160321110712030e0a080a0e06070b0a0b01050a05030601081506070b01080706030903051804150e010e15030c12120426030408 71
    0x182e942045a541a40316809442d52000c2a4811b6061550000b9099410f600030440040c00301c406002400d60804001c0c0c1c24051042c2082a0031170003000b450010740a22a96485206000f041003c000242c0d01e98a080703655801007182c2c0e072440003403d0340800100303079040a000f105606081180d02c01d03000900303503103040240004188000c0020b000311000d0180c24102e011840c0100110b42e0340e1b07443d01d485411184142d40c0c81882a0034200d0301580c0b036020f4426204800c0300d13a074502d0b0540e80c41a004461821025240c05810202c8030722801c0740d80c4401c3c000f0700e00c4500070454101d245d41761410940c6004000e60040342098130385800781c0c00003503000c01195403111a0401c0320720048071082c0020000d290709030180091981040340054020610180c05049406840809040b40d40d102500c941200c0e0704000c10350706800104221060345040f6200280030501103044411890400e501c04410364040d400c62041c008840d1114254144040c1c04444110747d0381c1c02a6060901c0c05085695881407075 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 557281744 1250 557280494 557280499
    0x7030603030e0117060d2a0305010f06060807030213030602160309051207091a0913150605060d02030901110a0201140903090607230d09050102060a060b16020310090b160815 76
    0x7050483c4c00c1c004007024036598107c80e05980f01601840d19154021002248411a025420241e40c0315016009105250880c2c0c05e07a01c0c0c41c01c5550728070b1800c500035404464440000c6000003000700c0821080d201605100161540c101030344859420050200c0743c2d6a40841e02c10b0146d400c2d20f5030405004079a00040300c80078140070540c00c05100e101808811441c200075080548441004141d0742d800341c0c00145c0500802c5041c2400d240c1002c204107032086400340c241c100c0c034208541000714850b903004650051055000007000131801400c044030f81d100c29039040043c0c1d120012212500d0b01e100083c0d401c54980401180352032070780000b1400d14013400d80094a120807294600550a1032038440c1c0c51441c08040c00d45984209402001d030400116004032401440340300005003040ca400e00c2840d00703490110807050305084034001244041c40840740b00301c0c0c1600944e40106081c0c8418000d0f0703620240728055481c104d2416a07061181300078202230620400c4006818001081ca40118801c0751600a = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 557282994 1250 557281744 557281759
    0x30f1b28030e10050301061e1d0301020c1209270408072612010504020a1d040b0a0e0610022b05160c05040e0f120a1707030603030e011706 61
    0x3820141c034044149000c2c1038121552250210010342d0102c011416030ba515111401d01181081402c0b000441c049001c0020801c041c44001040e803490501e10100c4100400141ca0070005a03603940c10001c6004100d400c4100c00310742d0004601e0300350501c0b040114400d2201140e0003078031019070035402d0043c00140ca10307900011100244110a1100c01c6440b461088403080c030708140c1003c100c145c2c08680d013202c4e001d20702d00c004501440d0078021071b400800c007a0f9803c3d402c02d0b15942c44c020035a101d040e5165001e55919003200756501c03294000d6000302150060511603190110600c80070340c6070340064004640100540030350a880b005c02c80c0049480303240c840021180c064000342c803c0e204a0301d016034102c0c5440d44240800c5220034502040c0c400640d000d0018041c0c40750390a9903101d29075482c1540750050102e41c40c0400300c00028011400107454050103c032805490b044007440c00741c81607000642c440382c0034014150086070304030300c402003840c0901103208509403182d0740860190000d8407072283c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 557284244 1250 557282994 557283073
    0x10302120304030803130501061212030e2e0609020a05031f05040905160b0c100506150c071e0e070507050a080310030507050915090403030e030f1b 65
    0x80081c1c0b0007450740060990340d40c0c00e1244141d414150b81d0b000c00c803119801d01c0804203c0c1c0b0000000180900d5102a065603000b00520381900507180d921305691452045480c04984a07038950304158106020011120580380d540c0080829a00715801072401203004200d03484420364800c1c00c0703980c4541035203070078292200c90825004280c00a603010543c000d060180141c14418041154040b81030b0740c80c03d030700403a591086000f215010f66541c1240640000040004e0003482c1d4000361ba001c1c0006140300c00040c000c4a50302c9040d000f03400b11031400d521546080c0026001980c0140f0f864011503030b031b104841d28154201c0d940b450001d145c0c2041003c0401c0c8541001010007210004030b501c10046626441c0c0002110000d407107500c400d41d070340d105000c0c0005144c00d10f0420203000300752029064075659010310034080d01c401d000d8030480800d0f540d41200001c1007030920140032420301d05405582d841d2074422002013012844404c414054111181e652000314080c4c1c00c5d5441c1c130781c034060245000e10 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 557285494 1250 557284244 557284279
    0x715020d0f030f060b040e0702070302030606120f070618081f0c200c2e08130501050405010b100516150221040201030c020703241d010b10020109020603010302 70
    0xe8902c45107803c0c982000070208a00280c1c00181c0103032864403402540b20b41e40c1240c200da0300e00c11407002039090f4001d4004600c0d94140040311441c58101681295081a2a400300900e4084d240d0f010703500060340081e01c002907114070208580144110001085105549150826222070044810041503500d0b0300d224401801084403000c001c2804000400c500112004661103d021809580c0310724010409078800200c0c0e01c000c0c0c81c415a00d46c403600704003042c4420070b07100400c014021010f0200ca0744482400a9024014141718600c03d00022a082e0f0742c05061110744190110403809008080c801002c1d612101d600c21000b90340c204950810285128154100034860106011880e81803607494003151600c0b004180e004504c00e03039003000303840c01194003261036100fa800005d200510003050b8180c1145c1e43d2007135542c101079811001414a10b4420725070a030141100f26102c10380d444018034070051520980d5080c2034811400240480b0561364000382e003074070050100a205064000403200f01c0d0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 557286744 1250 557285494 557285501
    0x6040201090608040b13231e0106060c06150503030d060e0105060405030a030f23090f0406030f0809010215010914060a0f0603020705030c07060810050301020f03010b031f06050c0715020d0f03 84
    0x8440441e04aa80a1540040f0b8076000300316101c123030610004800208400c0144034210403549203582e04021013415541c0c01c80900440c01e8100d51003401001e0100e89540c050000780050003200d44005005460055203414035501644017500c105018031007040192404543d0400c016814544042904800c4109980c10091030f2030030718810b500074155505100e07201c1300410308124111181043e01000d00d04002c20b850090000400c040c41014010000138424005024194414015101c40a5074141403003000d000c03da0000311000d48441820300500d0a03502e0701504007070140c3c1d2a4140606043d50810088200c0c80782204041c0d000032403005205017401602c440140520568000682d50200201b20040540703003d0102200458000b403e071505100302c0740d0348018410041c0c1180c0c600001001e080e08024094104c0c1c03149000c21134404254414034001070b0159844050305c501340701c02090f02d424919000018030403c3d0300316030229150009660021201645800d41c207450b68002b00b02d016 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 557287994 1250 557286744 557286773
    0xf0c0507060b1c12230703020709050114010c0c030803041505060f0102031801020c031005010806070207050d1e021002010222120b0c070503030108060105040b0438060c06040201090608040b13 84
    0xf091410490b681740c1000c078014603403140a54216500c5e82c2e01c9500200840d5420311071800c40f00d52030b0140031025400f0319410141c103070140504440041d96512940055030040358100d0f2003540003200f64000303c08500c625900b090f400c0c0d0380050306528000c0081d54901c1650b1100400001072101c000040c0c0c0b01300b10311240b019014083d103441c0010f805074030010305000e00500d0640e02030807000850f490302c00140d00e002c4682c01000401e90703c209072590042c0c00d0740d603460350b0521000b42c089400580c1303070000032585400c40d0364001030303459900c2c9080c800c05c0080f44d151114070720307030301e51041200c0c40102c8504498142c0cc80c04000040d00d403440303480a10b1040c400020224003010000041c0d02401103080da04841041c0d4050015032468030801007242e85180813072505102400e0240b0104034110150f83d140c9640744660b20220701c0c0080001d195030017401c041080359101d601004115640108240c0041c2813900340000c1c50306080c1c0c1d900000160040200c0e49014140b034078182071280c04602c00d0311 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 557289244 1250 557287994 557288027
    0x40b030709090b040b0c03191509090b01150e030c060d290108010e040305160201030b0613051f02060c1305101707020325060f0c0507060b1c12 63
    0x220400e2483c04010a0b04101c1d019100c4200e01310009490b181c10004491090000c810070b40011000b400e40f51000b04245040201400c000390070100d0300800912078410810f000d00041000e0f589015020840c2d843c40321705032400c004803081d003104692000940c0f0021902c0c21180680c4804619120310010a29180300109400450178400300c0c600200c002c9070740d0800c00f81d94181640c0e8a400c40ea8000100680c0c0060001d2001c1201c00301c01d516115060395240d10500d408204140c14900059003034202e50780c00885244000c20401c464604000b41c0031484a410441d03010048400074081d40320350f002030969201c2100080c15442040b440c5001101401004042880303458144078004c100d00007851140104410360303c041500e290000003503d40081c0624000070720754100d002c14085103203d413041111710584982c03600001244c0c0b030241045180080d91801d407100c10030704149041c1e8289801850040c1100c2001d4908014403000b11a04684c02010b03d412031120140111640c0320301103007111 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 557290494 1250 557289244 557289251
    0x100905120c180a1802010c030c0203070302090a02120105030106291306050a1209050718112b180303021809091e0111041e0b16020a061d040b030709 65
    0xc030703041d00c5002c9850080407045400c12100320409410400c0120110019000c69051841d07480003a20030aa1664154070150a0b0f0340c80941d240e002c11844c11080c1c03800c02000e9008100009115410078003070f03004140c124000c0c050f580ca0140030b61849110030550344080204e88601803503a80c6500110b5107c0d1300c0c1c1441c4103501980c1c1c3c041c02006a0440484000064000070a500f07540c41c650059201c0760307401c04080c0941500c0c00c1d0108148442400804824070303280d04002040340b90410141207100b038080c2e5403507000007405543c1c542d448403045000b40031628004602000042c0800500c0d100784e4181001662500012850030408070302d0b07e205075101c44030404004c40c00b1008074105e44c900c0441060711820005d40d15040d42a500c1c038808242e0880c80a0004002c03420f0307010720080215505087d4903a1040d00c446050300560b1000301a01415007414281004505261415000030101454032050341400e0f0045000d500310b425a4881c481c41d21402c080090765401c0c04400000c083c0040d040 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 557291744 1250 557290494 557290519
    0x110a150305060405060d110105090d060504060617070305060609070c0f05100506060702030c060a110d0503071d0303031305010b031f0b0103021e0a0c1e050705100905120c 75
    0x40281000b110424080d40c20300c00800c0103828a42c001881051344040300401010300200111007235045002d00f903900130480741014000c41c10900c9214011030041c03c01283c0d00b0705120645274502c025545201d015801b50030100041070000ca07a150b00288220f071640c589417070b00502101e0821a0200207000802010417282c200500043e4030102d06a4021043c440c50340c41c502044540d001c4e0041c00303501074206210700702a5252400c01000c00c0045810114003142920b103403a0f00d0000c03104030b0107011800c0041881080d9401070b1415208030300f031180204d18889c0e400f012a840340009400c0e40c41d800060101d0004108007900501e000c40c2c0c2c0035040b101c2054841c040141030788101c071941371202d0f103400880c413081e500c82d00841d034007074080c4801071064014103060350005a020507641010030504004180c006000d1410414541d2070b0a40002e10050705810101d00f03204240d400380f4422600442c0310394600350092880800c50343c040700d0f030044030500340c0c10307480c100484180401c0e030002d94518070 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 557292994 1250 557291744 557291747
    0xa0c020a0b01080d0f0f050a080414010203130605130309030f05010e1204031a090d0c0f0804090207022701090207050c0a06031b0207180c0203090907031d19110a15 72
    0x48030340b2002c1035600e9081c45c40303003c08183e440443c20000d00e400148108010061580242107507500305114201680384041e039900c0031350898200b9200300c031803007012060420602010340034140c1c01c0610007083d4142501389541c040c0c169000c0d0711000306510035169110003445000c1d4080940c2420b0700c0251003486401081d04d481640c0305010460b1121680d0910078800e42030081c8051184042600600035451034207400d0f42e014246280803030340c0d60290702844000071003240141c00141020000540c0b0f4a41c2481003044111000305102c081401c40c01c5800c0d00d100341041c020781121404040141e403050b56040207420401901c0350365401103100c010000364913130325030b22118420401ca140b03040c11110304c1004a03191055031186091034850040d01a007108010b0f131042d011075000340101c1c2e15104042c404601100700480300c41c0d0200350f440b05142041e00c0d034031660580c502840c5c409000601e20145000314060314544000c4c0480b04038240400726521a031110030081c000f584144940003081010 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 557294244 1250 557292994 557293003
    0x60606080105101103040b1e0a02030304150b010f03020f0d15090c210b1315030b0114130b040e030c0d0f0e03030901030905070f080309030c01080f0a0c020a0b0108 72
    0x24141c00f40840d807044219003880f402480b40210302c00000745142504e0081c02a2640e00060041850602a00d00311255051030000030700d144030503070f0084c58403071405041060111192454524009041078113800c110381e0b1140c1c400039000042d083c01038954051040c80f010600503145440443c030714000c40300144400340881b200449000c96820701030300000d604220740505103801200c404503560702c1107043c80d145941241d5810304001d411815880c0e1001d10540588051800304107104a015500f031091118050511340900842181e0b4964040880085805242030001d02c429060f52481160540d54031074000340c550401d07000440752118992101107894200403641c07903022680c03001941581c0d602441c0126041e017002400f031803c02d8505801075000d0071110004030740b075003d2043c020419a40c80d0345090042d0038040700450701c981c1101300381480c1141d82e0380142d0520440b141041258007184098070350008c800303000842c03144000c1d44245e140686c0d180d001445011420008140c4a00004 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 557295494 1250 557294244 557294249
    0xc05030a1821170c060c070512030c030a1505011409030307060e03210610030509070509100810050103020a0b070807050604030e180103021e0d06140708100503060a0c05070606060801 80
    0x4030a00460f060700c200000922800342c050940307030483c6001075145031000c40603011060160b0251005407401c0f5640c50300c0c540c0f088440124250020040c80405883c620600e4210546254072b880e0040c202400a40756400303104420690402c00030b10b4071800c0e10188195012960302c84000d20461107068589916500070302092055008082068a0310700b0740d02c030b002c030f000350809801051400e401a4086002c1c020040c0b8181542c0b04400c00020b00740c0703540000b18070895001d00c1110549090128250904401034401180e0b00e05090041c07015a80340c6041e00d00b11120f124010703030380e800c2e03500c1c02160300e010300400a00503000c0d401c07c0005241c0c01091007031444804075500000c0c00d80081c0c21004020003808040d4100390003051481003640b8102c82ca82021800414400b2a0035580d52014191050024000194094241403044041d0000714158100c1e400601c003480d03990800010a0380c42400900108030251a46801140036008a048541041c0c1250701031140303d840d240c0c0039003d200f0a1 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 557296744 1250 557295494 557295503
    0xc0e0a09021905090f090a0506040b0a060e0f070c050a0c06090f0501020105042102070f15030c0c0f060b0402071a060102191109220506160c05030a1821 67
    0x1040030040e95410329440710143c5034000c0410555031514615607030404401032107081184240c814600100b8410805244524070809504001e4a05a4a5102943d80030751204507a801a0342c140303d202e903150650302d540000140742c10089241c0b90308119240c403042490140c0000d4004a000c81d88551060251083e6904421500e801c199a00300481c01c0b40d40442d40074001020004580c0810640e2004005100c0380a10440306840e4495511b04a002c00035809240d800380c1401c5540213031138041c000c0c03603101c600c1c9007842c0304100c0007926145442008c0090091170709565510410b001d60b516415205c0c0c0c240c2084100341001c01c280d210f2100c40009a4102d405482501d03400003581c0841d01c40c00b400300780d02c40341c901000740355001840a00c08019000d50007100350b00800181e00840c1e400032129550140009010178180440c40c0303261204103100080810074007004145c08100004222400c1d1802c0e40340502d1045000680b408981e11540c1000c9292010700d9600c42c541c90411004210042c001c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 557297994 1250 557296744 557296759
    0x130c0f060302031b1c110405060408030d0c080f190f050106110f030f1b190b041407320310020a080604091e0f020303070c140102011a06070c0e0a0902 66
    0x50400310405018101c80341460300790078245c0421100d01900b00e001c0240e40b10108900702612400051615041500840030369800484e2004081403c7c0c094040f01030100c1c01d00000900700601c0358550050010940751800301038625403156011a94400c401d1408181c50401280d61180801400d620045647c000c2d50f21a13210341d00c00800c0c01000b290172500c58041007610b80700c5103026070035070900d030840b508280340252a81103114100300340000040c18810700158180303252902d440088410407240c03007500c5a0009406201740c0038640c102030411024240c0045a003140410501141940010065018000c2c1d0400710481407403038001c0d181e10801521484640da99600501c07080b9102c2c1039000c0c00f1891602c0c1000d04580102c1207800c075042c041c5010030880090b84e00800c1ca140e001030800c40da019456070b400c01c0610480c0d000015000400d100070302604010349440440d54000d0b80046200c1d1000240b14410021580d0310034005000c8503c00003030b00e2610840d040c009003241c10051f4001d608 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 557299244 1250 557297994 557298031
    0x12030c0801140f01050c1e0f0d080402010302090409020d1b06030207170a0516051c020a030e120307050a060501080106170a0602070c0b07060b011407020306130c0f06030203 76
    0x50240c0d034142c8400c182070b6140c01038010200104401c0f10300361141806400c11891404ca54280086010040402101001e0181982c946440d004106c0292a480e400c2070b41030a994580c014406a00070b038092a005d40c481d0500c00004001705816500294005e40d903296a20030049400a100c01414040030000b02c1c0c5503443c48143c0c203034803131880018140030500302418070301c8003198081d00d00f00805150040c20b220001c0d0b282d071100e180d4801d0507102070340300230080d004601c42c3e14012042624244007a0010f03846507035000c0e10446440005511400d001007080100d000f00304250744980e5001300440340041450300308400100000c1c003070200e1a5007001c5001c04d0001c68031007442d0140d044a401048088004e80b00d00c802074200038002c441c68105684000703540200c46020781400385c002c03000058213006240001d01400302c000030222269006001d800096034001c184268403d003d140341030f00b81c2ca41d0341340c4056020344503000500c0c0142040e50125000d64545c0c0914400c0802038088410751f0b8 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 557300494 1250 557299244 557299247
    0x31e0e0c040b01210c14040308072021010e24090604020d03030b0303072a050915241201030b10030c060302210118050609160804080408010912030c 65
    0x110559010b40d0851882034130304003001250b0082104883c64542091100d801105000084d80300d0f9005654000c1e000c14205c4c241b110540402d00300301d80c4011038034040084000400c5400081460003055040c0038034002036503200a400a4400400c0d900984484012100d0140346503881c1402c40d950107560b007030003d8090500010030600540c7c008001d80c8010500740c0e0101c000d4182031711600d8241c00140b00041c00a0004d044081d100070b2030140c0300d00709d0181524089003021150b0311030341c400d60740c401c00e0203580b04000754194180d40b0281c0e080080f640f00303900581c680324221030401803200c00000390b10029203448031095060ba4860340c00c0700155241d0343e01240f000a254040548403121046080007070754002e5004000f03d0802c1c0e81110f40c010b411081c600d48403002684020320100d041d0000307800302e6074a0b20074160f200108690320071413802e00d1001140c0002c071039800f45c001c0c40440b8002c0303002e1101020a413002041903200030b0203003405520304280e00b00304404190011904240883c031042d03 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 557301744 1250 557300494 557300507
    0xb04081005150904031e0c0311161401140c060103051b090f04031817100216030305060a0305011506110105040308041502070507080307030f021606031e0e0c040b01 72
    0x10078141c145050310b01d9500080080400000d8400c4042c48454801621034010055130074602410750303216100c10407418100a420342c018040381001e15000300114544107008100807105075942c012508482222500c0165501003160a04000079000400d050402c9c180024800b8140d074843c2d025550711070203104213406002c00f22034a06a0081d07001c03001401da0544181595403190180c64624520090780d041c100c0074150396000020902441c5013051005c0000700301d24528030b05c80314402c41c03400080c0b04030f201c510700d840c2030014100b580b1040403560f2565107480d44006181c00000070441c00000b10461018140715104500220341030170b0840c0c000b0302d0180704003441107805442d108541e81c0c0799510f001039440491440c03203405a091000e0030101c3c00801410015051920080d0781c0c40b4080c2c10b0161406480d0110003003154440040180300c40896642081150001c0c10081100340005168407086001502018261807420100201d56680015459240e000c140d4080001100240046488 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 557302994 1250 557301744 557301751
    0x70807060e04020a030902040c091406040303050d0e0a050708060601030f0203010b18040f020a170a1b0f12020d0b091602070303081905040515010b0909060d14070b04081005 76
    0x481e4000e0181203041c2482d400070103690b046880d000981c0724490b030029080f502c5030404040000c030001002d1101c1000314408000075030084514030b003440d00d142d0b4010300074400e4a40513622142c035040045650307201000400c49566000041d5440300781c845200b146e44180841d100b50029003070035286520187c040c800c49042e118400c2c0c9191500e140d00e6800070700c415201c29400c7e000b60f40c0b01d004010001142c03000e0b00d0100c049982d10700c0c00c1041d401d0a991915405441a400d1515000d0320310001058221905504101824021141c1c1c55550084ea08800d161001019540c00090900182c9040754040d0410000803601540aa2140103041121401d00450a40560300c20642400801d0013115081d40c40080e035900362002c58031450341e0b0815943d0a442c2121164002c841d4042000c494201c1701d0301502140640904002c52000040c00184002d0302503405403001383d10020030b2101c00e409103042d10b05450202d0300340c2580c40038209a60f910a04c02da050901030554800840349060154601 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 557304244 1250 557302994 557302997
    0x120f0c030114010309020109030b0901021b1504030f0903080a0e03061614070f0f0302010b1e0102071701091209050102010b06033d080a0303060e07090e09010e030f090307080706 78
    0x2d480103001e00560003040d13001410780c18001c244800100080c002c94506204420005c00981c41d850b02c0010315001d0402e046080146801036030519112454480c1c010fa441509031070110a013010311401520100303c0c640010740b00043c0051040c06d019001581000d881e08150708888a42d82c0341650084969220300110002640060851000c0d042ea500035040b124050800903901c108550740703405800d82d04280c1100581d4541100d60002e2400100c5034003015642c0b007d640c01002c59000003034907203d4600072922000c801d810f6080c52030400b58040c0c000c15900031003010244826010241012140c0d200d498010b6080420750b00c22428014203980c00ac0307101c03001c40181c040403a4031980c40850752070800e03507005541e41c181441c600c283c0080b4030000c2106074060301345144075050007010703501d03950041c01c11110706d00240030a5540c03000300d41c0200c80c00400049216112049024094901c4c05d818410501c0085425014086107000901410004078212442c05a540f07910380d88503207862080d40d0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 557305494 1250 557304244 557304269
    0x317090904060b03030405030312010801051e06010804031b051f140112030c050312040c12080306010c05010209041e05100b07030c1b031a0703051612060506120f0c0301 74
    0x800140c41500f0403507074004020150707410a0740302d1000c40c4c40c6812614000d003030700d040c0c400104600d00c0d082c03003055049400000c00d61860240b049000d40d03411805008a0b040002e42d00016080c1441240d00420295074400401000320381410081d80e601140c0a42c4011a03480f0000420a401544681d018219162101d40746036843c2030b14000448151100907818401d1101540c00007035401d00080ca01c99180d5054024035081a00b040f1196080710741092100840c040803800200b10341c0f4091740d600507000d1130045000401c0c0d281030360280c025103090541050928520424421600d61118442d11550300d0800c45076a5204120b00560303003910400f1a086000c00c00c480110348141103840c0900d0040d04e50590031040e001c44a405460030340c2c001d59032b051050031b002d0b929644081003503070812100e181c14080c909148400d2290100540508810720500b010b100301c032503805402c058000c003001040d0319180c00400c038401e00409021160307000080078200002d030a403044041500c5c162005041d050 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 557306744 1250 557305494 557305501
    0x314060a090b1302030705030106110109020612060a0b04180e49050a0f08010e152116150909020c1509010c02070801200a1b03020703170909 62
    0x880c020540d40c1c1d54281c0000441070240f2004082c0c0c00190702032440350b9070300e81d50796140441c020820308035401b1104059060034000750250781ca441c10b032548448181d0003ea802d80760300000418500b01544507240684003c1400901078080e9850143d44100400081c4801c20101c640a030311100f00b0310822134140b000c2c81581d00c0301061b41c0e0a01c3c0c81d00400c08c44000040c942802402c143c41407004c0418000b0300f00003011402e2590052084c61801c0442c2032902e829410080758440c0341100a00140600300c25070007054180d80c0d0801c1101d100000b400c2e01c0e00001c0c4001c0c0d15503031180d442621100341d410314003000041400425030750466100c3c0580d98030400d1070402502038040e510070f00e0410150b200d03400c0c07402056580c55070340301e010364440800003c401d048420b0280c2040816840116540d1502d103a90036a00000800400c06103704640d50b42d440b2149002030710020600303505801c001108904010401d50000703070080669000309402e455044003012110b6080c07045070001500b141c03460010 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 557307994 1250 557306744 557306759
    0x120f0325231002190e030d022104030f060501301b080105090705040c090b1b0f03070f110f2d15130f050a1701060b190314060a 56
    0x51030300d508440d034291038841c0202d82c1590240e801042c40a003003000724a5207040ea1540082c5c4103103402c4400e4003c3c0003110001d240c083d4485031002c81d5001000c40c0080c418454042c504201c40c0650380c4075142c021848034a0404d030009000901400c440d10601c0c100142070340d00409045460311036042030010b4440c1107580c0345007800704c07108494250321a4501c000306162000b0b01031244036840340700080c1412464841000103803081d0120f01014425646401c0c000f01e0307400400c075941150103550300c0906264a1111500d440c8000114801c9404003040090404c90600e40343c0080e24025070b0800c07050120441046180c3c1c081c1039980f980301e010010040500c3d010498070f110340c48002580800700c41004000705030342101d204688031a203540000e0080381c4054042d05071010b404070303025038044941400041184520300c0c4c00342000c0550403181c040a50002500000c02500c4424915a01d0700f6291450800e951030b0388038043c02080c2845503400000b0b03624588170f8864000140760760400b40c80c0441 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 557309244 1250 557307994 557308043
    0xb060d0f021213020a2312010e060f010f0303050f040e0c1306020c011704020a0806091f090302062a0a090303030b010305040c0b13030b09030703080112021806120f0325 74
    0x510606c4400d80b415001542c482c618555042d0b6204004240c1c42a8440954140400101148405082240103100708252114001c00f501d5060030411307503401c1d4202a1114900542d817020588513900d004200380c90a103400582855080402c0840881c0d444084c10f07620b4480c030340152400103402003001d40740c213518000800e40240c0050614004551518106414140111161816588900c1600e89420b44980d40c000b1000c2d98881c00b04160915503a0003034179650003611420300d46c09503443e01d5030079811440f10242d00d60070790300500359a00740040c00500750a02912043d00424504514158554007078001c85202d51f070700c04440414181004656410354004050904081a04120110000e40020b100600036106070004549540003482d006041d040140c108030789604040d01c20b200103885090328a2000c10300d845068000d5a19400441c581e1015a0340e00d0029100745090090442c40100041042510400700050400c2c0680d000400040344014000c040c04000501c0441d0f100740310341c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 557310494 1250 557309244 557309279
    0x607120e090106080705190e10020105070e09010f0317160c09061e032006040e04050115032f030d030c0f050f0906160b0108030406120b01050703030b060d0f021213020a 74
    0x2400c10b80662288c1c0031911881181d4176440160790f50301e060246a07500320402d61803c000440e200b81080d070400c06084a048403070300c0024090300e03881c0032441c121110507050711030044907000d003101002054200300815400b80d00c550000c207071502c0360103d600481090034000c1c030000300d402c2c489a90b1440c0c1d0f480040d0341d480e0a484054a034494100b88540c1d803114002c10040c00800006440b0f030806080050846490805000103050000c03003c1000075841c040e0340090b036850001c03100207122013101003030450400000d0180d150280c5102d00e216103806900c080200c200c559900e0385049500070f003d0f5554440e0040140c0d03000c005001a041c1854250300410050950b0303404003406510f9aa07500301c480c0d030300303810000f005d41011030b09209041d4071500c0c10b0801090590244a45250000041d0440c8151100030b401c0548448c0c50030660785981080703603203c2e15000d5003000403511204500f402508078480140c4040540300c04190304d010400002005642c006154885a40c60a41c1101c40d800500 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 557311744 1250 557310494 557310497
    0x1503090f12030f0e0a0611041a090303070c0608090f010501050d060509010212040c060f020304030804092c07050a0b0c0303190605060a03050a0b0108040c140607120e09010608070519 80
    0x85a65640b1400300d03014206600132100010124010380d450301001f501c488985680c1000c205000400008243c010f0003400c410b480c00205e0350324101c01000c01d0551007125000750141381c0e1a03800290040c1d009100701d1060b0303060401d80c0d82c1085815403943c240c03803003132041917484010840084d000c100c00380d116a410180792400103140541103488860071580031903050b074001c11114410407609400c2403a0800034051072024601c0e00d42582d40d407418030302642c01242070996842c0d0940c6a80b114090041000003c180f00c21240321100d40e50090f9180d0305805281c1c040d02820400154103000074050b5048142c0d00005141559a081701a00c0c0e13594140e0746194070f0301d844840c0003c01e6120034000b440340b2411942c020a2610b800350400c001d84d5800002541000710801c20000031450100a04c81070300e1810021902d203100c800000381c058080c030729010340700819416007180c0940c0c0041c0c2c1c0e160303031040945040d4403682c0c0e5034500b55140d0800303c5003040840c004003d441640140079002c1340c00110715 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 557312994 1250 557311744 557311751
    0x61103040305160e09060906040609151e0c2f120c030301060306080f070302100c02062101060810050f010c140601060e0406050328020d0503041503090f1203 69
    0x102d071a81c1c1c0c500344030038071040300ea42c9003c241032102c05071218940d5441413000c8020078081c240400544d60360800140080c0c14165140f060408100b251441c2c0000005441c0052003030b0f400042d20329580c049501c05002ca0240b41c10b9015107050700500c8034030f990402e010300d1181035008012414041030380c02d011651281c0075030010081c051181c40083c000f07070100400295200e604166014040b11070340e8120001e20b600c0b16039104e181b400c0c00580641602da0688030074055000d03002c0e00b5214400365000c004c1d408000465400c680c0745142c01c1000d164024150018107507640c5105c140c0744608140c030203031280a540c00c814816802e18119002c411007061504260001003901e5181544c6a1610300c01c0344c5400c403c5c010021180e000c0f100000a08040b102008000d00d00000a5942c20b002180e02000700d13940200c0040b0000c0e40042601e20b240c000d45040344c622070714500306449a029014402c0801e6264005680c4a03129218543d03507154469a403901c0c0500d00c0d2a505a0200101e5044041645 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 557314244 1250 557312994 557312999
    0x206010519030b01030b09060105120d0f110d050702091302010c0f1e080304031e2f07031401050c040b07112107060809010218060d0b04090f060b030a03080106110304 73
    0x40e010b10f21402140115a0040c4a083c5502c25600b8041d040c0d02c0a407060310390000303000c4481c6000c901c002140c2c1c500c0c2031071080d5400e45030055030205244002c0018500885c04041c130400d80000c01021800d108550791040e07584c8001c00c044151101081c0a80010a078907441c40c0051901c100301e0150600800c80c1c000c992600d9001c2c803559046804085070742100c0442400704064005021040181c003001c42c03003110070030500700140f01112089130781c0b6560f04840b244100d8055502144407036880c0e50000e65031070300c0d100d041070728035924401c502d6407903586400009011600303400b00b900d055500c10300c2854a4a1f1194844041519002082a40c041c45030341c03030b01c1280249020144170913900320f40548121450b046c40a020305000419848150b401000744120f0703501c0c0d8000040030a8802c4404603180c0c2d960402e000000c00348401065001490441400305001c500001c512180744186421702400c0034010a1544920021200401143c3c92600611500c0d00480b030b04141a8500e81c1224140355 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 557315494 1250 557314244 557314253
    0x5010b09011d031906050f010305061603112206050403030c0f0809130c0e06090f100219060b041a0307052416030206071115270601060e0d03020601051903 68
    0x100200260103a1201d50111382c4100500c90246c0c81d844800840700c00c40030340c996100c964454100070200c60702c1d80e15061112581c280627a0226004280e020308254507024011801c9000806140105514010031000061203600c030341e04a0313090302d5060740c50000c200003541d45d0385940c010041c0219018141403000c038003191500000c0074211400041c1c003140741610008040c0441043d04110740c01410100716010711502c408c88101d51600f42601d000048450f81300d01213062038120940e101c0c4420803c0359440600619800c800079140080350104140c0e08042c03102ea0529500d01101c80d0503410107502002149401c031056806e00c0005804080d61500c0041c004210340d002070b00204143c2c1400844600b419070412480d035002e10f8909100741440c502c41c8405588240001c0c0034088000307031070300091500580221900c2c056590041c1001c0c2c54142c5103581d522200700f40034076000215102a51a100d02c0c02e10501d066044d00341e00a004240d0030031043c01449000e03491f4000700718041880c00000507 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 557316744 1250 557315494 557315503
    0x5060915100608041716032309100201110f03040201090608010501020d030c02010e030f0d110c0312070e0909010e062a0d0b06070302150f0f060904061506020709060905010b09011d03 80
    0x4851011b8101d010943d07450050020020240102c204600403082d0425010111048541c658000c80d442c0300c18522480007203001d0020392a100c0d884100c0460000846020100950702562003600e40c804020b07100c110403110100700b4810b0500590000d038102c0d40044c000d41c0080181e52403807001007140c07a107080c01c03946558016484030020540c00104072001200910400f00c0021035800305901c0d0101c1001916070300e0188038920b50b180e40c642c01c00705c0c48060180020074803404c4064200f4405280004415000b824032000303070101d13400b0710700004000d81c00c14111903c0d0405d050b0500407202c903c04099903119086003101228490b95500d41d101d269071240d004d011514884e500a04030075006100f00c501441014189600d80341441c0c007849240310159102caa03204006841c810780c103550301e062a00c042e1031b002800c0038171411082d901044895010a40e80c041c0d035038541003440b83e01d6072003800300120f1f50248038100880005004004056106160028003000740c4040703d04641846030029041 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 557317994 1250 557316744 557316757
    0x11a130207050a0c060c0308090102130b0d06050406030c064104080a0503040501110c030a0609030c06052406120f07020a050f01020702041815020c07090504050609151006080417 78
    0x1b00c4e0008000004043c0d00c6984268000001c00027541020801024182038002078019054030789000f03c1c18043c2001070361320450007420001e00501102c0d9403401c02c2d00100340d003400354900045d02014030304400215880c40741400d044e245072030300381034100320852485011000142e0b01d000e2810000001d49600401071804014001c1010719591454a80007500c05404440c40c0500c0c0e400038518210b1550f03021440948480d000240860b820085140888828201c00c400400c0146481c0c14000d010b00010343c42100d103044000c000301d1002c0405c0810001c2e0280c01c0d00c1400c41088000026080181d2076009034101140380100c41001c42240d58050905040e18540c9215039408140035003586018002c08420304a1003039100021229070305d608451a105d0350704806125000181c80c02c08130303410042500280074000c2e04200c641800c1c0307005a19404141c40340f0207076104403050020140034800041d4000d034000c2000003c120714184040c1d60440008105a40d01201e0b402003440d1284140004c009 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 557319244 1250 557317994 557317997
    0x3010c12021c15170601081f0204080d0f14040e06060d11190810060f0f05040b0a1709190f050106090e031c02190c08040302030a14011a130207050a0c06 67
    0x11130404020710003913040602032408590004d001040164404201c54800b0441040140b9003406c142e0b03c0680a8030451303015400f6845074100c14030101d42c2c4170b1700c801c0700c8619580c5c0301400c071116004400d031180154045d2036118940e84010400524141000b051101007040001c6130880303074040c4003069604132002d02c011040028846855039603000180d039501810864180090300c0c10079030f000380f4923000c004003039003440010303a02c02140314003072030559008100421802d41d82d64019100100b290190740901c3e4002c8003240089401110b002c5010384025052600b00c000c4407e06440c0c802c0020006101a502956280380109001c0014010380f0110030380040219602c16100091034000c09102c481458504d206208400d54540c0640d140c001d01541032810000518880c101540c051080b6031009506200316001c103810400100200045400140001c001d645501107031000c924400300c100039448040d039032a030300390750a096002e04110380c003481c22200d081120f581d4a41021486401580 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 557320494 1250 557319244 557319281
    0x14010819151401080408030a090f0b01090b1306031109070c12090e0f071d15040e100902030103030206010b07080d0f0203060a080c030a080c1005131103010c12021c 72
    0x819240407107242c0e84032a00a2070540601d107003944428189010183ca5504010740782d403010b0050004034440400403503080400441103580d01c0700c902d0300070662000c02e54050351a480c0c24000c144114440c2d5401c6941128207030190007004420465644d400030014800d0011444041001c22071780321362545000b82940b01d89800909040c00440d100320300510a510800f442c500b04043e8682c0841d007503042c00b182070b0140900200250000302c00d0b042d21107444400d80c5000c140080d8180c441c10500d03004e031810301541c02c00c240d1142070340b60503444240070180240e07002c00010001200030714020f10445000d484218204095141485c003070707234040d140c401d1899402000303100952800085002c000c100b1007005120304019040443d0300c90920140c068100d200104021610400a03c007801485550150800a524250b00d40d9100d001084809480c00103201002e480c203800c0500c20183d540e8556254a5100031400206802940c00040002ca42300c80004013406601c01e40d00800e050180c4d0150f204 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 557321744 1250 557320494 557320499
    0x170c1603060204090f020c0a1509020d050a02151213020a0e0a0b01090f030309150207080607021006141c031103070b0f0a050402060a0e0418050a0c0803041401081915 73
    0x1d0007a101c14014405210f44104405607d880300012100800ea610414002401002c130003403d0081480c81e002a40002e01c0d450f5407400c000c2c0c04038607254603510807a510100120b851004039441d000300f0300304c103030201c021001084400100e004141030032440142202403031138031b03182c0348919410280c415240e09611060000b029681200a0101416211080e52011491510001d02034840d0344602c80501d081c0c0b4082000c0c651091240c5800307400301a044403114100808000e585000010110140c14030300f4202050b290144100d43d980018001c20030308441c046000c1d500c210595100c000c40031b02140307100808017001e09101a0200c0ca00461a00c0f0a52a088264581c4040002d25590f60b40c0d18000404c0016036402e8240c44c816041882d0102c0761456840100e07004055110b1903040058004134040104840080d2600310f4610801d0000019035844070394640d640100d00968a044403040407140c103075442004448c1d4030118440b0199004d00413604a00116000090740c2c25036101c88c2c1609 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 557322994 1250 557321744 557321759
    0x1902190201060503030c0a020f1f09060e040506090c0307030f06060c022416050307300906082406040b070c0605031017031c0b0f030a170c1603060204 66
    0x241001008140c01440c41d01000c14206c2e074840d408440700900c00d51000500e41c0c030f1910740740e1800c800c0514100c4e041c568681d6881c4040c201043d1845001c0000348618100810740c1094007441d40111009480d5801c1503c4070418606260801408882056a40d40660728079194a002c0d07035000b080243c035001c03400001e40c0140200c00e4800702c007000c50380208510b0350800444001c1100c115411808032200055203e190050461042c007502900b40100151450318a144c01548500300d1160600d419400c01d1940f0403d8418040c01d20480010605a20000e54008188034842092a4a0f02808541c1e0f160741000161940c02c1a0840e0740103600100c0c211040008e00c00004001d8540c60410505526003d09510b10101050243c440351200d03c214001c00c0b00700c03c1040da030500c0781d186141e2071920a06d0745c1e004003c0084410040c0b06902012031101c80381400301d0061603040d0000018070503121001d901c2d540651140320034a203140316000111110a40c006142000755105d21005070b52540341404 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 557324244 1250 557322994 557323001
    0x2f0909010209030d09051c0b01050f03030c06010b0319090f08090607060e0c04111806090a080d0c021c030c2a06090e1b070609030e0a030602120702241902190201 71
    0x81c00311f4245050b80340240480c4005403603070304640301126030748038080184000c41d041d0300403d08000000c2c41284004141d003460f0f80080c1d032241c220109455440c0f2541805241550800c440150603c82c00c0d41e20303c800715480c03000170400f20201034012840c050650f90ba16088803802e0490801c580c008182e81c2c00646091702401c000340f590f16411030304100c00000b000c0d0a404038072451030b2040100245205160b142c03010030200514102c0142d511200c1061400303090308100010481c482c48040c05d0f154660102c0ca10860902a0581c1d19003444980d15a124050b030b012042104041c0250a840c800d0440c10404090029011503514481641d140c0100078800d841d01070032900122000299035410750413034a09032102c8a40055000c00d440c0d00504042c1c403d0a2403418880d04481c0e1000080b051208540003000d884103810140c240b260349800003283c84001040c00c80404c8821501c14030161a508801c16411041c0c06d42c10540442c20030710114100c0e404805013a03210146000c610400380c1e028407 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 557325494 1250 557324244 557324269
    0x803010e0a0603020a0605030a09061a03010c11120f072406120f0204020304060e01110901120c1b0c09020a1106060d121103190801032f0909010209030d0905 69
    0x141c144400c60030b5500050f0740000c14011481000404400650701010a400001b84540c01000030800c0d2032000303808403003001b00c0606d824006d6003000641500713a4401c010103400c2c030b030414002c0c168002520079840420b62140d140c01c1d00c001d82c00d0104101043d84220702d00d010420740b1a12800712841448500c0a50f0050391010514103240320034907010545007058aa40a6030440b00160349a58614101005107032144801c1129842c11008000c480c3d210801407003036010980b1100598480091500d0980f00030740315602c000b59034806030302c032070805113a4001e611074403410409044c192900c20300405c903000720143c03000254407a40c05642c56101032000d5a0803070001e460101c442401902c8800d00c1604070ba02c05d504000301c0f400040e514140034010307a100c040201d50300005140c0e0303284004001017030170300003a6219440c102c420340d040c2105000400c2800c1440908080c046000801c200990600410908040d502003100350103596080c001741005000700d84540e40c8040c00c0c031050080116544 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 557326744 1250 557325494 557325511
    0x11090c031f080c0603070c0b011401020f0c060d0b130f0203061e01080606160b0f0103030e060c0d031a0d060c030b030c0102030417030f04090e121602040b010e030a0803010e 76
    0x70030300303010541001c100900d010800342ca03000d940751a405070480e00c00c85e18034800b4010902000000c10b030303201d0300300b03541d80c200702c0903421a44c1d104a060b000c240c850414130712059001d1070400c035902a03030100d43c0010201210040030400c03074075031780c40013001030707030100d10100d19241d0b400810400c0914048444400e20112603801c560100310480c0042c02c5142c028101c54883c0c840404d10005016818010b0910980c0c0001d4030540c6040c000c1499650003001e000840100c0d04900301c83c482401c101302501c00310510b80c002001c14240b01101500288010004003d905070b006850107981e8440b03012683c1c07442e2140c040018030b135640500080071a122801510310a80048488104e6681d00006071010b030b481c03124912041c101e03650503140c41e502c135007010100411130108002603040d03071542c000c0c0c0104046100f07581c030f0101c1440c007011041c406c101c03d030300715071050848040240c189584990141c9106041500c09680084000303892300f801c140007280d00500000061080c0c860094046030401d050 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 557327994 1250 557326744 557326801
    0x90f06120308040b040510090b06040b03241e07050c12090607110d060e0615060f04140a03060e010905160e0606030c09040c09031109070f0c11090c03 66
    0x241d40c01009940082e00c09011041200e0114060240500444402a4805004001c580c2c0c0901d0080310306a000c41d02319120380d1070041081c4071401c020401c0313401081c0c101480002d5200781d46080d203100360040c10b90396400c5000790b083c030b00120413a440103004501c15184c4a46501c920007000780303860700004070522007000500c104691901c4003420b54080c41c0e4058210324980302e052011a0003054400300107000b4070300300808000512008282c260040b503e03002c842042881074024005103104103500c1c401d0f0070030100300c10003820844030f1810246160007030034000516525110130781a6866489400303456550354022a003044400c100c00240016034116032481546001c5402c40340c503074024081e5009450010015813603210300000c41d07441000081c010018900311010040c13001c4401e02045440700d5280c0880d040c00d142c219021446000d05540303421911641d80c208842038403800343c1c1180c5100303480454025a50b1090201842141d0150580b61a440d011540d80390440a00304029051800b = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 557329244 1250 557327994 557328029
    0x312041e0f060c050c0306130510020304080703080a1b050a090807180203100b19110303040b07030c11062e0609060503040c080303070206040302010b1918020f04090f06 74
    0x22003410758000c0300c8043c10542400c400710306141d07041003602015140e00d4003c000822540071034a42044080601840c201d84c1b08840c201004400c1384000d440145c82864148180b400103407007014030380d501010300314000c2204410480d0b005646060003801d40085040030401181c80e5911440039401490b50300d000300750300342c41c3c6241205441c04114907014450340000025a200e0502c1c04c00b00001c10743e581046550b134001882081e0800d14480d0108009070008a00d1050402e00105a030301464100c015030429841d9070301c054005040044600081c02104102405540d0007408541c0c441c00c100d5200e503445444031036000c24010001c07000010340a203050400c0c8000d551010030704091700d5840c100305030f4948840c1031610211040703603c1220306200004c10403000b564041003040c004c1c2d109400030f00012841e4400c03c40c66114218440c0913821040800300070250000b080050b0a076000b4000600d418410b60742082e00b907000d9006002c5668607506030b03040724074180c0b28081c02080031101c48142c40341d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 557330494 1250 557329244 557329259
    0x1309020a05040207060612030203190804022d0301020a03140106021f050c07080a050d11090f01030911030d08010e0702012304140106080723100c0507050312041e 71
    0x8045000e1240903d902044110411446900041c0607044c8400c011030500480e142c000e60300d0303002209070558540511500784240e4000c8510707034007865008110803000d20041100f43c16450600030701003204d00c000c02a44015807000e10043c00c100c06650740215600c2d080703e24048000e601a8030950440d07106654540003032008104070780e071003510420045440e44031300d14000b40701d0154000140c40001c2c0054021856030b0080020500020f041100f07004c20100c000c0411000c0c01585030440d00040b00c000082c0301984a94031102c4154030480e040c0c071445450305c0109203003075003034050600841d140c4401030080036085565598845c3c03182c030003844001414914030020040e00304400c0d06141c04000842c08109510307500c03100303440c1c10200070440c0a543d45551555100b0500c60900c00080440c0000251200ac0c01c40d60040600a0f00b20080c4003810901115000c980708070560701d501480d031700800c05540500c90105c5c8500325080039525a42042c1c024100300d9071092382d03095440b043d81c03420000781 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 557331744 1250 557330494 557330509
    0x108030a170a0902030706110c030615040e0a1509050f0a0804030f14060702071e0e010506250b04060c05181011120301080c090702030f1c0c0c02130902 67
    0x1070700702a00c0018503450b0070b41d944000e03100120b802545401802c10100e603140d804003001384103c6440b030032601160381000c1031544401055901c0c200034051000586240d052075008900954000030445803042629128802e88444c25880341c050f00391520700f400103021040108142c070300c0048015041c0140540c0e9400500d215074400103150203d041d2100e402e028800350302190400d0110241c403c0d5160040d8001d440700380b54014140021940d81e0001c186014802501042c0c8000039650f140c20b9003440108090b90f00b110300a441007a2122140c460202c43d0311403000402d6200304020704050400e85041001d940b44038000004120007400104010148080b540d0342d580030507150f0400c64800d110702280c96103071500b8101d03000d01c00e06034002c0d41c1009040c0110304940704103054942140c0034104200c1e0f1906d055443c40c0c016030051181c080c038a40400000d09120169102184120385440c5402c0103480d0100f102030f000c581000000415820004181c034a2100c00e4541080032220b56800500355 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 557332994 1250 557331744 557331767
    0x1005220312091d150612130302071a0318010b06180a0603090f06050402030c040606020c0906030d090b03090304031e1103010209180c0919170d0e120106090510050301050108030a 78
    0x40e0241030b2900c04c8607200d10007200d0101c25a0074940303800380340010411002c1040d20804070014880c1860005000391140484103800380003d42151554413043c04d2074035139800c0c521408086c0e55803901ca4400c56034405000b0004280103140000480d40c0300e10070040c40d00619031001040c1402c00c00000c00064070712800141d00c40e4810030019042c1c4a0b40081b9143c10000e0303508941151519401103072a5400060445441034220390524165a55005242e204e0805085010214520080030700800583c072000d1039100ca90541160305090783e91b1201540c02910340c1c0500c1200ca40c042c6000c060250b00b8544000095003680294034242c210780c08030701c41c0110850030b100710701c140c180413521940c0e00310708640f12500004d18038107403013405215510100d00d1074403559000011039100c4404603000410a0711442040b074031112402d07a10407085c040c00012907903640c81995600c030f0011400a100e4420380e801342311059070860125041405050840b041030f041482250703c240f011030011940004070101 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 557334244 1250 557332994 557333011
    0x617010f090504030c0204020315090a230c130311330702011205180f0c150a050705010608030a02070e0f18070e0c0304150b1005220312091d 62
    0x2a5581c0d6404c04480c0701850f554000e50250001044c0444020913000aa1001c48110f0303054609407110301052040b2074154040381c0060b1089140540c1d110b18100c01d0300d07442141041302d24900422240316004640160b081100c202c201031554a000e0f042c80501c0601c0510758001249802005842d4088000310081101101e1880002c3d0301085920a00e0060a0b40004060034402e50910301424040e610030000c00b50003601c01c6c28003c50004400040a840c10726024004c0028403048000d00c000d1030b404602030005010b400c00c0480700041742442250002c110030000307903445502a04000b42802d41640c0141c01c90240d400170f0005080b1b41d01c01c2a5006890a0054040000ca40800508114440c0d000941d541c444c60100721031910b01200541c070541c0b2566040c44208400600703442181c3c242d00c58a9000644020ba6400490003100181140000d028240d16504440b90304141003140507041103035100708196131f01e0840754001c4c880c000a000d0020202c20700c008074800140d09200028213589 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 557335494 1250 557334244 557334251
    0x8180603100b0a0e1f020d09030b0403050a0e06031602120403033f050a150b091e10050c011401120303020f040f140f01030204140f03160f0617010f09 66
    0x3d1a0340640d40d406610a0080c040081d954112500c0c409130142c1c105124015010700540701d01514807031175285040d01d0740b102c030742e08260700c90b6141164250008004001170158041c81c01405558407030155109041d00c088081c060500e800000f0b0400c2003024000e403100c8001d100500c00250426012500c4881d580c4041c0c4036140c04215200b2071070b440000310404d420401c3c061303d62250311900079070b01c600c214420500c0b0b80d1035130310048a401141442401c640300000d00240c5590700c4c00c005240c09e41d01c10803183c8c5000f2426400043c078441c082d0348001c0049000041d484180d81000e002d0700741c00f403500d6201050f05600d4482102440082000000c0406a001854a00b07a407030f0b4401360b03809000c480c800a0150768403030140c1315405655400c0d41c0e101d451450140103071b5600c02d000300e40c151074100d0006100d090300d041c244200d0100075030b54540d050007080881021050051418002040e50140c6a10076074540f107000340c80c00c80d107100c51003040042e0400611129594162110881d0100c01002 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 557336744 1250 557335494 557335507
    0x504110d0e03090603190501080a020d0609020112020307021506062802070312030c0e03060402030706030e03190203130906060f050705010b0915151213050304080a08180603100b 78
    0x101d082d0b21541c014541e0041001c001d10000d20b02481003101c100190034003c0102e642c82e861800e98501001c40001d40c85000e0300c01c9031000620301d410500c0518410b05000c2e99401040345c2c80c3d8160380049130306200503801210f1110f4020760045419412400c10b640340751a21912422001603102c0106a401a0101502464030094420045d04c0015904a841600da1441c0c0305401030141c4440500c10b40040c010191800c03503807802082047c010f40d401002050340d1440c001098016100e000c003440994003090011418401c00d080600c0c0200781d030fa50141d03030355406c400d203842d000d00c007160440000c29141c558107012550f04002030801c90302c0b1508089032100154600b89000d88009554650801d400d1006e00c41c0030059400c0b400c41c1910101c8501c001035030380501300840da000e021090344100840c0000f01c0e00034082815600c03800c9028105880c81c00c0d40b1511101c0c600f46405d0b104807410100054440503078503a8a41401c01da0504a42d028a0341c14203103440094070b10319000e043c81220002815 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 557337994 1250 557336744 557336771
    0x203090f0102030a0c2d030b0f030604050102070204110a020c0d0c09090b0708070201181103070503070b030f010605120f06120703030206090705030a150e0a08030115090504110d 78
    0x8032518804000940d81c1c0d01d40b82004401074580e8440007000b14001d00761000302001c1c14210b0042c070150003403071040b1202803841d00b100509842c2e6031340c542042d4240c4107044251400d0113928800c500400000d6600e00c90740c4140030885000b2011004005802d001c3c00c40495404184e0401501044460380c01007010b6003400b1401c5409984241140ba1504e40100c1c00c10851410083c46000d80d5210000140d0b510b0400b0703401d0301c03544540c50701814100d041c00800140c07010751120030f10502a04848105440f400032070710b0120316800907006120301000300315410148010035805820a45011424400c100c40044101c441c003a02140021030000002a00c03500d030040000800b40342c0c00b04139040c030f65503401c01030b48a21003619500d40038058900049054240011410601c0380d201c407540702d4502a14081c4c40c004c00381c92562044a0248019500c04114440b004c1c45c003034014111244008010b042000d4000b40241e40540c0c0500e09228015018240c8403007513866035a9210400b04103501250007 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 557339244 1250 557337994 557338003
    0x50703020304090b010e04021c05091b090a020f0a0c050106350109050d050d0b0f0609010809210d051308040915050d0c051e10030e0307020a0308130b070f06020309 72
    0x815600240301180c00327665005846291454a01e07a041d0410603600c803040c0007902d0350403112070040a611040103100362402c00c907040c0c80e8851140c100060819084240c002c03078a0740000d07000400a075054542c141440300030303c10b181c004c05101f0059040c00131401c88600700c4464130a4845083e022503440840c4d0168290000700006501030103445840e5806540640603070003001c92450140d00d003408403003050400b50409045844000d103000d08092554004582d44080100307080818020b000d94080112200c5182074030600e042c1200b90f444211981d482d40440f6401081031001110f80404080410588400c55050741d5403060301159240c4500d040295072070f215031249401c5107580c0b46140c00c0c042403072219800d0320422030b0102c5507004030280310401d034101e100416602c000d038450f040303040c28040e41c0592092440001039034244291600001c2c80f01c285a8015904243c000640c3c8403100301154124000c2e10f0703811071050400340f440e2512040000171980c000d181c07980c0003000c1001c4c20030420 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 557340494 1250 557339244 557339267
    0x105041802090108100e060606070204021b0a080d0e0102121b090a0b030a05252303100e1320041107050c0901050402030601020d0e220516050703020304090b01 70
    0x3800c078222541c1d944d180d80d0b512442003d110812030b1801900b02400e800101e110f90080038010055030402d01c4d941c0801c4001d41c41040d02c09400c030160005940d0084051203000c031200d00500040d0344a101c1e604100c0c0a03034543d44a59040d0703900c1042014841031155802d40e400506070b0901c00d824008a05940e1464891020380c203a02041d04e180c0003828260a200540c49100514402d109540f01c50700701000a1001c0d0300507150078400401c180000c0e40c800d60b000d207044218103041c18040312041d02c16481651065400c2008115855014040351212600d09604001071902c00c000b8050141c4800070a60100d080203441c922052069211584e1541c204480410440c0e800940c1d424061811035507411140350b0031805600280c2c0009032919040c03080d20701c90b00c01038004c0d044046505a049400301c40e004482d43e0b111201110504c044040820380284000945000040505103818004d180d20b6404100104001e010454440029070100c15a0300311401880040340c3c598400005848640880d03 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 557341744 1250 557340494 557340499
    0x10828020c0304030210020a02060304150f0e0105240102030706110c0610030506130818030703060e1014010501140a0e03100b010e0a05030c0d150f06050a0902120105041802 76
    0x8101491810000b200a104481c0700325134000c568450040180c1e11b84200700000b0750b100c1c406100003004201380c0501e40c00510641500010301904449101086446901a0650030f81d56a010025202400e0180303030410003600c0d58101e6124040d6000030b580c0d12031031500030000d0b40c43c1c0c4003503034840a00000740d501e170b07481d401c09a5403141b40c00079488420440350b10042d01c05100b124082000b400c640390075165000d03003151140c2d1910792908400303660b10320b1541990b60188a40070001000c120075110303103400a040d03400600001100c2f02c8440c4180d410229104030080c00c904d0040095a820000014200fa00c10802c192a85d26804082c0c401d14000c4980b283c05019121213180e881e449076114142c0f100098850056928000c0700b8855a01c0c0f80740501901039202401041c01454828110b0201501c224800c0d180040e011b458030064411030b5001d0340750315485950511051900341070035000703019001411824580001c2201c40703442c1061140364082c03a503410008050b41da110703c00c43d00c881d401 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 557342994 1250 557341744 557341747
    0xc01060302091810050609060402090112050a05160305060f010c051207121713150b150a1e09140a030609150506030f060c09010e0a090b030c0604030201082802 70
    0x50303403d0540a414400c2081402120300c2c100c2151454031986000e00006000c0da007041e621034040c8002988140001c905000300b5a07050014100a405054482c2465590101e50750070076040c03401c0800300080c04502410304180c100302c01912062000c0242110074070b81400440f189060150400000c860b003041300040003d03030002440804941d02c501212580e984005003e0b490048044109094030f284a510004410146c00300f1200390b2403d5a8035a103040005606000f4400039809041c80840d40389200c00101d041d4a01c07035044032440c100c102c0c0000c1041000c1418000080c5400054013501e0000b0541040000c0c2c0c5454115901c00616800302e020807017100d00303080000c04034010348001c8002904140000307070203040110b110307104044008024080e6403154060400281c00c5507900c0d80c104400c0c200c0c04031450340d500304404010103030101d000070004401c006050070506021a51402484204401c20050341d02002c450762000c113803c040803aa0b0081302c02100c148003541140d50b1070900 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 557344244 1250 557342994 557343001
    0x6020c130218090a0b032116060608031b160e0f09100921050c0318030f1204030b07080c12130203060a0b19320405270606030706050c0106030209 64
    0x101360340001c2040e00d085040314141c410780d50182d946142d40506000d0407003404c1c0300101203a25152040400a88510707400b1132059102c5901c507155400030203010420102d07803440c8800a0384140210300c071410b027401030002c0c218200340f003044011401418850a6160641c0001e43d4002c051103002200720210405012510f841c2c02c1c00c001c600540104880003048002c124050b05000710201c4080c0804e007009181004681188451140480302507181c241c05610ba2213058810144445c101580b640b2850a031200e00750b0500f20b4501c80014500800d2104103020702c5074100000c400d03640180329250594029642c1c00040b0640703842c02e414000d42502c186014028411020740121030030b610281e840110041c5100c0d2905044000d5128a8079640384c074000000701080c03600c0001a27041180300303008a581012802080c2160011200b640c500c020140703000b501100c0e0060400b1644110000070441810020b0000381c0740c50141c418036061201c0080c85400308a029003081000f503030010841c030010b28 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 557345494 1250 557344244 557344261
    0x8010c0804050f01060302010e010e0406030f0b0f15031c020307230d0c0b0f040302070308040308040f091b080a0b09010b190c11130906020d0b0a06020c13021809 71
    0x2031080d207044455008482c0d824801620505c184400c403901607540348801c09495005450001c0400012904036441d60008404124241e0810100b1481408420580c1c80c0c003101d0101b03140303405400000c011050325032003c2140d40005e00317860b080c0c03c01aa04520580c103650103078658400c1a40c000e144070400c0410b11001182d108815150706208015603071001c64000085070f881c41a100010080792801c4c1c0482c404820350500035900c648240100d51003240c07240c951498540059200302d400000006092100d04c0c1445400c00c0201030b4460280250100565104001e0f03001c070340301c0420000c0400c001005e06125803ca0400800301608804565031108109001c581c808680d003940c1c038100c045500d034001d11840196101e00e40080103440e94404803020030443c0c1d1007007010004102d843d00c0a20300490703280d20060a000305226000a2010741d0442031001101c1942d000c0000d40d00113a81e4280191a000800351790312203015030050740ca510f202d040003190200f0fa0205904121100100240344 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 557346744 1250 557345494 557345507
    0x60c0f0a1b05160b0f0d05060103060e0f15060702010519021002180f1c06020a02150a09021002030307020d05031e01260105041e0201030b1203280507081308010c 71
    0xc00c20303d10380242594131002d8108641c426002d0180d903445007042001341504055100c0340e00101c05140c0800d039550740c0c50440c1c80381c03001134075070b81559071900d0240b01c9c094a0000940800950903038035641080364540019000303010b4425500301c80d6541a4008507000e1013404070f030617480d051040464444405500c50040c21000c100524040e15500c2808041460907040f0000c2011541c0c2e400143c40e074190792070b1006504400c0c4044154400c4039488010325406a4150348a841c907607a00080c000792500401c088540311007468820364004005009405902085182701c400b070341c1c1003036652030b1030381003405410608401035000004a03080020602105c01c004d20f0550321444094190308078018000d81e400c03210142c030000c2000044e61705048800c08a440c0c949072050050500240381c3c07443c1d0021030034080111541d0307081a0000a0a60f070811700e88000c003180300c00903c5080040c2a0b59071005440751240c2c13403001d001000d0118504003101311003005000078045c914004e00c00c0840300280a03002 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 557347994 1250 557346744 557346763
    0x70215031918021f030212010e040524011707080114100b0c0c10120603052811060913290105130e06030106170618060c0f0a1b05 57
    0x816080844480c281810080342c1c02605400500b24802c0a5054800361443d090222245051507001e00c43c4240001c82c1c0e0f284c0c3d034020603404500c140310303107042d15216003002520024074240f40b06444010840456201140341522014101092100c071803090441c503101c5540d0006281d582017861440400c5065141c2c54003c9158003002c01005440e110444070501035421004007075030121040802c42d2078040c003040a41c0c0700302e0802000701580c0c4a0540155441500103407220750240803030311081d101c030603220310b8040466110303413403102c032182d842136550302c000d0b0b01c1c20340704010101c0c600c3c40310354505c00074100c082845030007000302d002c1c0001400c1183d1415003404a000c2150070f5103840369401481150082c2d140c0c40318610019062003100a10000041c168035050b658600b404907400c803680100000e00e684150003407010b0310341440d11140d0140300485111441c0c2000b0140b000317002c1e0450644203071080f1094800d85451400200f218540783c062a14650a502c02000030188680461040c0a = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 557349244 1250 557347994 557348041
    0x1c0308042411091011120f04170a031d0f0d06021306020105060907110c0405100b0433020307061107062d0b13020c0111040b0c010e1b0607021503 64
    0x52201c080b000ba01c0042c00c10a560b17041d90003118024402000074002000001c6002c406e4038100340d11242004070400f01c0b20902d81c0154044601d0304145608001c44006600d100640c0c0031424a0190101d0385c800810059280a000c0d056854410452203405807041c0444680d40141c3e0755a4840009000e0a025281c0f01c3c041cac0c400801090b8124420035504024070000401080240d08410a10008101c0104000003d40d0180c0020504a100c10000c000510340080c9010500c100d00c400418a6810801410304214244031154020383e00402643c503641d4009d40d0001e04030314080004410740c8241a0010081e505c1c11922000880400c294002201c601d4001801d690b1030b4400c20b24210360a07100850b0748403115000100d841c5d803843c2c0061000c0da8025002141c0203480d440302480c1d541250b003150b6142e2001040c9101c25003002d1103903414051182c8000c113800f03c01c1c0000050031404900c21507002e001c00041c04d005545500b510f40d01c85124100c0000c0e6070b03107000c2c54980104070040d04c2961 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 557350494 1250 557349244 557349259
    0x207080304030815060315010e0402040b1b0d080c070c0f060c03030f0b1507020607080d050402030f06070c03030e03190509100c0b01260303010f03021c030804241109 73
    0x3481305424140c40703282d855015180e00d00d15211682d00d18a030f40048400541003056001068190f91a18009800144070302104261144522900d1000306400010b403480c03d0f0b80106144550f656020201c0c5400180c4465038540d104014204518559003a801c01540c0d003103907032030018000e944680b103008194002e513802c100000c000910b49040d20443c1074501e03801a401100c001035001000b004200c40791004040a151014980d01c407102904580351a0401550780c00400c02541024440050384440810242c8410315003950040c00440b4031460107402c143e41c0e200001010303c0f040044421003400d200e0405d41442c030380140241142c0c0122a41406843d40c4c070000910240a08208412158801015440b81e07007880b03501082c81d0115114200e024603031480404071580103000841c046d010110000305c0e406e0550050145121900100c141c45900c0003200c2800b003070380300050a030060350080c1840301e80043d981140c18008078140d00000c5132850050040401c4002c0002040101415134404 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 557351744 1250 557350494 557350501
    0xd1d0f0d080a0c0f0c0612021305060c0c121b01050406091e0909060903030b04020901050f070f0b01030b04291807091401051e030a03180b0f180f060d050a06030602070803040308 78
    0x40d090740603149c004545421140018001480d1540c0640710310520b0800b16070b210803903000000c640c4a180c004444050300001c0141864801b0014a4070040b00e080c02d200c6d15242c030b0f00c5001058000716106e6a819841c0001c542f440344032a801c4c01030014204076206014000540c01d200d8003c0115040440100e481c01c541c1d88624141030081e9150140b050711024109401c800c16520654000c100032501c42000140f85000501c5040d0703910f01a50060000d0752241c58140340c101d2a2100324000d900321148200c802c244054035548a05505c40d010385038210490107140501450400c8507001108003a08110b600a16440c40c000c045040380c0c81164074118400b511420540000144642c494054000d584820007090081000820022000303120310002955040070004d142c21400040e0016100001e20040d124468a0f681c1c0e0403442c22526000040b0032400022600d1140042c0c42c1c000c10b8032000007804080c0164010401150014410355a03000603103000589a4412501100070500b8600030 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 557352994 1250 557351744 557351777
    0x23090d080916030f080f0a05042d0b0c150a090215040303230f04060507120315090c03060e091f09020f0405060609030d1d0f0d080a0c0f0c06 62
    0x203081c0d0762030b0101040742c001400c40d00d5000000c1c41c41c08041e10b02540070003000075070401300340042c52030711400d541c0e00c0c0e1110704210301c004000f40540702c01c00070564503240150000e1000030075607040f0382c400c6011650707410081c5c50720340c00c190700c109407044210786803001c0121825441d003040c020f0394821600340c115100020304044c0d260256000150004194a080320075040481c64260042c1c020803c2d0182070822542021489030321942015000850104041080000da030030313440345011403810305002c1c08582c2040e07141101e10900c21250b4054881d07580c1d051304ca02a6200074094440c80b03200050a20b8a10301d566031310403c10101140c089515104040d91001d0740c80354a0080758028100d854618000c020403000e04005020303280c1c004030400031032000343d0701045060080c28186d1161015145610b14070709140c1d12008103240114402c500c010003070754800380c181c101280d00526072900d556080101315100210005c004106c85e034000c5080c003e11268208040440d69503a03500101c00c50400d40 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 557354244 1250 557352994 557353003
    0x2030301080c01080c04091503030912051506010e0301060308130b0f030103031202040503160e0c12060613050d1a0109020901050d050a0f090803090c06071523090d0809 74
    0x1990310725810004102206611980e540e5401082950f081401c01361a42604000c132020480e40c03112401c0305403420410181c0200800c4020910607005505459079a101c1a0312054800255543e009281c00091000da0051041031054080035008105941e240c2c0b610804076400071105404c10900100d0029200c16950100d44140e0040c07009242141d00e1550700391402401c80901c42c600075000d010224035504c0c100840003d030001d03200c0c00031a00b443c00302c1406d440c00d0064072040440804000d043e0503d000c004109800000580e40181c1c1d4141b856008c401001c1e45410013503114206e488d280f018070403205417004140400f5003603d0304699031000520201d104511900380800e4080c8400040850541d1115500c410303080c1000c0340c1c00010080072000c840b51140101c41b44103020045c4a4200c2c0308205442c0100350654510386480c3e52500c640025400108815000c50b40311241c0caa0707096400c07042c2805842c01225519800d041036a291503d8044180c81500060410000a100c40b000083c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 557355494 1250 557354244 557354249
    0x14040c1706030a080a120c020f1e011803020607020f06060904080a031508030c0708160e070309081305090708010501050318010207050a0f030f0e0307090b03100e07080d02030301 78
    0x320350401411908110650821004100760341c140280001c0030003090501d801405032101c603a6540010414040700c13801202d41104944086600003071b002000d102c000a07410307591100100c020a502803140000ca40034080c6080d100d00a0a2403034505001c146d0006085802007080d034003a0f420300c10640002c5692000d003143c40716817000840001c02e0104880100400303140040340307400701e05640b5501104070565103135840340c400380d8800207400501c88028042e510141c05400003401d1218400516001e0b82880c42c0158624418441c0110710914005d030301001c4a182e1040703245448108221404010301128450b85014103505000039808500c14810241a900140c42d8581940c4034800c651804528403401d881c15990701304800380c040b034400c0000001040c400d00070181040340501d0007d2a1a0340803030074500b0f12140b07841c03140681c0e6000c01c00b00e0603540d0421002405810102c0000d2800ca40c504050000310b00c0c003030318244084004600320090711641402c84210000c0540d00720307540c0c882403 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 557356744 1250 557355494 557355497
    0x209010b090f0f120601030503040501030f150501030b01020f250803070f0b091501090501030323070305090409060516020607140d0b06070b07020309130e03030403080a110a03050114040c 82
    0x101810442d1409a401102c0d03540c2c040c1800c07501540c2941c2c168130b040c85c00e810944040d0b001245c100465030b03141c00b6220004041e41002d20018812200001c0400514000d845c1072584440c001c4400c1c0e482040005040000f2404540c0090080301c050000480301d14121074013604041030204154800004851019034040d01460407880c842d21540f60011014203c0803150040340001c12000c0180042d0a018020101002a20b540341d032602400c00140d461041121140c0204442103c10144094440d095094203110ba83c82d0b5000d40003500034508100c0051034180780c0814444400188140e02402000c1c51702150041c2d00c0c0d02c1c100743c03030700c1d03201281d081080d0350200b0021028683c290000e640c021800307081d0fa4145045581d443c040e8600c111007160042c0c0c4080b43c45070541c507142d03400d10070111600004010b0280d15911054403440002e0000d018440380c0000300d804045a5404080160b8800d01d420ba00c3d402c00150041c05001c00784152505028000e47c004114a41032103426840d0809 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 557357994 1250 557356744 557356759
    0x1707050c15071d092404020f0c0c1f030f110a020c03010b0103051311060f160c1d04080a1404090f062c09010e0712030210052e0801020a08040209010b09 67
    0x1103550411034820352000921742d10f884400780d140340351a41d001601402101250300f940b124160192103260105000c18a0b00c00e0070b240300410640c1084042d402010281841c0100d0004e140200d40c0020b0000e444691451140c00a0b9007028964041158201207004070000e20400c14402d00441c01c0d60404e49401c52085401340d0b00400040c0742c103800c3d02201c000034004904014407252110201d81199050100482c4040b10440810400304102409001002840305120884c21907401441d200200010003d000c00101414154040e07045030500320300b94140d0325500c81e00c0300e102c3c1001c0c1101030501415141400d10209124a00d0f210f03c8061005034400c000e0114a401a42d40410001805500d41c5541c0c1d0091040c01c21018030207000500500358280c040d9009a140c000e140000341e02071038001038075040a0105c034001c1468460180c14400c0381d5282d503910700c070603009500d2585a211805a61002940200e03140e00310920921550003200c64008a83e130b12000c0804901c00d00d030b041540a41c2 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 557359244 1250 557357994 557358001
    0x3170c0f0702030c060f040f06110606041a12010e0d020303130813031505060906181501110604051c02030c06010b0f040302040e0f0c0301020a1707050c15071d09 71
    0x300340a405074500050403070707081e1040c14000c070b56281e0056a031300c40d00050000e405e0089078442d8030100000c0c5924502401c841c03c0c00740d001a04c0345000b8040740d00c216254042428081e0a410352100300b45401024860218059800d071750081551801c0304680d406100030a100d418004801c4c0e070302c101289820450b03503410583d07a21142e58098482c0381182034102402001040049200004c0e40c04480400500381c10888100210064020107040c0305407131149041c2c02c690015a46035030480b183d1110051150001c00050b2007400703444161070748502c6401c0811050046c0015603000507404102c1d0140c1e080c0c0510022078907880381c0c1e001111294001d100420942213004020141101211182ca081507180c1d4005026503001410031009540124444001c509090040c0c6005007403c070003c515000b8400b40c041c080704020084400078550346400070704440d005404a030324035030f031080c1a1440703030a040701e41c5074820ba0305554030b00c002035580e0496240810b10b040144203c00008081c6e142c142d4 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 557360494 1250 557359244 557359267
    0x12072703030c1719030b0a120f06110f0a200624040f180218190915060e190606050906072609120a1110020703050d090303170c 56
    0x200c0342603004561901c00c11002000d4459540151804074183d17402142500d2114104000b18030701e600016001241c001d00440003444907404c21280c0e030781c0031801140c240c0e04030508945501a007000d131b800c00031000a10100c260780c4458007c02400d0805002c103451f203054104180d4501044818a07080c0d0b03140403544c0702c0039040066418078010010b102280c4c802c0da036524801501c0c181040415941d05000d403500451800b4940c0c0d0307403130058010b00201c240c6800a040c60000030003c020301000c6648068220030300001c10a41c5102e20801c07d004d200c13003039940d001000604400c40d1417040d03422100311064000501d500401e011a1140d0391060305210340402007010a80c803c0d0001c441d8240d080204440d00d10884591100440840001c0782c1c40310310690900c0201c01c2c0000a904503074006402c1c00d00014480007071a09944401d440280304100c5130b00082e440c00080b5040034055214281c201898664402002ca050324440d641d007003044011800c201c03004000039618218444024040c9001c080e = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 557361744 1250 557360494 557360513
    0x30105100806063604030305060d020f04150e0c07030f020c06090f01110609010501081b030d03150e04051f0b0a2903160e10021504060212072703030c 66
    0x120605820360903c084025807503c080d0f110130742d41240c4600d09204000900d5054440c07d54011815208030a102c80c1c1a0300041181c201103440520941e66411030241c02c01c0c5401c0548040c1c900c291207011507003440040301ca00c2d600440400c40009600305003441c21144040380ca005c090102404c0c80307081142d40c008001a805400584034104800038040d030611203005c10441c3e010311000d100005282d41010800d900703000c003100203002d5118651107000916100000d44010a411620380004d0301e000d1400f1004c94900107601a0490004260901082c05000704400380850f6030740024a031002c2e0000d19850980c3e5004c0d24031640711001100c00c0144a04200004000401c0c4e540341c454a5000b0f0007040300190019030340c04240404588152445a030003141600751080c040391180001d10904900035500c42c8942d04c640300f50701510000c035080050769019503d030a198003014141c02d1400310401441003180124a0b0882203500b0105803500d03541c0580780301503a4060b41d4400300c0c0c140c1501da40c6141e = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 557362994 1250 557361744 557361769
    0x150609110c060714450102160605040311040e030c010b041d031b121206100309081909030c0305030901030b1e1e030109121101020405060a1d06130503010510080606 72
    0x301c07114001200d8042d420910170150660114000c2d000004904002843c0201000e281d20b60703451884402d00c50b03036800c6800da0301280d5019010034040804070001c10040c0c0881c0700c12548034480466030202c504010f41041c00b04840c161070401608032001c40240e072801c0c0d400080406a04100b044074058400810008405100740044a0450585664440c46580481c1284c030728012140180034881c81d1000700d001c90400107140501200003281c4500c81d40c0c2c40b800080b2848801e65000a2003842e0048105800541c4c10021143c0352983d6404d00c00e44030f5210858890019140c03d100c10341ca45001c4554002d06240080c0c0d1f0106449440c02780000341c06003400e0240b05402c0207409808a540900446c400c0900c01c03180704007602280b41019001c103901c140a0304999005000a1046488840503610100300d5460801c03c95004801031007182c1244200343c40c0c000c03c00040d0070091100c0c20058500310b070070a07002000035070f80705a0b08140582c02130003030035110b40086020524624181101041 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 557364244 1250 557362994 557363047
    0xb0108151c02060f09030106081c08040c0f0b030604050709060e0402090103020909091e01020421320721031116032001020f0a150609110c060714 64
    0x40710344080d000192541c004040849140d140090550790900b02030040d8002031007104020401050340340d2100751144446207035801002442c0d8000790900c401170500e40000c001c0710300b0305000142c0702c41e040c0c1c0b2550300854030180180e080c40045885240b20345d0145003107c200380d46202c01044a0020040654002c8600904040d000e00c8080001d65840b51107600a4882c83c008210701d4916001083d0401e0300e140840740140d02c14082000214204180015001c28081042a0b054034601d0150103820b00421030035400030700980e41c41c8030103d01214403440480310703104070390515960ba00349c0d0403076071a410f001000550102d8040720009000342116628010140c0641d1100b01c11050f45010001c0298810350b403101c0185900074420340074801d90300c2441020b2018284c0346a10726440b568a600d0154001c2c00d1524a140c2c42c9544440756005030003400d440e0b20180700541240003806126003045114042c01d00600001c18440d074003884582c02003106c84010700f81056402c80044c0200040c140c46842d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 557365494 1250 557364244 557364289
    0x6030c090503030c0f010518061504090b04050a03090506070c05040e070305060708220f02130209030f071d012610091406010602010606021e0a02030f100b010815 71
    0x95a42e018000703881003c000b5001040301c014007048032825030f01c005d0250b40070a080c0520002080802040c5c0980c400100808100160403440102d0000d0505c190094031440501003403004000002c100e03042e1650280d500c5090141e150820001d103403103100c400400a5140030307070400050a05401801c00c0f03203d0301c0180d45131295039403120307401d114084032150000380200041101032640d00860b101240d20100500e4060b000c1565540103540c1a0680070780300300d4100c0795600440601e0340403104c00b184040c00743c0f40c008100409481d41c545c15400703600b10403c0c804030b600f211514400a118101e07072401d526441d42170300c0c007082507042468401129a4134000c4034031050f19402140503000040340328a00c00d1420b001d200601d1400c15a0681103601103904004041154a1380017807804e5803100c0300f2220f60b803220701c0c0c00e400c00c0c540001024000c4d01030041a10744200901c01060320003281d5001a001d005c00ac102c00e0045074241e4003203840f0302501c0c2d580101c01c4464180a00704054000c0200300d000c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 557366744 1250 557365494 557365499
    0xb07020129040e071221050703091e150207060e030c030a0b0702070812030925180b04050f0906070804084f091a0d080f030a0b011e0906030c09 63
    0x44400300d81c100d070146d601070311550f400360040b604404040240103c500e0224141900c40c0d138000c1110406204e0000c0020343e0754265207420030070b10f074000000d05030b80030058144510321001a449500c10f203c0c2c1000700c0e2400a140704c182c1404107041165040060203044a2130a96540e40d0f4055005002441141300d66a00420300c12020004e50182c21208400c80361640f800c085440d142c1b41d40501c6003400c40f90b0b901c10f080200802004c91000f51122402d00c240796080d843c1712503000781001d40119600900b007030184201846003100c424000c1040c84140ea00b10380e5405403c1c0e83c41482a203000f0040c05041003403560040314410160000000e40c1c0440c80901080b0f8404042040441861800b180301011100032028083c41c00c4801403044100a10008e210403509050040c521071400b0b0007106111441010400404111000701016500b19031301e07410024000c00c010420500807501013002c6035409404400039581c10241d00c042a502d0b000028100b1f0303001c40141c04902801414041100c001 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 557367994 1250 557366744 557366759
    0x60203090a140705090901091203020a020a0206041e0e16050702060904090b090105011707230603040303050609130b0402191505120708040c0303050a021501030b07020129040e07 78
    0x9034a1000d02e8003000744061070030312042084002001d0b00305462a803401852000040c2c0081311801c14020f9818016101d0718a058260b080c0145103800039030141d00000c000c9900480c40e070388a41030010004000b0034080e2503d02c05440f00109903005d0480044034402406950320a0000303043c034a05c050522400c0c0702041c030219041d01c4035000c0840384180c000c400c000400000744146401402c105c100c120a0240251240ba100c5045003da0424440e180030386183c03e13441680c08081140000e41001e81e60324282c24002c004220070354003c2c0c070401001d4041410001200000b8490681250605d0256100c690070400ba08034664048100e45c0d000d1400060b00034041e41c28001c0480880e168a683d828480d8008c075005ca1004286d1000c2c0815503080c0301c08640f1800d03a103000d0b240d042c10600d9036110034940607442c2144030419603110425440003c010018000b2080e0b029024a030000d000706020352010310020040e01e4806c4503040150845404a07103401d400040e48a11000103864486445219 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 557369244 1250 557367994 557368013
    0xa0905060309010f0c051e03040c150216140609090603070e090c0f0a0b09120313060f030b03010908031b0d150f06080912030a0b0a060306091a0a03060203090a 70
    0x1051501e60b550b915000c4c5080c80a4044d40c0e003802854a04140780c024070494082c80800c0700c0310113507032440010000408002c46240000c1c080c10030440c120000c143c1041c4001e58031038104c5410405881c48200014043d20041035021070224005d04490030090810203000002c407000708841e03854490ba942c001845021124400c0c01400514040c288800100d424880c0e01d1801c00c020700c1c014074110314208441c103441c0081c4d40b5040f00c100c59500003a26686140303851030003005d00b603401d0883d400c8070000d550380d0401c401a42191498809003c3d001107481054222564280041c00654080001071120b08030035511011000019003418244600a440711003210700111000840d101545c0003405056071510141c0c00400040c900a211864182050754980c62401501002040c011001c51105006904840b040f0384000d45940c52440e504e210003005070400e403081401491070100800c1c482000d210b14181e0310078028155030803880c032b55640d801c0250710052110805014142d40301000404824 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 557370494 1250 557369244 557369251
    0x311010f0c170904110f030a0213090608070f08010c020607030c11070f14032109281e0501091403011d0601050a060507120e0112060e1605070f080a09050603 69
    0x515003a20390743c01070180812120104900c07a152003061001101c00290803003103941c0701001c0080980c84201c0c0000c0e0402c2c203181c0b508500c8820b41400000300769060005011801c6546d495a00c0318001d81d1040310790f080360041c0c0380130700050304000009a02540a0703048000c0310a9180b400412040c01000e065041118a8012400190076400300300251101c13003d144c000001c00701c0192401501c480070103030443e032030007144c081620008501c942480e91035014810005c00c08010406002902d05684a001a51030088a004441e84106c0e201070501c00e00000c000d5500685401141c81c1c01c0100250480000041d00795040d900c59501c089080c854031032222240084800038011941040c0c00c0000a41b81504900c0400600740080000b0680340010140c011005040212008801a0040b2441500e608a244655052400016000441400e00c2d41f04042c2185122000880d1880494a5200f06d6501400042d0b4018030100880c1c451801080742e181749060800c00c0c0340d942d5004c280d00750000c4 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 557371744 1250 557370494 557370533
    0x180207060b0303030c030f0c0f040923160503100503030412063603030b061b070e101502010905100204231f02010b031e0709060311010f0c 61
    0x4168981086100d014810815208038007a41c1185421030142c0c42c9400004d105040d810750400216445280910031100c40d000d00d04401c5965603190804407000c1c11542c59004403008514a0340603402000f014000c1c0100151094103415007a040700c111200c0e04040c280881c08402c132a000121a507081000f00004d0000f02c8901c00710014a00b84001206c074000c000c2c0c4065180d000510300c20005d5016260125629003503054188042410210018007600c50b10603080407000407105c2000010442e00124004c036201103a00300c5485807203501c0039203410350380d030780312548600c0090041001070011044d41c0304113440002004d00c80342c0c0b6074a2801049002c4001031550004061100034565070641524004040640038001c8a1502007a02c004c1810200500c00360801e0041c0c282d81d01c02e40042012480080403501c050140310040b9841c2c140c903000b25001c500c100700c00040c0030804d81c0035040403039801010f0b16240c007110b0001074460310182039080e01046891200007000403d4400b041a500486 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 557372994 1250 557371744 557371747
    0xc0302100905060709150801090c110105040602130909050309042703120c1d130209090c0301050a080f0c01031802101e020a11150c060a0f182a1802 65
    0x1e14800745c40020350f0303006050005510815a01819000a1503a0458405010009008264440c00c60380120b0448c5148019401d041c240010f000d400d4015040d62030070216440c00746a40c03110240c0c202c4031184c000802e1900b040c8074139803c52516034024098205046001c404018840100340c64034000d0890440c0403a08544040700c070310000d84551141000c1c1070074241d0480740420007100d001c07011506010701c1512901005c0244203460b80640300d0101000e0211055414030308205046078109000702c5024010b401d400155000c00001c1030314105031b400014021202042c2c0044000c0d02162381c02c900352005a40f54040180c0301c40c80c4403051440140c1d201015117003c1000c580224003e003126004543c0030182c143c0124000000c4031640003000c60b9158401040340040302c105014640b01500c1c07900403c0200b00315903016800000d01a0302e13140c02044002440709d00100c1c0b20104040c0a002d40e0b03031003440140c07408080540c024040640d500b43c102c2c141c0da80c05d4910b0039841c002c9030103440140c0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 557374100 1106 557372994 557373001
    0x90127141c050702030c0405010303080c091f080601030e16090e010f0c050c0c19050f01110102030a1e020c060606070f060501090b01121a010c030210090506 69
    0x50303110401541c0c50740e00710701600c90b80250b0b0f41603009004031008031010340b03001c5c8600e074103a0341c0c90744400010f602d0b00c10780f40e6455001030326001c1d080185c24020481900e4420030420404085a40380f48451034840300040a4400c003580341d00c059481008940300307801150605100b070719600680000c81d01681d600081c0540015460541e00030725000c14a40d10703d80c00f00051902603900c000f201d5040301d00b8014060720f0031501b813030400311422010061103186451316800f10744c880140350914015548c1748200d400c90b030040d80d03420207951b500c00200c4820401240e0b944581c1c07051034070071400e200310001199100c1e60000c15040c80b13450001001e00c10440c1402020b810150443c008005543c0c44004070402810684001c0c0d02040e0b08a2074030704070800a0046102120202c3e20120010b540d0358015101d00b169003404070198000c10580004104082c0700d105d04c442d0042c40101203508 = true := by decide +kernel

theorem cover : BRFrame.Cov 557194244 557374100 := by
  have h0 := BRFrame.cov_init 557194244
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557194244 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557194244 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557194244 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557194244 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557194244 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557194244 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557194244 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557194244 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557194244 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557194244 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557194244 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557194244 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557194244 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557194244 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557194244 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557194244 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557194244 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557194244 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557194244 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557194244 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557194244 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557194244 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557194244 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557194244 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557194244 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557194244 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557194244 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557194244 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557194244 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557194244 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557194244 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557194244 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557194244 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557194244 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557194244 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557194244 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557194244 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557194244 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557194244 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557194244 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557194244 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557194244 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557194244 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557194244 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557194244 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557194244 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557194244 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557194244 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557194244 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557194244 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557194244 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557194244 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557194244 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557194244 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557194244 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557194244 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557194244 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557194244 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557194244 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557194244 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557194244 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557194244 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557194244 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557194244 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557194244 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557194244 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557194244 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557194244 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557194244 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557194244 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557194244 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557194244 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557194244 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557194244 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557194244 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557194244 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557194244 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557194244 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557194244 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557194244 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557194244 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557194244 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557194244 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557194244 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557194244 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557194244 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557194244 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557194244 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557194244 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557194244 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557194244 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557194244 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557194244 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557194244 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557194244 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557194244 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557194244 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557194244 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557194244 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557194244 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557194244 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557194244 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557194244 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557194244 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557194244 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557194244 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557194244 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557194244 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557194244 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557194244 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557194244 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557194244 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557194244 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557194244 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557194244 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557194244 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557194244 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557194244 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557194244 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557194244 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557194244 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557194244 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557194244 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557194244 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557194244 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557194244 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557194244 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557194244 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557194244 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557194244 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557194244 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557194244 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557194244 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557194244 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557194244 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557194244 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557194244 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557194244 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557194244 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557194244 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557194244 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557194244 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557194244 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557194244 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 557194244 ≤ n) (h2 : n < 557374100) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
