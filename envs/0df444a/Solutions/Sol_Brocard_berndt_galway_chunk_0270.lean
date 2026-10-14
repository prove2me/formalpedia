-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0270
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:52:41.154975+00:00
-- url     : https://prove2.me/submissions/c73d0bc7-6b75-44ed-a925-3e6b87c7eebe

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 48381299 ≤ n < 48561155 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 48382549 1250 48381299 48381301
    0x408010b100509010206160c050303190b0117040201231b0712020112050a02160503270d110402250506060906091503070504020c0c1306140d1a010e 65
    0x400c00d041c03506000103028000e0401800c006641c01007007440e400541c840301e0a81e513019820042d1038072094880300604a02000080046e6110101441401101007600400c80d00040c00c0044d40d01030030ba04045141518980c002800562160180078022800c540508801e0303d81072080d900e490708544c0d0940c400b90700300e504e0355042000822002c0000c1451031840840000356400181074920301c04008001b0b192120001100d40140780c049800c5100003c0000d244a0905c3c20900d0b1650083c44da4a40d042030304203580d040e42101689041d01c0903500a01c4002a04195902c1c5044c540080400c40e400640030701c0741c0c03080d0704204804c0310b12054211521502500e900d01d00a410084000c080700d10600c40c41042c0700c01a220101c8256000c07124079129080401e41100082c9020200d80c0700d20740c080d0001480caa025900854a54178000c0e090700d450020340c00c8200c0260907180300b8020038440011880314141146803a4010f40444c0c1e015061421922619000383d084039003098000358002c0003400 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 48383799 1250 48382549 48382571
    0x1207030e040e03030c07060506040204030212030301030c09051504090c09021804050609070c03050d090b0a09060e0a020f040b0a0b13030b070c03020a030c080c0a0b0109150f030201050307050c03040801 88
    0xc02a80800c003040b02c059469441c0140510800d402118005840e041e0b540000803200d0b11154111000380d60000e0444c00032a1007405c03074a03a41d40c801d00084481c0d505080b800100d1740362030701030103000c0c01481c4d0014400c40506004d00c0010400004140d4806004810003e0305904a100400343c0e080c0301719414107051003100900c8250781c400f60000d8002e502101c00c014400380c2c403036850001907030b0502d801c40d0b03900080400c40010306030b88200542003801c403c081c441225010381c0300c10309842c1308400500c40840d40d2030b003041d00d4010050700a904042c4041066410385000e038025550720000404004015888402c40d1006411082c0c060908140c841000d005000c0c2440900354010510f1030514a0700e407081c0c0d4020344a400503913004050010444d010410000200c06580300e44508d50100d0344246545d081c58020500b0a219502d90545000c9040645819900d0b00074240c1e000029001c4c04289154011140c40d400101181704101c0d003800b00c240f44210510081c001402040c1c00031801c101a0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 48385049 1250 48383799 48383801
    0xc02030c0d05130303180e0901050601030b04090b0f09031204060c080c040f030b07090e0901050420060301211e02040f090f030c0201051605070f090c05040b07051207030e04 76
    0xc0400701e0180502400120315030740582ca02c03034050301d030b0500c1c2c84140e003104071049421070348882c3c20080a5152003010403001260550110740310301c009907070038000003890306c05205c200d801c102406040c1442c0311000401a25413003c00c40d030030000500450303203042100e4102c1e90030003205442c1220074a0f143c2c03142044d0136604c100010340100d0000d0a8074a05440d141c01c0104e0305100e4403005020a456900149800c2e005100000c0100040041d48500745021082c143c006d100c1210f04896004c800c5907100e400e0011b40c1011022140043e00c490310356400d0080703034070b8580003a09035040c4e9260842807400000d42511110340f0385100000c0400001d0766180304110554080d1009003a41f03a00d44051030380030506c40c040a200c40c3c0c3e01414542021805400100c550340719907600c100007019200c0e603120400c4800119401240c240c960142c0a050300c4106030b80507140c030f01c2e46a00005105100c288030030b1030410010940d9502c0b0302d00b01c43c0c0d04410070540c0c41c20303a04465826004a000c00c1c00d03501041c101 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 48386299 1250 48385049 48385063
    0x1203040203011508190606030828091d0a110a080106020d0c030e010503150603011203020f030c070314030409050703050f100302150d0b180405100902090115050d0c02030c 75
    0x1a9552512158100b400c551394070b00301030114900001102c0b170704d48140084c03940328002854024150a980c4e00c00c00c0f5040a0b01d0340024000d2400703d05070a103211165100e03100d05403e6a81081e401c0250991890030300740d00710805003901d03000a40c0c50320005100c5400c10000c2c00c07144030507101d5800d00d40c540f40c4040c1c03c00720046086801c5c410302c0b403031002c00241e000641c0000d000090a02d5074076038a43c1c0320603e40d007050018009811240c0040042100d407142c0e008101c011b8030035800c0300c0c0d9003c1c0e0b01c10103d031680981401225941c0c031a000500014203d495120003144050007128101a500d10310001a01d60507589480400c2d600c409000c0007502142d04160b0107400424403a07101071450740803079044506e04090710245c5ca0081846098030307c2c0f5401c0505000c40003080261907008207080005030380402c2c1c80880381ca104400990101c05d50301d00800da9407a80040c0704060a038031703080c40c00d91120500d0584004028003041001002070fa20311803040072103095030040d41c4845803103d8a03850100 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 48387549 1250 48386299 48386321
    0x31902060906040506060d110a03030210060501090b07020f1503040f0c06020a030215070201020f040e070f17060105030402040e0a05011506090b160503040e010b0a030f0605060306040914120304020301 88
    0x2c01020403012510018145030020000d80d10096501013034100f0500c1c0c002c0c48484150701034982e400c008103040e0b0000b5803640003091a070f000c2001603075450042d02c20f0007803881501444102488a103000d49030110f10314152180141c80b19191a0300e03900f07a0407a5a2080324121003107044141c0c032a00740421080c031213014000c14001048607011a45010f50390301c641c0d080490100d9803a100280b0403074802e4042d1303007205811404050300d441e2540c0c60300c082100308458820001d40881901d20009102e20503481c8124003550101c16980c030381c030004544a502c01071082c1c1e006030303c540c1600d000100811242420b9800782000140b52680540c84443e58405544460100110104140a142520000c42e07100070401940e0042c40d11a83c6080c0341540180c0e40420075202081d400000c103205200001c0035114900d60b810440101c0c14400300c0c0445503140107080d04003d049c4000746140c03c0c258400d208540c01949034900c0c0b20426884a2303d0004480300051030600c0c003000f0720046040900070400410 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 48388799 1250 48387549 48387553
    0x100212011508060f01020c030d030905060610050717070c0305010506030c040c02030405010e0d021504080706050403030503010504180503040f06170105010f050d020c0607031b030905030405060c07080319020609 92
    0x80040d41c010725401029082d1032091000d041c050380c8a0b030080000c2880300300301600341da45a400b4880c003e402005490026907643c010341c00050356500d0210440d1007070100b1901c80c2802d20625441d0206a0781942d001c400f030321101003101d1804124080e90240066102e400046440d103010410300d420000440101d40c0200d051070a049402500481076a054580030b2906000d0200044c000030711040418201039009480c040204003d500c5003c010000e61b0707503400c1200d00542d61f0384e03030480e0548220302c00070b80003130300038070041c885441c0c00d8111443c0c42a071080f45020040c0191500c81c1154810342c00403294101d0040d00f040402d810400009031100341c040d90008961400001034800074a42000030108240024112000c58a0780d05a030b041d86651030494410303103006c40c1c0c00382c01080c0c80318005940b009019001d0f8842c920a01560806030fa101c4050341c1800e00d00300909c03281c0c0e0010076a2a02c07034000c01001054811040018081011740c80c14590146000d24501a00380303000509442003c0e = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 48390049 1250 48388799 48388829
    0x2030f032e0b160201020123010512030304020a0b09040f150801060e01050a06030e0f06070309020f03061611071d150607050714040b040510060329040902011110021201 74
    0x6640b0030040e02c1e80142d10941e00081e0301c031903200403401402d22406441140101004068107440020341a40c180da0003900c40d084a04109c14a1581c0e901048030000d5010461000602061540c940508094140504040f6030703e00000565015100c00d00101d440300300000e41e0400400809008510041c03003c164045115418503000c603980580d03c0c02110700f459181d05a0401000c401c01c03c42001080f15400d60f041e504010100402800411206a1050001401000c0c65190100d0424010081400500c030316180d85202511390540e40c00180d01107008809d070003e034014600b03070710103c9074060341c10200f003a141c4000c151040040310307404180590014080d40300060760004a00080e80c980310240780c0c180220300c00050140c84c43d031015030342260070002407201e8455805580c105072880b6890501907003d442d461104e061018210380880f0311401c200b0b49000341000d9100e0181c690041c03529800e5541440015071501e003005c0700c01c41100740c0c0003580ea01c228168000b440e003d0441080c0f500740c1 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 48391299 1250 48390049 48390059
    0x7050a02150402031501080c100f05070b070e0a03060e010c0216090b0a05040606030e0d08090c06070501020403050d090906060201060509060618090915060f0303040b0a02030f032e 79
    0x1441c24421140403500640300041420340d58200140b00001001e1118464950313151416983c40d03000e01c0c2d800030300444200701170074000c1d07001c3c480d030705800c0099985250804000c4d07101c2d2002648081e107400140803088040005075220740c0c1420000e107015140125443c03050848860031500d09070b04041c01c54006642403001041301100707100865020010218124100d540024000c040d0345d0300060744145042c000142d1240c054011685a003a804c083d5010403a010702c098803401d00407038a101007500007400c80f40081c03800d1005011a280142c00050800ea2269100c6203003032041c0e045000403a060040070065190a801510003412040c4000c0c8049494030300464031082000c3d1107d4482c810115203030081c0ca600071003c00704600c000708281c20380e04148542d00d444000310094401e0750560340c40080d006051070507406008110280056107002c6c0b40c52080c0c183c45d0801404002140402c2100c2800c1d940701c800954010012481010b100800c8100303919810700c09101c0e90610103500e0340342000 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 48392549 1250 48391299 48391303
    0x609010b0319170a050903030d06050f04050613091502210a020408100506030f1501060e0303070b040b0408120106090512011b110106030c091406012a060b06030a05090607050a02 78
    0x103142500c1c0d0210030345600b071348441a1018099071298941521010405802a41c520340010303048075025180000003c0c40c92040c001601c804a603c541c02103801c0300c02111107032680e440590b010b07000e180d2511159600851500c240e03400404002002c0002d008804150380200390559046484000218a003034030b000700701034030740c038a592606c025581d407680069103544051141c1c06021500d10705585c48180820102d4070104028091440095074074140906030341000011a0041c54100f144200241e4480d55043c00c0b42e400204102c4a080060080f400810031035039586000c1d2085480b158609814181404100088580c050000382e04080c102d4005400031840c21116031307030034604841c1c0031080040c040d000d0501d41c0d00040a11000290010311114a64444490351154a40d809225110417004403203040c80310511581c248190b02d5951344910031a903091140501c00e00002c40d0140d240e8000800c41d0300106c8a408803240c5803010000c0281c81845640d80c0f100c0c85080081c02c15000c494000c1d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 48393799 1250 48392549 48392573
    0xf0804030e010905060a031d0f03030109092409030314040b070c030302190302040503010c050a091206060f0801090201090905090a0311030c0a08280e0607020a080609010b0319 77
    0xd400d00166a8201c003107030340700700000c0300035110240540399140015800100108101d141605002c01c0e0810940405400030906019142c00c1100640c02c50742000c2c01c0ca0010f01ca215400c681d03904040e0090142072400320f5000407d00c2094000240440f048d05003c3c2c195441d9100c5880700c0180b2008002c000342a00419a4000303030a490040517114051806a009200703000e01c02c1401c0808040401c0401d82c036030010400e8482c01d400a22961549400a4074540100310305a80411031404081c407025804c4200150518005d0001013030032952072903440344800090b049280c4594540c031740e0906550b000600b0340010300a25030204110f14004a40a80b180c0311068010704004090306040c000010400980b0f00190011065510b0b14406241800595008410f0880366100c400008112491004c0107107171024010b4460b80320a45551007082520307448a001282d103c42240310210320481c2c00c0040741c0c450011100000740d002c0c2140105450440d2413a42c5940c1040d840e010840003480929480d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 48395049 1250 48393799 48393803
    0x31b050a03030806030f07171005070203030f070e0a0e0f0f04110d0302010f1a150a0909091505040b1506040b0a050c0703050f060a06150c02060a090504020c010c0f0f0804 75
    0x42c40241c0326080042e00f006c00804c1d00b0911441140c4001c83c542c040e20340341500c054001e01c21140c006610460f0802a14421605940903804c1440010450750290072266400019490700b03810003148540002c41e00c0091390440901d5000c51310803c00c501c0c1c240803d0b10307004801186c441e603040c902981e84464007090101340034002c0c4001d45100d410503000b500711040301e954424051129070340202203c001c981c4860310040c450704818040007200030707540048800d4000d450307858013242410300345510040c010074802110b110400580c08000c5406074070a5034011445401604075a040c1103000281519400303880b60f10480b0304010800103140040201ca003003d190307041281e200d0041034042030900d14203034000b4101b4001c5011031503401c00c02240c420b00c01c0c60717180300401c007207030715510740072801400b1150a501180041c200000546003180242c110318000e841c008003002d40700c2c0c2c0840d081c0c2e04111341c500000d030b4550011002454008070317501191000d0345040c0d0a81001c0c018010102407020b080 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 48396299 1250 48395049 48395057
    0x1030c140d0c0501210e031809040302060f040201051b010c030b04140f0408090d0b04030206100b030708090708070b07050607020a0f060207080d0515090705130303120204120c031b050a0303 83
    0x100950001c07650509540c5d9110403820092490381140c0b40c0e4581e0300c012880703104501e00d41502c000c5c80c5400c8620500841e056802004030341d03101d002e00e04000c4030290080c2d050110501c400c1c10506a01d41d10b40707603480c42c00000800c0401500c103002d0240d41c07140c000d90b0300c03560800b00127100040d02900815030290310b81c015022503031144e0400320b031544209012543c0048000205c88140140303465040d0007107200b68200d07801641c0d030360901030034000e15001d281210181000800d207480e10807214241c001084d0310a444003141d842c056103150001560001566400126007030080c030a06115040c0d2090040c00a0800d021503a642d0301c05030100c480c0e00500c810780c00b2413031105110100d8160381d03200d0301d1000f04000034101000a030700e41803244070187d4850074421000038851880750342a03501c90030760300c2007610180d411640d0556099503052000003a4941c00d100006000601d0b140d080c01d041e0107503080064250545c10709030040440080c582ea5a5500c070b4004201907141c040b00c040c22681c0610b0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 48397549 1250 48396299 48396317
    0x120203190213050d120801051507030f020c040e0f07080c03031606090203030d020910030605092d011502070b130905130c090b010e0114040302010f09080601030c140d0c0501 76
    0x62201d0000c407940d008613030015145280c4204110031010480c02c142c80311380f50710000360b80e00c50030000c124106035038181c6100c40c14440480000c1c003980010480f601d150054400951600011504441c050081030345a41c2c050280910129001d100701005804200d000e064403003040804a41d4034450066403500048201866070b0a00c6a01d80c0b1404a840d070040549941b541a0392501c000b0b0340060810038841c0000181600074135000340b03d89400c40b05c010304081d40303a60b180306002c00d0446c030384507580c442d1884a4038242081c84034010840d02908490280d1044a00801d5009292580641145010319010003042001c00d400703d00007000c95240c110082041d03541e9802c500d1030203516600c0140300c408a0030000c10401c11542004440c420284d0f00c0c82e0003020300c00300450780003808688078151020100002d04c0554494132040d81e0548281c00d021646d59a640c0c940c91a10900764025204000e035101c00f400390031080031101c460761008441c00800d900c1c058a030014002200e00c00e00b0b06020b4403030 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 48398799 1250 48397549 48397567
    0x6070e01090e090706110a020d0803060f0913051501060801030602071406041406070f05030105090603010905030a0507031d0102030d0b0f1003050105040c09030b010b0a030f05161202031902 83
    0x10054001402e0303070700c240c88041d04060a903940d98161034004c1e0b0340442c810b1100d8075000c00f40001d0545025030014081c8842035804e0301c48042d00d0344054402508140c00c0c00075035000351900c8000c117000f04241941e41610903030500b402c50400d40a101c030107007032107460030040004591001866055a8000074016550f0b10145400b00f501290895004c03d01d010342c4c4108024846081410500c844c9084180e601543c2e032994100c8072490b8440c007030b002140e4184018400c80c2420b078001b95014a000d4000184108542c50359840c0d07030012580480014000a101d408150344512442000e54a181a03d8613020340180040d4480c00740000c43d519060740c1c1c00003580c40ba0b0300e840e0f1455851310064500030f041c098255004003d03103800d014441c0034908005130100458821407032841107a40007001041244d00380400d00c0c1c403561098000d54205034a4007000d6011203a03a104050142401034015084220340600140c8238809840c451660f843c07045c01049600c1c8481c010340b14841c0e05564005940361020 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 48400049 1250 48398799 48398807
    0x2070b04170d06030b0601120203100303030905010204050307180b0303041401050c010b06040807030c08120702090901110409060302044a0105070e120304120b06130903021e0102040806070e01 84
    0x702c10801c200c42c104880003051252104400303000301001e0f0b13136625030b465200c103490b0164802a9801002c1c40300d604410030200e8820740c00004264803650002d440d16649800080c6407880c140c2100c00350020041078100502030910034004501d900b580514149460900c14641c4408200901810701600107104500000300307510101c80c1e028014542d40e00d86490741140c0f9030b504945d000c11500d9511591010a600c40e0000700c11001d807120058440ca421515403c0c01b268800280005825640ba6017280014090103070181014011110000501c140340d80104405d8400b01266080460000002010310104d035900e10032202c403418840c01081285182002040074100341e100c2c050b5448c1c43c044c445110392020380070429010407210340214286c000006501c07441070344520070004c00c0205400d80061100380102d07520000081132004101c49110070030302a200300348801c4005030040c91102c1c4401a0018141e01740811a000031402e007410001580e5403440d000c2d10500611000d015915207580c41 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 48401299 1250 48400049 48400057
    0xa0905040b1b0c0d0e010306050d0f02011809020c030a1205101401020309031204030605010812120a0e0a030c0210050909011412030703020705010e060a080f18160e0a02070b0417 78
    0x1071507084850400300039600421368002105ca05001a0134601c0c0021203181035140a5030240d04540e825460542030790042d07428019490030500d01c18032805001821410500c0941203050000000e10f65802c01200c00a280900c980d028080541c6404144007500031030020900c2584d9100b111080032290303110051749103000d070300174059040c440c400f520714550f0501b03009001103a206460500c1981d072030311507050311000d904541c0d410780b40d0107100f810802c20744180700c190040c940a400244809071206110b0801c222080c058020a4100d00341d0002c6040c1070f21050340da0b00c0d032441c0960a00c610750000814982d010301c600b868404400c05504e80303564900000496810a410031242c0d56072440c5406511007100344113490101d0b40c3e1540002d101e0401204a400e02413055035400282e0361366940c0202010301c0900115170003451584c40280098081040d42c1d0110350481c1e40e0100d8900d85801c08441560040103105118018449100000c0946201c180c109912481c40007110350b5140c044100c90203 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 48402549 1250 48401299 48401317
    0x40e010b0a090209100504060f05090d120201090b01090605010212090612010f09060b0702130e100c02030d050901020c06160309050a0807060c08071b0206040b030106020106050a0905040b1b 83
    0xc1040c0000b03020051a401060707a000c2c26a918501414901c42c1074500e401240b080f0303400f02e07222545070231640d84140e00070284880700801d1201416019141c041c003560300b0340c0d9030f440541c3d0b55400020034061000000c0f070061003040c206001c0c0b1800d060000b0b403640b160805032007080201055443d51692000d0580300d000030b01d06005000c669543e42e090201d82e469114002c81185070070008940701180030110755941d60040c20400e1200010202400240500040c841103401000d41c1d1840e1807400340965065030f065a4015603c4c1d140c1200e1010403101c000d0a41012a0310400c0a00c9817040c0100b00ca560103040b0380c03c48004842200804d501401d076684000f400c0c0e024449024003040003038406081c4290181000f0040700d080c10303074180c60051003a40d4040c0031442d0b01100d00703072030381050b100070803118070146c405070030702c1c1d031b15015441c0d0780d042030700b0150250b51104d00511807801c0c50b81c0368100a04500801740034500301038a80d0f80d00c2c400050090691801820042421041c40d0421544a81d0b = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 48403799 1250 48402549 48402559
    0xf03060509090a02010f02010b0d02090a0e010c090510020c10080723030a180b0c030702030d02030108211903150506070309090b030a03050f07050a052407050301080606040e010b 78
    0x2282c1160031036125071609a049022540356407040d0035040c41481207113804040948035031241403298080018100c0014080d0230102d456660150b82584280600080c840c2242c47d410503881c1407100b00043c0e00b00d607564103000c55004101184003542c0b003c240280c0d030071007803c1160882c4c54040017101d401880800c031510402000d980d80c13207080c0803c0c000f14803071440203008201500c5a150000e42d41000c4400c0540500d80340300214101104000c010340d00400540100d902e020095240d413030070798200340d0005038140c1080c60b80e0812240b0b01b04201605c0890045c4c014641102c5200c1c050550040e1001c4204055a80001100c1c828901d802500502401007800303448410a11b0004d11100c05030044c7c2d0300c02800d0510060320740c10000f074424001030741511003601b030001d054000109034101540a1b211b51040300310340c00104400f802204002d202c202800340d000c60001503025000e907006483d90b02003001c1000100801400412000c3c1c00107400c517008103540b0a01c0103414003401c0040034640e0700c0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 48405049 1250 48403799 48403801
    0x90f2b0c1a030a02070f020306100f060c0809040f06050a0f030203060114100c0807060908180a0b1e0409140f06010203070b04030806030a082208011406010c05030f0412020103050901050106050a0f03060509 90
    0x410618ac00c00c1003200d008158025115032200b00840304244004c80040030901e042c04629164035290b003210704001035200740000e120340d84100142c00081582e220000c0c0d0075209034144254101400000d014250780e0041850384000c0300301081c2c42001070323481744042000d6007007440100444c0c1000c54031965044801807000e20610b0609100c0c55102044500c0800e21001407400380f030030027100d43c07001c0340e1500c15410300f440322079080b0031040a42000d00e0140c10f0740410001c0380ca419548a8000400c4e00080d21150502e02040404211100076024505550003403000d0000601281e03c0c81e03902a51501e04000c942e1a02d00209182c16002c1d00001e054a40100d81c09005040060a00304aa849591011101740d038078180c3c282210000307004030b0943c0f14480006620395010b074520118203031041040341d140c8850903945820381c0d041900f0070303110400882c0c100d01c00d541e40342c05101d82001c03c600003080a9490010094114420719600d98280504080d008031a14082d510080c020b14010700754a40c9 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 48406299 1250 48405049 48405061
    0x71b0e0c040501030c080108340b0405010207060314060f061c0b010e010309050d030b01020703120503040204050c1309050910060807050a0b0f090f2b0c1a030a02070f020306 76
    0x86500700340600340c0000d18120000c0c0300c0c58412100c00703040391500800382040f0010801c0e61040a400005034000e00c1c640151004080d0148001080c010101d507000d803602ca42c14017000a0038506994442c0c4101070408900c8118075030040e48064014030116800221140c003c00411840d000f003007804e421000004c01c1002c8166400d400180d900c11090740c80e40c10b410304080040d421283c40205c060b0a41d0310042c007001e00d042c0207a001600b1441d0500484907802e030f40b0341e0303400c6030005d02c1c0c1a100005503001c000c1c001142418002ca03900710000d80a61402e0800f00c80002c0050b2040344603002d00c298549010568418090140007620302c80c208040c4001ca4403a143c4c907079030340f19520419001e40800348000030300c440080c0503140444149003401746404628070420520744000b41c8d1241d4410080c41c03030244901001c0b585401240000004854a245141450f403070029065001401220408000500c84061a0120b0b50301030081c0400503251200350a00c4616042040002074040c401c2400b4405 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 48407549 1250 48406299 48406321
    0x30405040b040b130c0207080f100908070c03050d0207060507031d060c0703030804120206060d110102070e0a0504060b030f0d0c1103010204080a0b0610051207030f060605041d010605071b0e 83
    0x145ca0140f03400301d4400c0e41c0c0e01c440039541c8114010303c1d1045c2e9082502018403c4000b034004000b40740c050000281400501d440d440400e03415540100c9580d40104032084035030360140f02d184010f0a0a0800c5070812119460244c101482400c242e040d2021610012095540314425104c0c131070080d5044400c07260712441d0241c00380906503001e6518031840303080c41c0886440010f01d13606c030b508050240050300b04160358003210425540c04417415800f600d00302141c0c0c0040d000c5070503c6444920b82c042507500302418a84120742c020b107503007800780d040715142e411440d1001130704118410082c64000c0200741681006440c210998045541c113500001d400143c000002441c0075529003d10440f4415880c0c110030009004030340c11500c004240280921401044a140c1c016403040042c00d02183c94001c0551200480d100d0760460302c041280801c00b4043c001f00e48950710082c820000341c008a55040c03160207089801401c200500420349440c0c0000461400c461080c000c00c07000d01ca10002c0c3c00c00c03d0340e02c0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 48408799 1250 48407549 48407561
    0x305100b090c09060f0708070203010f0506010e030d0e060a0c0b09070f1211130917040f060509060409360b06100e01081314030409110705030405040b040b13 69
    0x81e1051441c00301241041402c9022600c84a000601c0c00c2e10f001c0b990604401140c00c40e90742034690000901c40000561001e000310ba004c40c5000d84001001c0c50b200001402d001c246582560107640b01c00c488419051b004001e001210f002260780b242c59009800c800c0f43d074010054801000c0001003814081803180c0090b080098514a01c0c01800040e259684602020703c410070160401c0b03810041c0d10103500300b1824880e00307507007142000301d90b9181075228041d522001900c49040003a00140800c06520903002040160074986000da01e850407810000301203000d1401614012581d54011446440b40200d01d004404262056840c0d42d010348806101502d03070403c802e4458408030710014200c4c6c9810644082d070060580c9036508501c1c06003004603440e4100030504d01c10381c01c2049480012a844004050840006c43c00865545050803010700039142020038a401c801814011440007450110030b031800d03200c0664000850118404c001400341c10014006030308180f0a005208860000e50404 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 48410049 1250 48408799 48408821
    0x403080615040308190905120c06090109091a0f030c09010302060310031a0601090f0305151f092a090312090b0a020c0315060d020d260301151403040b060307030510 72
    0x450783c225611800e000744080410924501ea030802c800b1000c1358172b07210000c2c002d0014189030403000c66403501050760441d07541d001822941700f49500c8049881c41e1800c0042e4000303e040e070181c08015011004128207003010b00000344200c5001c80005c40303116607405002c000310740202060a41507250b6864848501c010b0300d0090028981d200c0210310003200c412080101c941c13010040c0705048060301d0303d5424a0000e80f040e8130403900a008502d0307031202910360b0805856140f500152184501034800140f00485000d06c50059200c0a0452070390b401c81c01030300450b60000010222001e03001002c0300c24003c0740d089407040642c0490791003031499001802940c0780000380d0442d582d0201030200400070300d80440380c1c2648032000000d80300040c204030003200c11113032042d0280400919a01d0070280444840c0c4c800c4444000d021004001c7e880c100501280d010071503042070024810448a0034a2901c0000e00191020900c240410030035201001400020b40d040b02c2501c0e903661034818500094881c0d0050 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 48411299 1250 48410049 48410057
    0x2c030a0209130b01120b0106050a142b0b01092303060112060c02010506090a020901050c03070305071b0302060d0903020c03070306050a0c08010521100e01050402041103040308061504030819 83
    0x810340c590030312000850305d41c10125100f01c0b43e20b00b980849030f03544008010401c0150a00b59150358100c284082c0103e04174108200b5803c0c0441e070300c12400c1c101f01c4105200014127041d649500361341c00c8446a410b9034801082060b8101d480d440e160f0b080c0c4610940c640c0c140c8990701c000500700301984100794446200e10342c24484880c24000032400d0311703000d440312a80b148041c0081510103109900510104a041c1000c504011407100c026055030806031041d804150b0001d5280c04204010361181034a081e000039507242a41507030007080c21030150000b01805140c0c0c41c0031481c249802049034028203100181100c001540f28078110001d00001c1d40c2d8400c0c4242820a081d610602480d07105044c0c40c5c01030126205050005404107000c1030101c00e1910f14010f0039404040d8240e18001c01c0369800c010000070505e41000e105000031140c00c1100721207041c7d010b20034000001e601003100c2d50000c40494006408050112160b0514801c6620081480c000001c100101c0403103402403005110440d11 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 48412549 1250 48411299 48411301
    0x3070f0c0b07180305030309031902070609091109060703111e0327030307050a0b010e070503061201060b0c0714030303010803070303110405040c0507122c030a0209130b 74
    0x1005550010308a0380080c05001c0c120300144070749120b92462074400d500070210003030041d074030b071101c1c0c3c04c40d031003035600065a4000040c00e1500c1b074000f25102466000a10007000c600d440c1c044010415550741c0500b08085481d1f52403204410b02c030900703481d4845401400c0959034812440d01410314040c100031042d45019901c025036081124100381400c0451a4000e0361901e003841b440064514030750380889400240300c01d00c031880d07070320208050600c0c623200307070024004600541004211010140e00992a0311022402c0040340355011041e242c001d2002d8503505801940100110b01620403500028501d48020511003501080000c0610031203441100940c03155501e0f50070300d07840748024040d18103c4d034420800040001d1080c0e00c081d0079405d4204440741480e4407540094156900100450000f94000c541c0e40148000554004203401e040e080c07404a0070b914071501c45114040d0340003100180a07140014165403800c2c040310540310f1b8010038003079051034040400940880c1400007940d0a0001074 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 48413799 1250 48412549 48412577
    0xc01050a05090c010e010311130e0703060e072708160e0609010303200115060306030311010c020706051c020705010507020f06131e020d0605190204050604060c0812010b0307 76
    0x204083d28002c4041c0d44405840e0302c030400540103010080a001f845141c20406c07e03861a82290b02d020203004000e500c031701d02c0d04220303800500313450251f000740c1ca081c040c9a00f449503594002c800304ac210b10585400807140d64071001e0048420055520040d114007841c40d0320b04000300303a8081901650f04000310343c01540c880b541444107500c0e09000080c0030038140c60540200c4100a80d0a000c440909000415140440030307e55020038840e82c03182c000300351918802d1081541143c1c1160200c51258003c0000c0f102250000f90f0316000c0c0d00c501e8080c07010008020080340d41d4904030030307c2000c004006555904651910318004c050071901c1200600031007107203880d01c80002c00e00702d020b001060340c3c8a0034800c0503122071518000c0015003a500c6841030002c4401078a643c60784800d064000e41000441e480e00040345541015040119006203104100901080d40c1d8202924107840300d03860a60b01162031031a21300303014452030356842044100400002140c0d0174000040d8894052a910172004020007 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 48415049 1250 48413799 48413803
    0x80601030f06051306090609030e120d0809010b030a050307060e0d0507060510031b030606060e0904080307030605030312040c050108010b121909030e0a080a170a020c04020c01050a0509 81
    0x3804000c0041032049a000003180c0740e6000035401c480303503031854440041030381d42d26003c031880850201d550b15281c5009000341a000559030b242c00d02b0507a4408050440b4504041e21481c0810441c1c0511040201040001200354070842c6001d2014007100e1151105042c0180c0e20340005c4800c461141c10505042104800861042850041031b10340f5030801c0c0c62070b502c15018002c000d010700c00502181500102003100d03015071034441003003144a55606815424074000780d4050f6004203007445010354001c2096120702c00c0f501d600542180310a6125103618008a000d00a80e511180d41840007003000250041c1e00200c05000f50b10036039400113456518001980c402c00248151840081c042c002c0302c02c4156040303c8107030b200b0401100c00e40030b0565000c00f00d0444c0c001000c01d400246c2040504805820141c9801002d000c1000080440746040c0d034442c0030310300c4403460400180b10301041c01302ea028002c10036030341c007040c009109540300d4054080241c020042103550755600ca0401022403100200 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 48416299 1250 48415049 48415051
    0x90310060b03010306020706020f070638010c020312031e01050118031b050603100f080109020901061412010e1504140c07020f040603080715020c0616021507050d060806 74
    0x4441c0c009400c60b883c42d16443d009421142084d2602034080100000041f00306004092452050000040010a111002c0b0030300082000810002c414048a01c22a007000103400b00901005d10308228a090a8030110341803405041c902c02103600080144408218800c51443c0245c0720310040303034980d0b07030f036840110340040a0040e4a50840281350062021a002d030003415615001c0d8400c0400300c954407804645d6030741c4206c8400c6e20040700c2680521056a9210703040c4001c4c080a0300074480c1109036000522900010b100346024001c8010401c0025084201520030150403105c410003150307528024034600e1801154880708000211400049629040c400d040320385400b284000c000c1c0d9202d0a4051540e1b104507026a80121030721030746042d43e0b40345d01602c001745119a6040b40c550400703140540b106161150401e00d11070045c0910043c2d0000000d416601c60b0303c0013a07d0700c41d00d0000c0c0050f41040103036910310548610210801903526080801800c46aa20301d6040000a40d036075162621584 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 48417549 1250 48416299 48416309
    0x3060506100c030804080c030c060a02040501020f031312021f03090201080609330a08030405011803050a06050c07080310080f070602100c1e1701140918010204080a0809031006 77
    0x100d0340d02103170114401701c000e803050442e04400c60303291080d4001c1261a041045800300c0e20f054001030103000b1545c2c1845140c5510502d40019030400718000c80d001944560b50180680300310b280800c000c2503540e008580100c0c5644060843c280d5a2140401405031205d140241d0200e440d520205100d4180060443c3c4038800b00c140b665075802441e5814416509900000040c0408032011081c440e51117200e031b00001d00400340103554843c903100024209038008402d1a00300c40c015042040800c20110f0070b198140e0b84044001269a901441e10b483e90040d048084c14a840c08010030002c4160041c1c2003096555a00440f03001c1d020754489641d03030708030900440b001a08941402c03a04900150050f4010440506000728a582c03100b4420034110000b0340400005004031102c0400c01c1d2541d010355014040c61400c05119600010204907031700000362148000300511a480c00b43c1c48404e5058402400e5a03c043d14002886402e252040b50800000544607000300d0012404115507441020304442c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 48418799 1250 48417549 48417557
    0x90118050606030f04150e0304060504030b010503070506040303080c040e09010c021506030d0818031314040b0a0b0d24050405090c01020606130e120406021507020c0609030709020403060506100c03 86
    0x1e642c503561b45041d000d204502c003074226240c0201e003450070802d002901c003408403661500d8071a07203142442c88507032006034005c90180c2c0003940244030300c0d11514101c80c00d494050500108503240d0942d00300e4207124a510640c2c0c140a43c07c14068044c00641254007a0b04440d401c8640010420000340784891003612015450b1340461000b980715402050302c41e51241c505284003d4503011028a40d095a0140c840303035440700b0740144107001c2c0317542040c608000c0071810303201000450b94a0000ca1100e548500501d4008003020910b500400342540004010035a40e0f5031802e405059595429084030481c010581324a0030310700061030f810b40010704a512039a050b801030400351620401d00c07040301703042a5081416a1101c0d030450034068100560301c10f01849450055441d85007420007810300c0014400560000114018440429400101266030200c200c90035a134a040e084c0001c0e15082c02980030244040c0042000400c3c40040c2d84824440c0c41c055580415489480c402111094400a1300038049 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 48420049 1250 48418799 48418801
    0x30308090c061912051302100507030507060e03090d05010b030709090f0209040201020a0501060e070f171501050706152912100306090b0103050f030405030a110d02090118050606030f 80
    0xa2029410482c00f08441410050454030b0004100c0056641c201c6000b200e11012203001e0046090111082d01c1c14a170a2418905043c3c40e0b41d0014011720600d10041d0090f84c8400611203556000d00c00c071901518020004845801c10b441d2480c083c0c465604407511034001c0110025000c986800340c000c00c01c1d8000c0502c5901c088550800c0303100c0301301030b10690441c4921030640b030000300e00f441694007502c4219900340341407815080041c504000c500440041010b106400300f9511140400300c0d420101a04c1c06110100d07040340100d50794042d1a102038629400c050b001b943d4a020040d441c0103640705643d404101e04654a0000c81e17080d49000c000385c40c0c01e0100003071000088601500391300082040c9038690303040d80d00d0300c1d850701b6039400c1c5900380d883d00344e00c4004100b002810480340d000c980ca11809141485c1c42d20b00001d4550062500c061302c41400342d00c52000d155185c204502c11075a000340741030460b5840740105004003a4460088040f28a480003094481c60007200380e910641801c2010300103 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 48421299 1250 48420049 48420067
    0x10c020607050309060304060506030d0c030c0209061203070605010519050d0b0402040b0406030b180106150c020307090c020a05010b0d0c05040b1f0c0c050406060503060603100b03070504030308090c06 88
    0x1007039000c5039042d1403501041c0810041c642d1000003c50146025610105643c1000c1302014240001c0c5200c01c1d0921100b6403a41c1c00094110900a54044e0100e03100220381d5a0240440d04141e108442c8880b98000020000c1c00c1298580c01941030340d4081e194004000740603c80300460340c03031900800d94003644941519001480041c0a168020b20261010404400f010b01060a40382c25400c121001d8107404200448005e921089040d00b401d060300174800c0074a030001d591001c070303129180b0004200c40d1514020954400b00803160003440d01e820f0803c8010504c00f4002d403103200c040000ca4455082c5502405680303007049104a40c0741e040b88543c01c0c114544420080181440510242c0082080c2440030100c503807090012040c000580380d2214000582c5450301c10034142e60006072099103440001c2c03100e6030380a01582e81c07004054441c1d540d079132a641030054013000ca591200b40d004d40300004000c000b40c0d001000e0000c40348641c4800303000d0380390b10f00740589490b812458117401c070b2820320051706 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 48422549 1250 48421299 48421309
    0x5030c0a020c04090c032906010c03020c0909070303080106081608040501180b06011103030103150e030408070b0d062103050f0f0301030b25080406051b0a0c05060114010c02 76
    0x8040c0c03580121958003882c1c80214090362039511068555021070003040040c42405034074040c0040c90301401000d052010520700d0041e00001c0e1205040110b0818142c0070503000f0410415540c0e0001c01c5108249031070407001c1d50ba2611400110000307841440005050f50207080200c5c064015000c08202044c00390300129010080184262501e42d281d00101104100d030001d44542c0c6400703140000c2841c45c0000016010b8100c15000d01016481000104046000f800380985030844007400454503d5001004071300d18040c0d500551020b01131081c1c005098500c03000202681c1c0e40300d24080c0001981c4107820358010004000340107010000780801d60000348680010040c0c200c0c142041400c0440c81c1c1e18901d01601309030000c945480c500d005110f10f000c1449100386007403021555041c488a1142001006407001a000500031510b540100f00141c0b04101682d4410f8540f8a4590302d910000000521004e2a00f00035a01c0d070003000c1c00801c03070803d0086c2050b0010310686515040450f07a6007400 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 48423799 1250 48422549 48422557
    0x21303210228480320030d0201020405180402010e1002010f0c02010617010606050a0503100302040c0302070c0911071b05040204030c1d07081315020c1b0303040605030c 74
    0x100c02c0d00040055000240d00010a010006010400006082d0700383d00c03501c5490612007030654003040604615030700c101e0186407003040c0c80d0f200c291340038070810802e2040c0e8400b005100841c1d15000d000d1aa0400590560140088900c1281c56400c034507924070a035140c404003990064001915a0008001400c041c2c1c00038800e00700714400082d40c815000d20074800c84080c40700190051351600d10400044244c141e4600f40760300020001c000e03c070300c0c2480c003604501c10380b035604061082c04000182710b183c43c0500040210b0300034006100002250381b0080095000080451b204040501e002c1205003c0c0d1240c80c502c16a40680c0360701e40402030311004030311210408100c1261040ca20046255116400031340019403061100080c258280042d00424060305802d103107507034415008002c0019400708940343c001054941000c100c1c402130030000c44c060303815200340e0a028000130303600c401c0040000703180c600340c4000303280210038005903030805031031340704602ca03003000142c0900108141c02c140030300030 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 48425049 1250 48423799 48423853
    0x7080f03070e040c030c02061f0e0a060b070803071b0c0b160f0b07080f07081b0d0c05130b0c060705220305100f0209010c0b0a0f0213032102 62
    0x2e42180410300001c0c0c1502c0107801600000798580c4100b00e0300c0d80c5c04000880c0c2112030413070400700c24601100c0e40c0046800900c100c4119400c000040780c40c007031681e071004002e018441d00044e0b8401c01070074404125403058810340c00090f152510b4100480590843d801d41c42c0e4010075001c4030741c0c50000c501006d038019282020314010350491034400550090300d4800014071a01a01800e450b1040001c0c140003001040348400801c4e890400540d2a402549164065004480b00c140d81c04840b03005403142c02038110000341c1500c0e056402101d642c0003405440314080342c038004002e49450700d400344c031280103200d4038880e42d41c1b002020407c09401000079040c150840d0700301401d0510507100160401000345d00503503850b004184030316184062802024540d481c01e1801b946031109420008056660404002d8940348400c0080b51107800c0e0760708041c12107001e0708015500d0781308c101181c801c42c80c21840103c5007030021400703030080d0031040341690744103d449030081e110b0b0500c40080840803c0000e23a00f = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 48426299 1250 48425049 48425057
    0x90307180e0102031003050c0904050616050f1206130b0105090f03011b0807090501080402010c02010c03050c12040e01050d0f080703020703020904050a0615181505031e0106060507080f0307 83
    0x440d201804003403024510030b81702440c04000541c614101035052484070707240603009003600c00820011a100145054021550130400300c1c0f4500c00d0a0121000d0040b41c0c00752a03103181c001040650031500412035801500111a11004c0800040d03100d01116035001a96010a00600c10740170640b90405828402c140060b0020828070003101619441e010b0002c001e002060550051201c0258051410030182c40282400ca005040c0354001074010485150001c1c100503000003580300b0188240140c0d0080e4101e0402c94040c01d0490170b00d5940384e0024043c81b5031500d0024000203540c541283d02141060704800f204119a2443d1200300340340d0b00000c010b0f02544268030300000142c644000d0544218061400350a00c030031603180907420340da5803054445186050400604c01c041c15a1908400c1000000c40061307801904c1e040c0c04013032051540056894010024007141d440202d205060446508500070080d403510354034251420f0152403405840604180b007084002d810900085070400100d0034 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 48427549 1250 48426299 48426311
    0x61a0705071505070c050319060221070f12050c07021003021608090f040b010f0e0d08070501060602060c0a3501091d06061807090312020705010e010509030718 70
    0x5094005402c668160ba001800000d52030b0240860110104003a1500f03c02402c0c000403414804041c4610440c4050305c550ba00281244100c5160f5414205c0d99202110724065071034200d03400340c42c0c046d01082242c045a500d0b031140103c1c8200b48907451144910300492414400507400b071081410320802c501040c16030800400800002008543d19a0380c03141e00840d60303524a10043c00310701300d10a00324500490070058001c00c02c1c1e802c4490918207841516104c0349030b1041ea030008890245840b005810340000241ca0414810103420201c00e90b1065001c0740c1507621004504221031041d42d56185c0090245645240803000820000324661007000c50b204014400a0009203203500a03809030f090241d8403203c0400089100c150040c101a840d4007400ac1c9180810106d4078668010342200c1c0d0800e018800070340018010080d50b80519084071104040281072000070b903030b48030355001d0b40340407809021040d01550303c250211102c1c0000540540340141c903100000c05000113010340b02c940076072691 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 48428799 1250 48427549 48427559
    0xf02030f030916060e0a0603020f091e01020706090f0608270f061509040209130b0a020a080606090607150b0303071109010603020313081602090403020109020112061a070507 76
    0xe40950b0040ca90740380640072070314041c3c0d1400d11582c043d070320803c02d00046155115842d50748100c000100c4884d800c001d41c0d2405080d80c59003a0340f00f86410349500010014a400c2505103403000521800c04c00e1702101c02a6444140035102d007003607403150400e02c45007840180000e500c1100b83c190000154401e1200c0c0010140e031130441c503503500d094084560b0000b9600d441440301044034a8210155200e140f0041c00b40a0102c0d90a00d4000c2019002d200100081001503006002503101141c01103001c0c441c0381040a290406540f14072a0400056911000305503035180200440d1a0a007000741a58980915681c420240c58081c06c0003031905661009c8840081d00d0610043c00264400c01e40c03100341c2541c032800c0210f881d1044c1c200c0810180305004011040c0c5d00103820100080d000300203580c6071510110300044815022000941128801c4180070425805400c00492180300b40c81c0c29400c2051030f002c0c40101d80c454030402c00f11100b812092401071802c50002d2040300d00500c20740e00015161 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 48430049 1250 48428799 48428827
    0x2d230106080601030c08010515071106040605041814040605060f090112060509070501020d140d150905061504051002070504050903091302090303090402091201050405010204060311190f0203 83
    0x3603112002045011081080a6a140c03040700390000c1103041941300303541401c020034403040c41000000e1403c2d100140074824003c1006807110002e2006054954840d01c4000052003508148034180034118601e840742c40e040054058501840600b00c861165540c4984030300c005407101070080c44e0445c0c1404a483d1807519a00d0031280038059240c4209003000492506000b15a001410381c403c903044400103100ca80c1e03000c20120300c015400e1510158840c3c0d0a000c1c09545e110720840310304451b151001c03400580004102c0740741101c400040806c240d5580c8401d010912180c09a114002c10301080180700c90b1500c00e60328682c01c1d1681c8101c4140d1500d0b8400306003180c400703542550099202082c903005528010204040e088003008040d414801c40e00c021954034060014a20700c0340e900841d00301c4090b100ca10050144004c03000091007541803504115000b58024091000081c1c244201045442205000c40315440704c2c500340d014020788011000c558102841301900c0450000b004029000710030 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 48431299 1250 48430049 48430051
    0x5060d020901080f2808130b160210020a0c03062c0a110d0f0303051506070b0f1503150a0b0303120613060602030a080405010e0d050306042d23 63
    0xc210081c04c5101c2480030151030040e00441c103c07501c503040f882e00020740848100c0604040d80c4500402d0301c80c039040c103c200244920750401448070b00041194480604443c110701170181c000c0d038010165010118080b80c440b0121354018040c030300c080000300006060f135030010f0b10241c410401c00803100205820075140d0049240c0d400003d521200d80d481c1806140d10400494010458441c010b40c107860382c640e04800107814000d801d15599400240d004500729460422500005024594500301391a00100c04241074400104074484040025a40c90f40102d03d420000310080080c0001100080c41708620741d402414040055258040074106485c2003001d00205011104009582e250180602c100c0d9044404032550840c200b10701000102d401004944c42a4003d26182c0d4859445080075400350010b21005000c91040c8000054000c0d8028084c500507041240d05200c544001c0e2540000009428840c05001002d08a01040c10340c0c4c84d4009500400d500303c0c003140000009140101c5600 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 48432549 1250 48431299 48431309
    0x171602010b1302070209070807140d0912110c040b060906070c03080f0403030318020f010c020f1509120304053304030c0302030105060d110609130f020a020d0305040308070305060d020901 82
    0x3c2c020a000c400c600e00205542e503c0b002a01d40030b4003628003040000c1c98481c0940100d00000e400282a44440f00d003034100b440c404e03030445510b011400c0b0b15600249400d001036403c48160003440d464042500d00341c090002c0100303006200380d080001180030443c0d5580600c000b103454561482c0000002468540601101015020415100d40c510b04014060b9207607036401465502c44140c8020040c0e58400b421180204207207004140c40e0b40500c08542da14403a016203651203030660803d03d2400540324010326000100380c40d0120842d4400d81880d076280500d0103030320342c03080d0b01c03031030005500218150401d441112103000203030f462038580d42400c1e2940700b50005d8a1104840d102802507080902800d90410b4042c0d0302c4100d051200e8445005842060724120311500000a00914540d9401000034003d02035080800c1210b192290780340007507100e0781c0d000d80980a014609041d1502030b00c50544182e416803207000e515598008100c000740030040440d64400703c0320940c0c1c80503840d104462800b0702 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 48433799 1250 48432549 48432551
    0x2071a0a050106084201020d0207030c0e13020d0605100b03061f0513140f0d020f060912190b090312010b090a08010c0801090f0606020705040b01020f15070f171602010b13 75
    0x20002400c0500b840c40c8c640965101000c10000140f50040d00380403144201050740980d1600400d5080b42c0103035040295026060300050f01c03c0c45202e6201c4e43c090200d1586014a043d03071150050400d0000f04c90140d400440d58800c48a02e004200310703044000240e140c06031030b000c5848a8030111303814a400403207850700c480c08401020305050f524512200340449056600718017507400070f008c0c52807100e1028010b0102207281e00d03550311650f60304200100880300380e51040c4c4286441c00b215041d0b0b1002030f07441e076407401d002c201d0b50f1601004440001c801d41100c0544d40c0e0802140042c981d0204020341d8000b19044e2001414900070300c1042c540b00c08541d261541545041c0110050b0b854640004401d207280c041b041208980011b041130031039000b9140413030907002c09001071742003010101a1400500031001c0d0a64034000c8017017144c0c421042034980c0c0b0044000403004a40898948044038400116040070036240a2001c050300061200c0b071001082c014403840224504903403c1d10915221 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 48435049 1250 48433799 48433921
    0xa0b040e0109050f13170d09060f0c030203040507030b04050709021b010c02030f090103050c07050106320f0603040c03061107060b0409050604020904050a050102071a0a05010608 78
    0x10b044079014041d000080041000d1003070030282c1d154a400a40c4080080402c507201c12034058008600c0199141c000660070301f000f101d1443c1c00d0802c00b82c907802010880c030030b240c0418120f600380039200f9240165008401880564159a01d050400e440030300241d80300d2240701e0300014440207a00007132801d50f80b1a08100788410b4505001801d64031001c006000795001840702018000710702c019142007000034a00450755446804c0e0a9403180705069020b0f0079542409004545c01080e80c0f0b4102c030002c40c0c000d4204403400c110440c5110700f4178580803a980882301e00300c001e01714a8098051a0441d00504031458110340d80c0c0d940030101c8171012800d0300816070104003013041c00328074400c4072181942030b14140420001541c5072912104c0052000327200f03140a00103d814050100581d000c00b546c001c000315650f20705400c000c14200c116511090200707000e035000924404050081d2030403104640c51782c00a03a00d8261005a0003004260f00c0c40c04185e01c2040b10074000040861f1031000d55000c1000240 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 48436299 1250 48435049 48435059
    0x10020414090103080319060503010603060b10050c0d0f0302090a0905060a300503071a060a080c0d0206030a150b0901020f062505090d0b06040509010c05070b060a0b040e01 75
    0x1a199400614030400d070301c03801000850015021203900c030202c1e20300c0c0d00c0c4008180424000504042d00f06903015807034070001104114056104640300380303003201c0e65094003100481c11190740c03007042c0700c08203a500700c00c01542100340102583d69454401781405070400101401150f10b0424907404000301c41c0d20340e824041e4a0610155020150000d40e03003000d0f030340003484040d0768409142402e0500700d04541c845801030007010300a03505c6242c0d0108a11625603d0004e003c0d41290303064890500c201c0d500600021300d07020014800600d4500a410407502c140141c0070003800c2d4200621040b103c030740300c0720f1080b5072554a00010001d030510000303240e01c0d00c0c030003400207180c420b850400e01c8255215400303000d42c281076400c2d131040010001005600508922408542c54040c0300c051981081249c2c141608014402440d24410381090720f04004036070780e2006060070b8809080e141e02c00304030304000e0000410458000903a000c80c0140c0101922552180e01964a80c880c3d480b02000c80092001406 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 48437549 1250 48436299 48436319
    0x30b04121407051c02070312050d0f0903020a020f0103060801060b07121130040608040510021c05040f1707060509010b010807050703020f06091b04230703020903100204 74
    0x300303096414000702d00700800350351004d50764601c10a070320020b60149070314064594420015040a150300004084240c90b1003000540170f50015501e0807040340c1403d044001c0c14405c1c0c80b5600e040ca40580c01007407581d60365000c0c0400712140c2094a410143c81c1c4001241c0d480d400d000303860042016100f001c0c0d580a40b030400c0c02020b11041442420059280181400e8080010f00742001c02040152240c000c81b82d940e80042d070070262104449298400305002407910740200d40d00d44114040c6040d03e58905911641104a02c24244141020205044001840f03801c6600080d8814401c0740c0b454801003641d1500c580e075209003045140c03e52000245c0c001080b005001e4980c02c050381c240288a010114000030b0400140203055108101d00440c3d4902454030030013005400c50440010b03a007050800314846520307405090304d82c1c41301d0204a090141141058400c0d031090b141c0a5811002c10510040d62004040000d00300a080580034010014956014840d0003040d201d040c0c00143e48903d800b640ca4 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 48438799 1250 48437549 48437567
    0x406140f0d0b040b0924010e09060907060c080408060901050103031101051e06030109060c020c01031d06040201030b030f0102030c030105090105040b0306150301110408100b12190c030b0412 83
    0x1a0041600c048078000103071405050b160450b510402c0003090350348100c82185032450f41100203428107080603103150f0402d585020241601e0a00f030705002d060f65420b410f1a600e0301c05850004155012020400c08948a80c2d100d441d000e00c50419540340071f540302031040c0380950a441012199540b9001002003542001840007a005200000d000d685454069010390681404e940c8000031608000200e4a540c00e50081004540c000c008110b407070407091009561341052105203000c289442c4208001403010701d82051000198030080500c0d90b900e07801140030b0203413070302429050310900b40d08640e03440081c0065407155a05101442c0c0741c3d85800304100c10300d141a44804e005510340400e8500548011400c01d0b4860034905060703440b1514000440c0c010080c02001810108010802081c1341001144d00d481c0c02c1e284660907c40320b50343e40100a00c0008844050f40c4903400707007998081c0502c0c162101c0d00034600481601a10560f6516100f040e0042117070200c8030645011241d03003089030080110 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 48440049 1250 48438799 48438829
    0xd0c0801061404090f090b0f04110a08070302060c0f03030a02090102100501120f0c08030a08100801050702190318090b01080f101802040923061917010b040614 70
    0x4900c40311080c40502d511840c007481d0309640d00c0303401d500c200c11600d402080c2900c0e030229103402c0b0303403030001000e1140c61400d0390f0440b408188911400700b5880d00945000640d4902c0001c2c000f420314550800c4150b50001c440e2851600a900790a200081c003400591300c1001d94180241c0d8400780c3c58002801e00307515803103030080d044c545001444001c40f6400d15511301940400b042501600702c2c1425080d0159641c0320007007900c0700007200820b450784403041c40e004501c8440c02c3d4030301079103910940d400d0b56001c03a102e6005074042000c41701e00c0c228183c0d0842c2d056000741070450910b0500c4c01d400301030154070742200c001d0a0700c551040704596441b4081c03903071203a2103000c0c280450401541040050302184100000a0b0850450240d030b140168112070080007803800030040d0341309001032810f000c505000c100f441c2d50908000103100d402c0041c46c03102d20212002d40f041c0d03860304000c007820120300e0800c0c10000700e66031040640d040b61503902c2400042c3c850301c0900000f982d9050300704101d4400c20a00 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 48441299 1250 48440049 48440057
    0xe06060708030c0a030b03010c0203091e09070c0c09061d15010e190803030f040c060c030f030203130b01081b01020106150503071701032001051903110f0d0c080106 72
    0x844008610000e0680f60041000803089541d1840b00c201240038040d1103409a030306518104001c0e042c942c0000090004180c01d9034408000d903030340106002d03503802c1810055042509180002c1605205040c1019110b119070702d107894041e2251002d004071403654200c0e01003903a02450107a544294642229230010020010034090f428920000b04200c0d0b5000700e01e80070704c550f044071080c3c43c1030926081d03002d4400c02007100c4c1c4900d4540048440360710282c0702600c002045140210f600c920a502c62300255800d512070520b00350108008400940c001400100d001c84080c2c0c00e00c0005081000303141c001e042c01801049203149035488207900300042d200c01c5065a141000401c1800c820341d61b551545455400c04903101c0d56000300a403201e03103001580101224044002004110039020381f030000d540b071f140301c186a88071000019030341d91142c1a074206d02c9075950156214950b100360494140d21152201003418449112001d050341d4220040742c0c101d0544918000f800142d1104c0c09034018601441c4c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 48442549 1250 48441299 48441307
    0xd03021b0303070c1101020a05030f0301050117010f060804060603081209061f0e100e010f09050a0204120f0203070b0c0f01050c040f06080702190f051509030d050613060f0e0606 78
    0x50041c02c1c813400404002d03d1200402c440d40513981c0280b1039025801e0b004010740b0380d6400c1c0315000c07040a83c400d000709030206040b81125a0317165a03174019241a524400b500d02002820910300b9030300c0541c01481240c1c030070f0325940d0102c00030342c1507006003641142c0d90320200f03840d0500700d020301d050201c020711840e540d2280e40404000104601d10200450311414002ca41c6510340510b030759000d8407150040c00112004d03030300005616a025403804102c0e034649104010948403018024242c0c415841400c1d81c20409000c0c64002c50710b00103540a200744001c040b00c401c26602c0c10a00c3c543d40144402d45c107a07400c1007070007802d0031800780104c1e41d00c58400e40da034a161505000580d80038000300e0091004000b109000181c00394020080b0780c8007421402c1603a61051221702d00032845103580c21048403180103000d006503c0c00319030441c2500503120304c005541071424000300e10340286401400c00d68081514060449150602c1c490100a0400c022150400500740420103030a0180500a0b07405404108 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 48443799 1250 48442549 48442561
    0xc080d0e040b0102071a0702030d0203070b101202010315080607050403050106090603080703080a0902090c07060b030105101202010c230601080604020f010305070210050a0b0102122104020a080d03021b0303 90
    0x10170840e003510000303c0b140510070207180214005000d0480000c0d014880c0035138400450750004090003c2c14800d0b924140b6603a01c1c5046031403003800c503108030140c00601c20b0b5104019802500300802c01c000d03090a8000d02d03552400c82d82d1406005881280119030002014400d200080c01140302414070400c09101c240d1944e506d07500309100c3c64002404000c00384020805101c4282c21148000340c00178281e035590f0070045c50400e003030740c4540c90494200d850b10703010f0b0440d802c06000e4a80709810f45049080c11901d801c82603001e034000a04100c0c1003007000143c1600040288500c0020881c042c0850310214094003511482c00f0010781024043e075103e0002c0200590322252440c040d02c000b882c02140e940c603142c0d0140d180100d410130084002e414441046050070003a8031024006000b60701315100c48581a400d0141c511405001d40c40c80399004e83c0c0c15030320004544070941c10605c09041000e4460791540d00c42e080141c004015800260005894010581a04051002d1500100280d4a142082 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 48445049 1250 48443799 48443803
    0x30123060703050906071205030a0501060305100e09070503070b09040606021612021c0b07140a1202090d02100302130e06240904021809010602030a020d0e030102070c080d0e040b0102 80
    0x41c40014104207001500d40d0b1203499110603920016030140c1c1054007400c074214042c0082e0001c84041007403900d84800002d0f00c82c80780c0140e90142c03900540c0e0a609a007452040605102c000300540d105100c0d011001629071010400a0000d002c62143d01e81c940260101b040300b520600d074014030865000012102c04182041200001c94564004d2441d0906c8c0710f00c0880e102001d40b2401800b0104082c10440900c042850300e01d1094019a844000404581c5200d1001e130241d180380500007035442c222002843c030703254010600e1100052600d04100c0090380014810740d082c0729400000b07034002c41c6280064502143c10300280c6001914622035141802c04610380302d040091102c2c4900b80104000c1c100c2034004125000b100700540300359507907420040003800c038010000380e4900901003880005002d80c400300542d218400b655026010f4825201d00480d4500b801810013070b85035508020600000c0c6003071607084000d00030500600b150341003001018003680d20100c007103030185051042e41007840e0784c0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 48446299 1250 48445049 48445057
    0x200706060b04180c0e09040605060907050301061713121808070b0906090103090206040906050a0902070b18070f06120b01030c080a021e04030c1701061a0f0c0105010b03012306 77
    0x41c450b0000d8440e910107003c44451917600c2e0184d070486048000d21003440625084907103e403109883c82100c58840c50700854807403100344282e10025400c095045003001c54644001e8102c0d0281d0000c12101d201616102d50b80401000800082681e640d00f864052594010201c0103042900180a13542c3c0b4010b114070861142c0102c1c18801c800019820384c507680242e000b2a003298010742000e1f116901c8000c0000280343c24020941300d000350740000508002c41d1b0080304c6400f0303808018000c60351580411110444440e03081e108150142b075070041401600c5844000040200740c0e40e000058120341c44440480d01070f907010342d04043c00c0405415070741d60001d640c1604030501c00740060351103000001402900707042c1c09032010580030000d00082440409521301040d50601040c0080c1c11001e580403c2c200c94440c0729040915500400e00d41460341c00c0c1014003480c040b6181030030318000d841c41180b400c45800360008015a40c02000510510a0b158401c506030712040200d8000c0c545000001141805 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 48447549 1250 48446299 48446339
    0xe12010e06060409061d100f050408160309210c0b030702060103030e0307081002030108070e01150503070c050f0f0f070803190203070c030606060305250c030201200706060b04 77
    0xb8a90940c201040629400306264075802c15584d1b1005c10040c1801d600c59200b030096000907810b14401305201d50881c8111030040f0f501c840030b54a8440040225140c2c000d5051003541401000440001d01c071040042d1101c0d891400402000110024509444a00300e1070304401203420081c4100b000040e000a54203044d0390701030038904003281d5074000083c90201c00380c12000c207501400c00d000d50002e85640186040c1e0740aa4252076100b502c504040640d00000d1207044121189108140d00725402030004542100440c549030318241819210140b03070030080b1034140f0003680484454412031000f8070002480c0f03c83c601c00b03454203034a03040c41d0558034018a0040c2400844480000c3d120900800803101a45e52000ba0000078540e6410240001d011601c640c0303003c01c0c1801d0015908510f00c8400e1340c0c022030700710307001320f01034040000441308034100c001c0132400c3d59695021510b00b641080352403d56102903008040e9070300d54502e48042516410b9118040c003030004c0c0424412081003507041c5240b48 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 48448799 1250 48447549 48447551
    0x31502120a020c0106151d21010204140f03070603150306091104062103030b0307050306040b07080702030702010c030503360c1206062e030207020f0108040c12060b060a0e12010e060604 81
    0x12245100144440c1c2d8a00300c029009058441c8e842010207040d000390003280c05110010016106035001d000c000c0942c0203120340c1c0350b0003008050111500a80c81195220035000501490340d48a50741e80013101c074000d60940b4418101a6149410300d450301032500070308a501c42160308052500d0140002800c040001814161140002d01c0c0a4070100448801084d004088920500b000d0900c1c0425000a442400c000b030000000102c00c13a00010803911071541c1030755030300c16802d81c50710110b669801c003070300310080010805c1e911034600c07a0000654488004096103c002035240607040c1c3d26001080c440f4034040c04c040c0070203115a20020400640c025400d880600c40404aa040c04a0040410f06011100780e0501304600ba01d550603406401140d20a176041000301c0d1403040155a80f400440c0d00914800a0740010301951100717200c2c58012031320511021030f120200f03000048081e000352084c80000303840c8907081c0d6101c0c9000360034070302c40b03a2214008001c0f003100300c0c00d00307900c80100038aa40c0c01a = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 48450049 1250 48448799 48448847
    0x150b100e040906020c030f0408060711030f0a050c07090e0c0a050904080901050c01090c030b09010516031e020d090c050904080a0309140607020703021005090604031502120a020c010615 81
    0x3c40341640448945043e41402d07607641d4508803004d407113590080e0080d02200d21030341d00003503591400f032600c1d05030b411074503c000c50902c00d041084400550080800b002041800c2c442d4850380f141c20080d00014016250010412142c0c4641745442c0207007410805200c3d003800d10013042980c4881c0346c06608143c124441554a402d8140142e81c540308608421800358a17103e4441d00f845110a80101540c3c131803200c80b1119103c25885a003603440580d54015000c01e03040b0003c4103140030354081c030004009601081c000007900181d1000701d800460404c1b5019031542d0310b070410810048202c00207080c007210340904909007a11034841d680a514105410304d582c81d600030083c00140b04051201440480440d80c0ea4a84078030b0003501c0302c540e803004a0182d82c02c1c0386034205281c011815206090005401981081c3c6191508141841c01c0321328a04101e90800c58031464030300c501101d03840342a4510002d44e407000038a00075401c40380182d04c201c6e0b007001d0807042c00208a0f8040310b1f807141810090350300181 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 48451299 1250 48450049 48450053
    0x10c02011a060a180f031101050a05090d0c0504110310050d05100c0513080a060b0102010506030a110a150c050d05090901050105071104050108011508120412060b0904150b100e0409 79
    0x4052400084804a603130080e000050328000d001c125400d40388224010342c203144402c5c0c0155294000e010420300440ea003481607601504204502516860041034804002980c2d032012a0403103079128441e29104d1400004c0206103d40d070783c1c59200130304c07003076170080d64012641e10360a88400140c1030240c2007544480c1001c090500c140191044d01c40100185031006649410f11566942400d41c1122010300700b0300d01c030240350300611a15105240c058003508400089950b40359203026a460140d9011074a1040402c80003c881d00302e07200c245454856034940545030810301c1c0351442c592011020440100f015403255202c000c01181120800e00307006132610001e00d400d0741e030380d520b442241c0e400900d41310000807044815003146100b42403a108004055072034600d060b44510003941007421200c1e0400003008103616849229203030700d0103400300150786840000001c00710441541c068070038440100752400a81d29a00c01c02403140d40807242c1807152551a40d000c5c140403a00404584600c0c1d03181c0c11982 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 48452549 1250 48451299 48451307
    0x203040b030c071a07081308040501030221010801050103020307080d050d020903030c0a050309041802030a0b19090b0613020909010b0c0a0506011d06031b09070c08030702010509010c02011a060a 85
    0x35240703601071080c0030784d40d82d00d40d00340003a01d004036250000962030002282c44001c01d03040b40b400654201800ea80791904041c01503010358040c2c4272450900c018060343c00b8030301c0950001940600080d4001103010b504d980101840c10354150422855500220006825560003030100c90700051040005030b140c0701880000303402c5014000d030070711150151245650070018084010007464104480401c08c0c91b04a885540030701341d00001c000c1d0182d00000c1a100411151710401c0d5210114520007051103110b21089029034cd02900110f4440d1070350000e018032454500e40da1828142204070450030714118100098156006108404c5075120000b001d98202c90180200c1c00d40702c2d0808215500340d40e6520000142c40c9021000e1082d007101d03c400f04500346000b203040c51003001080300001c400b00d040b070100701c03028401a10003020300c0801d84130000011044800b85114074401e400001d158900038400301e0959034252800011645445400456400400e0380040c402c0d101780e039420303250214858159 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 48453799 1250 48452549 48452557
    0x30507080c0c09010605090d020402091f03091a04031d060d02131a070b070e18070806010e09100306050c1612021005070801030809010e13060801051003030203040b030c 74
    0x5046104000340d01c1d54052800118640100019a00b01c0c440f81e07070310301c0100c44601440c00c1071907102062403002c5001d480c064002d00444d030700017050306d003800c086040c038200d00b401084030203400b0039140c240181c1480440700c03040c13030124211a0360f0480c81c0b40985d002020f8108e859140400003805100780345c4541c85100c10b0359030400c94081c0443da60101c0c03103032800c80c100441c424221f81c480c038082d00b400200e01d0041610030103079012110400c55111280203448031a000d1a0594115103422181505015480c00190240410340c0b5805114101000018840401080401c4c007586500041c4041c0150041410b41242e07044100010030381ca85800b091070310f1250100d100b82030b5009242c0041401450103a283c1c580e2429001ca46031a14900e0750b410071b880e000c03120704001c501010010004214040c0c014aa4a00140f50000c0382c240e2940002c0c00a40f0308400d001665035441c50280a210070034400c40303420000c8c13410303e04038840c41d6030340c0255a40f03c1d030b002c2c00ca4048401f00120f01031590542c151 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 48455049 1250 48453799 48453803
    0x30f030c02060d0b1c05030405101202071101031409030f0c030c01090819080f0a09020301090c0f081605030a032003070b0a050109090507030305030c041a07021008090a0f030507 78
    0x102d030383c403800c5040510181699aa400e031040c16a4580f03d5166400c03010742d200600e5000c0c016508140c50308041042c074090030070a402c1404038081220300481e459100402c0400e100740d0107003524800410004049a40700d2a22845008d00c482c280258150000191400c1080160b940ca9551176050800c034118091801c50700215800d0080d00820094030700060250002c401d40c1e42d02c0c20308183d8000b15842101a030310007030341c0b84442d004500c1d5402560011781401c0c0c00503001245864443d0760741c0d010b900050384542e901405400040c01002001d00c624600e1450300300710084031038180800039441da000b24500405015459423443c80c545c41e803048104d51b8201d80e80541703450301c6460814100070361044400004640c54000081191101e82c03003416010358004000707016090075030b41d0a441e00c0d84007501003100c201d001c0c8070004144210b40d01e03c40016030044c9007251110382138414040507419150080c1c0500140200304507400c000090300c40c0c40c150f0030005107408880c69041c01e840e540b10f46640 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 48456299 1250 48455049 48455059
    0xa140f040512010518030a08010b21090f07050f090a2c06100f0803030a0c1b050a0c05010305061309030302040b0c060603060f07051c110c061006031401030f030c02 72
    0x14605080c503065000f81c0c0324402d2221310301d05c5001d400610548903c282e04c0020042460140144802100340020308820130388030240c00d48914140340025112182141e0f031620705da01021004079040000c0c001c010081000b510f10700c5888504100140e0b070008014507c10000703545445100d0724031031003510112180c4440c1e075250040079200401c039850381c0c4126118800b6042c001700000f0409000002c000483c0c00d03040185042da03c84502c10400750111405032000c0045804034035240365000010090018450401130044050b01c0c0750040d0346a40e180d1005050501d01804c00c01c06855007084503003802129400085e0740d0381a0b00d402e40080c05103400610030590301040c0300303c0404000600c18000c410407411101c86035203450507406810411a00035002507030a1003401450101c078540488400da1a01001c181c26442290b030081942200c1e850950300c4c0d10036810710030840d460b00e081d5405004c0b54a81400441451102d0340d0000300184401059504980450350a040c82021305110503940100 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 48457549 1250 48456299 48456319
    0x402040f030f0c140604090902010228150510170708150103230d0e040e0a03021c08090c0112140f070e0f0906040b01120c03021902030a140f0405 64
    0x100b07252941142d0200301e4541c2c1943c900440c401140020621301c03402d00821040c5042d042004100c0517005400c0124194490448040d00d40e50901101301c05440c01603401c02401d1295061441d0b40d220000a118540e81c680f1040c420103820015000c030aa80880042d0b15216a42485440c900720442d80005800c4c020240680190b0b01000b4086040340d001e80700c1c1c44c0215041c91140703001d0b68114000071806900a8190a40d80da0180c18420b500c2a4000d000040c1c1c0b132407801030300c1e0400b981c40d5412030058010070100d0b800081d003646490f50000300d80c83e1401e40e501e880880c00350346692240f0068103104100d408a055010550000d441d440310182c80408031313051014529140080a440c503202090b00103400480c9400d00351400f0310909402014112980c5650041c00300a0098500b17990402c0700a030f100098a0115004204101410b541c0040e52124040401807007140c45d2206c0e401150020000e82c01d0440c1d100950a1240004150b8140c0e64800c04102da0490b1245500550704102855 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 48458799 1250 48457549 48457553
    0x60901120515040b01050a0207030b060a0b04091b09080303010519080a0507061409010507060c02010902180403030513021315170703050d0806030a0b04050a02210f0102130509060402040f03 83
    0x2d8040e9041c100180c030280310301c032010f600545260007034210210059010a0f41000800c03111401a600300f031001d005600f01540b10100c0c01125401904000450780c3c4810512580551440c010900f95056280c032800d2181400301c25178130ba10061041078812514004602c0c0c19080e440c0c41070004101c600200d600c4840300b482d181d0b840340390300d10a400109901c1142541c120071680b04640d079015051307481c645054150347d2050020003044440348119907807211800300580b1845451188452200c0c1e111005140c1444e00406480000b0b0a10701070200300c040c1e060068840c032042d402c04650107000882d140001e01034901819106600442005036541d8035200f0703040005c00c468044e6401842a240300d0140d05006555003002074800640540c0007044d004080b50400c1422038009200b0420341c0d900b11002e400181141c0e6a6025440715089881030b400850700080009100c1013041d8002035003010450114408140414824140202045400140310360364a5040f28090a10010380441e115124 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 48460049 1250 48458799 48458821
    0x203100f120b0106020102040f2309010303050d0e0c060706050405150a020403030809030408070e1b03010e090c090402010f0e03070b04060302090a0603090f0f030e0306071e1b020609011205 83
    0x2050180e400d10b4401e0000b160751441030080301c080e81c13003075000109400e14001070300c5618601c0b03501c540c0d2101c0c00183e08640c2503503107040e01402103000b980e8494030340161010140844010f1407008145601034112560546c071a24140c0d0111034100740c001580d9610b0f400e0146c1840304c00c004022081c0107010401c000d18038550701034010749020741d4480c03415948206103141e80784101d00944040e0780c0500401c000400350b81c030801e5440107002e880d24843e840344c201001a90703002a0003c4018216400c108041b043c0204020b40504804480c101902d003026000a0300440c4865061030030003040044004194408104e07420040c0711640c2226905e07903644400600030b400c40341c43c0c3c920600900f00b00140d12031290040c043c566403c0080b044e402401a55002040030034070a04078240194034000705150380d000c0c071610b072042589403038504817212240800000082042c11980c2401030000364580ba811820820b65080d039410f07542c0c10f540e03050480050b211126059601d071019410304081101a18003 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 48461299 1250 48460049 48460079
    0x31b02030a0305032a040b0a090801020316030e150c090f1e010f0c030816090801140403020105010b18040c030b030607030b010e1e0405060f030106060201050609060402120a0203100f 80
    0x2014000b5204c80000441085c0c1000300302040d880d20039000e100170f100c1d055241c4020f201508180c06c1821200d580c1d00200390030380c3c100b101d074411400240d88606480a4060244040100300a00a040c0400c0e180540c43d1081c0d8001d000c424041c480410700c54419110140130522010004094005070744200c24482c15003208440054001800b0b0072100c030100c2e0040e81700140d0a641612912229510500c4100d08a155041003100300305004e0b500155504080c4a6125040d0007624010384501c2d10b818040d007941c10607803103c04460b60070401019840000d08920f581c00c00c007140e01182c3d00c4902401280501000701000740e02d03000c1e450501c44859010341c032040d4491001c0e22191001500c04d41041200114400c0100103c0301b00340b62001d181c64954821a4030200041c900b21131484c8550219003145c2d403503000b400141c2e54443c1804040e103020042958040c1c0304440940c944556144078102c80b034000f42034890b1141e00400403680348000c50b180700f00134090000d0141c071031a69036040307a800590 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 48462549 1250 48461299 48461311
    0xd05090106080a030c0f0203010902060301060309050717100b2701140f0603010509070c080c030a080a0209030a08030703020706020708040e0708010e0c09041b0305040302150601020a031b02030a030503 88
    0x31a1000009218001003800d0103400e400d62904582d100d00c83d21040e8070585641405c030b80c155072b6440d40900503a20803020798081d148071f0750001a6000185000c929000355500068051505076582e0b0a8142c40003620071101c0c150f042021456204c803030086504090501c01002d058000220408111454100058103c2e410380c000c141c20003d91106004a05183c405140d8110008200500860805c04021504005035292401108070a5140c14405400c498800f5125400008154408a5008040070f4020903030b14811807818520800083d0340f404a01401022000c02000003041c207806503060b40c403101e400ca030f01559038903414a0403441c40d0303016005a0303090011180c04039002e14803c1c01c0c443d06a403002d01058207275840b2081e410b00c1540110f1107551340203440c1c0b0124900802030001c6501603503104e441c0072450381007919000e402c004c006160740c044641d0140070000c00d603a002541d19a45509404c114103e030400e00d0040904400929000e501840707410040420150705c280107502c910 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 48463799 1250 48462549 48462551
    0x60406090b0c0909040b0702032701090806010e01030b06030304080f0606010318052e0905010e06090d02030906090a0815040209060d02060f0d0207050a050a02100509011b030e0301020d050901 84
    0xc0c2e0b0b80c001030034190181c107802d15001200301d030008000070350b00c4403019080081e80c0112030600300b034004881400c40ca0b4406001241c6150032140c2c206580210030701000d4100c1c0c1d07016154643c10490508010b2034140f00141171802c80a0100d01c0c1518144200c034003802900301510800e044001d00941c0d80d0605a0702c2600080c501520341401c208000d240407580c6a104d0b0140450b408107500c41c0d8110020380d201030410400d994000d240100c49885030341601803055002080240382c41006c0ea0404c03074010301c01e2025810000880c4c51003a0b02100311120041c1c02c0ba10240c442440b5008a03000c000c984e0081505445054ac60211034003494108030702c2144200c680643c541c0d16882488514922403400a400100510000380ba00c0745130f4024016840b01d4010040c00d14a80da01d4080c40c0075030300f400a45543c3c02024030401541070851000521240500740309280809200001300007465502c6020200e1289000100c10540b280c0951100c41070020002e5440f42c480b540400c00611050341c201d2030039 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 48465049 1250 48463799 48463801
    0x503150103031707020c0904030905120606030f01050c0a0804050a0204020f130b0f0f0304080c07060809100b0a06050304020a0305010204060e0a080c0d0f080408030a0e040506010207080c041d060406090b 89
    0x2901d68030384811310982c4198060326240e103000042c8080034401a00403030501c101707040041240c0e1603011900154180d410b000b0300c1c050500c1410f0506050325045c0840050341070204010600001c0000c941c12440d0615082c0c2066640d030408609146c000440254401d00000d40340b1502c500c05405011617840001002d00d01598803590b1003418400c002c0c2c1c074059a2400e03c0180004486113014503442030140080a281ca081c1c040424200f1900b0303080b003400310340d01509000d03103050100b0502c281d1031000f90040200b1004100000c01030501d0b4403800040100c000001021034446501500085a01c84001d544441c1c4814001d848003444130762050142040c510001029400081c50350010354000d409a0007801454660f01d00e03425503120140c031009406c210001c0c0200c8100001d04c2503800d00c4e80c80c00924010001000140c400203044681154002e100501c02c02c040825503440d2801f0031600011003c0860044500500500d248480bc0380255020042401003a4000b03404480c4107100c4140c01d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 48466299 1250 48465049 48465077
    0x3010b010807081602010f0243080c010920010e090c040515040f0602060105011106100b130306050411010809030a05030703020f07080711090a02090f0d0c050315010303 74
    0x41c40c0d108640d014006006500420450a031510340c0180d5940b4038400403c185461120001c143e030701c080c2c5410400d050014242276250317030a244078884400344049080c0c40461054901c401001e110102400204000a4029003414250300030380c11035910036820a02c00b02c0304050b0506101144102c14080b460700d80025a0030300c1d103c1203a07445403e558180505050030407041c0b0072111451403900009520070000071600c10082c0000100034aa260300408403981803000050524020000143c1f132540031805114604445903100f001b80c07000e005025444007503da100e110503115a6001800d82c03803810003403106100e01c1d02040303241d115086e210324503280ca600078132607541d200700001c20001503030a00100d80580d10a40081c41c0b0300340200041e44c280107550315806402c1d4410082100c62007941c0081e48078600b4074a41c4154400d900a00441c01d02c41160b000c546118030110125124114800210080001c03004038000900405001c64540c800c80900000301c2c1c0c6d100380400e0340401c0040e00e180503 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 48467549 1250 48466299 48466307
    0x90703060506010c05070e06060f0c07050310060b0a0c03050904060305060103061d070303180f080a02130e0d03051b070f1b0506040513060801390509100504031703010503010b01 78
    0x10413658800000d041c0b40c0c0c0342888600f41c1d05c0000e01200d503c12410044a007120b4042d002130119041d0310b9015041035454501010300d40711510031003c44441c00c024003007129101e0201a680304824504280402c400c991a003290184210324113640d001d032426601000744000025140d05130781c4540020002a40d000c01c402c0b25403d042c90300750b400e81c0d0014509000180c0f20f04040054a48202c0010258545504201007006540d80091406a00c01d0a45c5800e6250a070308641c07400d50358110810441c40a41c0c0d0581c3c031510b1a68100c0141519140401e48004d0b003c5040002d01600f041416140d44680c5000e10020411240503038440d85600301d04004030a400140108844000b03101e540b41920b0b100900c01146400360310350310240da0310840040c2d000000e018030f461030300d041001000b880d4032110010380a10002d030444d00c1c180e81400316000c0b1240d040b1302110041c0341c0840741c401c1c00110070030046070544215000106480076060300d41402410050145042c4c1300304038000d1245030317183c8004403 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 48468799 1250 48467549 48467567
    0xc090b04050f010c031205180c01210c050702030105090303040c0b041d0c07020d0302030a0207060e0a03080c070f0303031b02060403020c041a1503010303080f150103020a031409070306050601 84
    0x15804024024110b9140d8000c01d2019900b502c0b9080c41300010081182c21011503074111640c60005100c01480030040c601801f8401c0145000d0030448401614021001613458054030446141682c51024485444c0030344207803001769600500070b100501e00a1829526500705a4046582c10700c00341c8085005405ca20a65040d00d254050401d500401d0314a0740c500301501410391140d1170000c00c18000981c170f8005001001c1c50298006507a50040c2010082c517000565020301d04120504000c103549030360341a907100480390066980da448640c0d00d0622420000f090f4080000780021650020805030550003d5000312081880011014041c500603601c4600449004005800408a400c0949010b070b0000044034000124aa880031640c07010801c0220941c0401130b0004012004004243e80140060390000d000710400600c3c0c20102030400c122441c4403107480c141500400e084405501c245c0c400b06908d000401c00c1c400600b08003062584a1259000540f01a810580001d001e540030b21112 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 48470049 1250 48468799 48468809
    0x6080601110a0f03090306050708010503060a02040303170a021b0607031103091e070801021b010f090807060207150504110a050405010f290307050307080112021318020a090c090b04 79
    0x291800c0e808a5541e9040d10780d24100131424016841ea01002041a41c442d641c4110041d40381c2c1c11865043c10308161905070000e00340350074280100001d000080d8080c3c1c000d0310302c880e11165100c1c07940340d000d0885c01074026004141114101c10350700c5d9006080000744180503884940b410404034182d40455030891104035916042030780401c0c1024044240d140c3d4005150070b106e025030f440b4640300c0720f50710b003079074001100408003032100c61440031810022311031240740030b565403070820030500e450759900500d006214010348440d901048031800d000d460254084140c0107510200624130b4586401c101c0b801584003541d02418441f070300400c8a05003480b441d4165407951080501c0246440700c0984006544e5450300c0c01c0440350080e2a1070412804c025502808180e11666107030310b01070b94000e01c01c000584c840542c0c40014140a400350310fa000e41d41074410400d85011929040310b01084400394602d91009411070403810000445079000e510426440119a071982540d03560b030b1018440c540940c2c050 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 48471299 1250 48470049 48470053
    0x301051608070c030e0126090307030e0603010312110a050613050105150a0b0a0201060308160209070203180108040f0f0c1409060a09020310090207080a09081902011b17040608060111 80
    0x1070351750541c002d04d21a0f11514071020303a85038801d41006000708200c4155561201c60b8408a81d9a04060708602d949070f8040c1c05132441810366246031103c00d0b41810130900c2c00207000c980042000004010b100300100690043c0850700242040302c6494540d00c1040c90030b407807a5291001007420b003442591010320b9030000625102e05103042c200320031800c2d8041c800110030b41d940d80000200040c02800640b664100e07500840c901c4030703c140144100c0b032400401d01d00c11904200042a0014550b02c82030f40e25401c03c0c031f40042d20396103502e04140140e0740c000c030140031504070106460420200d04080c00c1610401c0c3d022000410901c0240b140c003400aa492a0307100c0322844040c002c6c8011503000d1a0b0284c059100140f1b66903490160004a0f480210140d510000020f5405c100e960042c0110000b4102c0900900300050350708803a05815a0000b4020704005100700121038030b1158040c0c13011920f030400100e80c450010010382d030f0040e40c480c2c413400e004942001c000918540c040c03000c20004050f6000 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 48472549 1250 48471299 48471317
    0x501030c050c0d1b051209040b03031318020c010e010e0d090b04230d030302040302010306050a0b09040e030903161401021f050a180b040303050f0610080606090301051608070c03 78
    0x141584c11800e58a512000d0303601c0f04401c50301043c42040504c24564520400d0740d80e0300d00310024031045d81c41c04140c46000fa0f00411010502c03030056440001160b880c0728860030070041040c01d43e0003034841c1c4d0f44688455800c2200c1c0740150041948683c1d00142144110780c04204c28100541d4070720502d01c030300c42d0b000c003090008000c440b507a16424809400c5070103404d201041024001402c103044c003101600002c0c0d0100d000e0003113503058401ca03c013a2004a030000038075880e0a00c1043d451240300415400380e0348401601005090070426a00c11b44401410740700f03001005a23003134a0588491043c0004081020341440e980c0d400442d02e181d031855842d491005000d46a28080040c000c0a4508a00b05a41e040c01540300c8815070302e1035040f030381700b0a803096107401d241c10001c059603800f03028499004620001d02c561a40d0300d101e09020303e1510b0030aa140d50740d5480000d075803802040c4030306405509290030428100c0c00001d070310401d413499481d68025501c605208940100301ca2030300070003080b512a = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 48473799 1250 48472549 48472573
    0x70308060901090c0e060c0a17030f010801060e13050703020616020a0b070206031f050919050f0c04050d0204060f0902130e040807020409020f0a030506160216061b0b040c0501030c050c 81
    0x4001440a02407080440d08030301c5032580c0b6030800c94450078110502d600040280a84007640114081c010374545009200e605e062400082c0254000791600a02c4607400601c10304020381071020030029030b0000e10a584804052004564403508081c2c200d00c078212a040100e104aa0181650346407a00504120b0031559800b0f0b9140030310000800d8a00b01115000002855660b44030300140704a00d64116880d403140c0e1300c2603a00507203c000d00441007007503051040019104a0800791003c9540032503401d034500340b80d400460007c0a0710b400110245004100114100c0303515001400070b4144121290003c5903151160000304009940042c5507840400680000d450a90040c001850000305100c607804089000260240300d02d42c02181d041e000f0108001080d9003402c0039413010907150020744548081180342703007000115402110700b404840b04100c548100b600001141440d4003000b00304d0242841d0500c41500e00681c0f003900e00107800c0c90101e00102e4810700568001401600092104180304 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 48475049 1250 48473799 48473809
    0x60c060c070503070b010306020d0b0405070215071709011d0d08010306230403020601080111120a11160b150a080307030c031b0308010311040603080d0203060402040b070308060901090c0e 82
    0x4524250784900c0305000400200e048105d40368020b41c80340d01c0043c1d072071400b12008001d84111102051145207003000b049210381d008520360410066030b810310308140d9941001580d03079005140911091110340710822610300c2d1305510203010071018110796200140e26010480d9210590050303079000801c1d000041000a4898001c1402c0801080503510703161900b20700c00552640444055005070700c2103004110400e401c0c4500c0e84c002c4403084880345821a2039100c510010005422401800d590303008000d001d80090b4243d031f050342000b0811a41490181c10b24049000040d00d814403980c1c405500b94501d4503107900150210b403c03132805035007007400c035803410358a850b054103054003032080e02c0040d000030b11512800811114404e85803501c5c0c039411418818207494210070218084e51400038140080387c0c03410140d54214903001005079691740c070000440e01900a662000281e6140450035508040d0045c000300c1c4a460300780d4480740103a07a9028a14113480d409803417580030a0303445250680c64105 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 48476299 1250 48475049 48475057
    0x1f2c0109120804050402210106030606020307020108100f0b280c11010309080408030403030305010e060105161e1a0702120a030c0309020a060c02130b01140a260601030b060c060c 78
    0x1448110b820f081c0d840340401c0c06c0c0c0e8000f1294000b4803005080301280704d0030903002103000d0b02140c43c4c200085402c1ca04080c1d664490703030801034140401040020000540808140c0c09400c000d100409220b030b40d24007001d92604000d0400401814035000c0c0d101c40c120034075108920a1351650303148009038481d11850500d2641243d05410136403a02c4100300450035500040c8000d2203a04002c0d660b4514605008044510681110041c0c0842c0818800c0742da07071060603140003403600c03040240c401e005072521458140c3c944208814800c0840303406400e0250b01d0210301c800003c807510a04d139942d500403080b030700c81c410003040c038070262000c0c00b155442c2d80c46548a1501001c960500107480485500011482c15096020320009001d0301095011800d00000b0303482c2104e00c010017800710250f000c0010300303460010319041100e60030105203501d170b852003060034144030344016500c1c1e4400d1714103000983c0c0007401121182d02003800e0410525107030504804450144880002418058440c0285204180c0c4 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 48477549 1250 48476299 48476303
    0x901090e0c0a0f1802040f140102030d0c020a1e0203071e0503010212010906050111060c090607020d060507020d05070503160302160b070303051003030e0904021f2c010912 75
    0x4264100070351540c5501803110054a000d00031520410316081c0d28602a0301c2a95600000c02e00500c42040851984d005d0300e020341d2641c10508501c6a03501c0d00403840d500600c40d00b54006802c0550300e411301d907004110740741c509002d126402100103211701c01e045c402503180c40094041d808000304005502a8603070000c90410180c505403040c03680d80340001c0c20b9810180c1d05000c0c00b4000130041100c00414030a40008160a09000b00700c101d4020019480c0c1200a04400581d074001404600d00d5440900f21a03207568000c0502c40e132140c1500300b0000904017100c9038030140c400c41d007940058a010310240c5840a41c000020352402d10103010311904170591690803800e61044610309510000c820603000003801409642c140c442c0303094140107050f174102a160052240d02d00005101090b4440b00b407015412042c0c6040031036807550701c04070340040140d0904401e40101544841038640d40300020401503000d22000803904046c1840e0014141c1c1500c08440c00311b202d02c80d003000303081c040304201040700e4 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 48478799 1250 48477549 48477553
    0xc030807020f0a0b0f070e0a090c0215041506051507030c05030f120a1a100503070e060a0207050f0406050108041401020c01111902010504030206061507020406090b031b0901090e 78
    0x80c0c007002e01501e403980c8107038111506010a002c10000380325002d44a540f061103071804c0c0c091415040081817440215024070180207480709120090b06000304244010801300705443c041920301030400c5d0100b0018000b040a00b98149600011185815580c0000b84040d00c6107c0e03281419581d000d80304124919003c40d07250100340f01115500454102416403c4200c1c030300707804c5c940790240c000c2084544401c10300708903440c000180f0342680c4405120811090580c10160707980c0d111000241e9640740c8400b00340d51300c541c1c0000c40d86070881d8041120b42c200d5030191480301c60802101c0401003a12901c1c026180000ca4000008012401c3d1540215500c441d44000600d40001e0207081429264081c0c0001419000004e003c0f04120404208090001d8248001c2080b0308080c0c0c2c0007502c0d41d10140c0058424111441c0107980c4414190403214002ea00a00800c0455541e6101501400c0c03d0042148a4007807e5110400c008140d07000101898004143c401c0c180c4c01d283e00030b8014814940000da8034 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 48480049 1250 48478799 48478813
    0x10509060d0608010c030b0a17060a0f02070203070602030a0e040608030a032d09020f010815060d020f1903150e0f041a0906091e0304050d02120a03030b1e010c03080702 74
    0xf1010a00c42c81c01d034031000303031340215905901c1da09025001c00710b503200440b010110b5034060030718840820300580000c5401400b182d104007031002d580c00782c06060030280d89409280e0000621039000001402c222409494000c41c3d4540d82c000c01c01160001c1c40380218a4200301300f0441c143d40f00364000c000c2803004e40403010710542c0c1041c100503c201c1520510144c0c583da03240c038906500c0c28282000c454102446c01c2c11140c5804d45e40322030200e482480540c014840400d1143e0f41440075011754008401c0a045562503003150200c0d504c0440e140908503002c00d1a0240c5425103003641c040b24001d9440304c004650300b43c1c8826031f00a102140003002961400140c04d049113034160b40c0e00e8100e010b50402d100070709442c14850000349c2002c01008076032060a0542d840d0108040010040d03808841c3d0480304071191810f14004500005414801d4070020700906000750100754255000b40c0c82c41400fa00d40202140c00306410420402e44011b0035408102500589000a48206421a400b0032107106a41003 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 48481299 1250 48480049 48480059
    0x160b0f0c03040e0420060306030307140c04090b01050a06020f0706050f07080d0212070206090c0613080f0703110103060612020315090c0a02060a09080a08040309050616150506010509060d06 83
    0x104aa040e0b07000c03210042603100b40040300d40300184940c200c00d02140c21b680386040902c00690399100d03070710000308940300e48a02820008004c0c403400c0071000d40a0018400168549444281d410090207451b1140021840c046456413000a01d00c45400050004084040c2003220030748854104401d12520b2440801c29000003605d400050107111018413005a115203440003080030743d140040c41b11045501440411039490400034810509010a0f264140c0e140c4113403c0042041016800c8140309110340c40c4130104503540060044204c9001c4c402440821a40c44d0044040d00e4030362084c5000179098aa0030101030f0b460b54004c640003105080c100c040070625101082e2030720b104551144202101003140000940c06110456001c078003074604225401481e80d0303540d686d000b105805820800e1075800541014055507203a170181c00000d046949824182c0b0000c01010f010400c1215842c85000f040b154104581c0505e90149005845a604003c907a00070b100441d0042c003036500c0120703120200050 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 48482549 1250 48481299 48481319
    0x9010e0c0403170a02061e01120201020c0303131503200318011a01031406060d091401090c05100f02100e01090f062a1202090a030510060602160b0f0c0304 68
    0x10701c034a031503c0d8441e102c4404060103424140010202c8001ca00848a2034200c140c45044d150305540303a40040140c00d45403400103c3c0342961f01e107080b580600c00065800c491508026100c0200c600145030180788100240080b010758841900112460000101041501540d40d02460307000020f85214003158120b02045800d4910592900000f2140581c030001c0c0d80d40d05010304c0d00c03540c1c440c40700108203040c00400b1560502c1401581180103580720000000c00001d00a06004220b00c4130003400507400c00d00341641c6a5000d481810301c02d10119035654682c42c02078490a1031400c5a80141000300b440c4090480601580c01d00c041c41c0d03550b10f00809002442c10a610340c0202d01030385000036100c841441441100b000d240c2802040080c85401d2180907a00c1003180c000d2041465015803903070b0716400461010101e94100034440c0c0203141850782d488000398032003400c640265084405110300b8420081d60300409000781662008100a40e804088014000701100a0700b44100c1c4e142541d00c0111030 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 48483799 1250 48482549 48482573
    0xa1b030e030a1208130206031b0405120303091501030b16020709020a110c0301061503020904021c050708010f1a0f04090507020a05010b030106240908010c020d080906010509010e0c0403 81
    0x907207804a41903c0b881070740e4007034480c0e84c3c400070081807002e0040e800d0300019a0b5002c010041303c1140000e18082e038280d481c2000303440003403070040d00210081c005e0b200c2c1c2584a03041196a41c60311720800d81481e00323442c00f80c1e101504030b035000042e001041c1c80c1e100780c0020300440510010154807801500190a5203644000d140c0c00040c0c2da10a4081031004c0c00d218140301c1d450f10a11b200e681045418400f00d20507000e03207013150840b4180142c0d18000071010801070f01600300e405801170038500110342034820b9078020a128140303d0381c544ca4142e172031b1800c80d4035120351030113051152040c4000482858112900408030403131500031682c14540c3e0303042d050003030b100100d860000603008540c0c1c074010414240544480c42000720000d0142a05000d052120002c0e01464416040744c91460a1038250240c08148003030401e400080c40030f0124a900a980e803622043d00c1400188044005410031101089160503036400400c6a441c50346800a0141c48641c00b0f020341b44598010080040000c804c18418 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 48485049 1250 48483799 48483803
    0x30b0a020a0201151202010905030109030f05070c080a060506040e0706090605130f030807290604020a03091a10052b0311030301091505010309240603020a09060503060c0a1b030e030a 80
    0x10410446100052850788c2590000703009a0424541100080d00b00c0d80003018a0070300d10306151901d01600700003100b44400d92050025006002c940e80074001c80e504403d2007501c0c00d80e0140131003601000c6488d0b8841c8148100c00020303c0c4210300f80507c5210b000100300002c8400008d40d801500d80c0c6155540c180c1c168002c44000e180017034468204a00040041440c084401090051040201030403a62040003802644240da0002d60310f00554041e1740103891064020202ca280c0300c0e0340d0010400103c00c20b4a843c1c11100d4684000182c6140c2036150076100607813140c4000401016658048064518840490a00c24000201441c20130100055070007054624030214021000040c000f420f43c0a42c3c11003030405042508520205a9001c0340422901070012001050340c80d1958403002801660170080d1b2062083c02c5c0025aa081500034405407102142651901e8442401142040c4940c3c01c0f40c1000c21a01d56808201c000c080d0080000c890085c00c00841107440303540005d08002c401482 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 48486299 1250 48485049 48485069
    0xf0b03030d06060f02030c06010510120e0a02030106050604060c0602130b18011d091602070f03060218040207020d0602070303020d021207030c0206070909110d0e03030403080f01030b0a020a020115 86
    0x3044041c0c0e224007840c0f100c1d01c4071700286103406414000390f80c89150501945000f11400401400064812512403548103042c1904000c00da08414015803600a0070038103174840c4d800d02001040324900360046904807600c1ba100e2083c42e803190b076941d43c040c0d04010400c10f0910b0640b100010610b030304c80e00a00e954010040400e2010a010002410034140001206000041144030b14810f803202c902498004a4210104041c200b0b0860f049261000d503800503204602e030f2076400005c03c40c45801400714101e044806a40804048062004034054840c0103584240540d41100202d0440c1d170041c0301d00b50007483c001d0326001952444105a901200c2e1203c00000004204040d0365494428071100018a1014204a01f040c00004200f01568061200b43cdd07130703441d458500210810b400721383d1500c12440090180d180400141c40e2070340c00882d03044c5c010a01102c00504d4020307141440b00d0589520000d04040c87d2292208070000b500103e507004150741da00c90304804508103100c19a0020056400 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 48487549 1250 48486299 48486311
    0x40f021002060a06090603020603040f210203070201090801050f19060f0e01080f06090c01050c07051507150504020d08090409020d0506010510080f04030309030909021309051503060601030f0b03030d 87
    0x3c0500031568103600c41001c5501d412405e00051b91400c08890b04590403a8060a0524003428604a00200c00d0800405459400b03c44044590044068200c81d03000740c950307030ba5640e84c505d07c16081c0d0320110f40103048940c0c40800030310302e40000180b012403004014400100282c68101c000020540d5821804901c00c441004200e0714008010b00d0800060050241205080400d84103a403240039102150500c10040b450300b201800401500004140060a40e0100101d50400301581d0b03011140903280401001e480158004041c0035242c0a50740c0601482903058590300e40d42e806030040289290b0054582440c1000b5940309031030340202c240550045c20040d4541410820b50f555000002401d05c40c0010822503481e0806c0e68442d0301580600b4046607110403440d081341d80c0600c0340c000721000780c03011520303100d90228080d1140658002400401464460170055404001d00d090980e5169000900042c1c80754407940080b0100c0b40300400119418444100003403d5400c008000d10006903204 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 48488799 1250 48487549 48487561
    0x106050304080d0c030f11070b010306050c090319050601050109080c010c0c0510031a031902060f040509040804081204081b04060801020406020f0c0a080601030308070e040e0124080d0305040f02100206 88
    0x41f2034081c02100c5a2010341c0380c443d0590314600c030140144005081680e44000140e1082800c0f002c0b00c0035000e0040036214075601160008800344030801e0143d5151140740004582c5500810384001a03601d540300524405030340b03600440d528800007100f243c00d0902c5c206c0015454444008001d181003444d180815001100440e0001642607403000910a501c00400c1d03130108070014080c0082c43d1b07010780320b480da2440a00155865849554001a00104440100018410140080e005840b440c000781c0c0e025041c0901d2a0700540035a0003807203202e40041c4800e01e0351100c05021a4803c0601800121389280d4400341c01d422608280c8c17280d000358101080300780742404280880984808110b904d0080341c0e0074411040d40d0707540705020003000e21103030401041030b40c0d009480417404014000d00520000001d2840d050291503001400c260259a03601003070f060310704d2040c05200ba540040c004020740005c0b4441113004e040060000c0e2040d0411400480268541e0480308140200325002000030307003000 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 48490049 1250 48488799 48488801
    0x12100507050301060e040b040608060c030a0b0306041a0703090c0b041d01060906050c1f0902010e01030c02190c0f0311010809030405010903030c1a010905011508040b0106050304080d0c030f 83
    0x280031000304181000148505600a2806059504195000644217289402007070092a05800040e420301c5108100700010282c2c100440c4945c400741710601480c80028141542c500c400d40f0300030300c0d481c041c03120f07607c0d0300e5540c1484a501080c07071310300803642d01c0f441c0d1030700c0064600640004500d45400241031141008039418280917824180d51104590325243c40146072101502901c0104140080c03810140f010820148411301c0300003000c2819001e20312070040080035080c0d4202e0201d07100001c002c0081d80284120990101c0e503401414000a001c0715491041c6682c0e402202d40c1c00403040c011680783c08207144e0b18061031146042412845a200000d40341840041c0600c52a510410061003180d1f445005581200c1d8141001c0312081824908107045030130b46050f4082c000c503603030000180ca86d441c0c0c200a0489001503d50000c41d1035081044844000c100d4003c1c0000003440300400803244103600565019000f4903a850404603001030980c241c0301d0302245200000d4680303c07180014556 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 48491299 1250 48490049 48490051
    0xf06040b0904020f09091f02040603050a15050906030a060e100e0703080d0507050706090b041e05120d090b10060e09090c040e0102090303041e080c0307030f0f02121005 74
    0x31103070103a061400d580000c40f440c8011401c035008540110200700308080400c800d20304420514044080341500c1c803078000081d0000d200d030000207810f04010076001d003614442d0f1020021140c400f54a61030410b0140104503d01600c541c2c0c00d4410707490280042040d911036828059441c3c800b404010355114211070554040781c0d80e104064001400400000c1d0400048940c0841e56030400309036580c1d0140709913113034041c1403005007030f044c10000c0d0b801c10440c14008580c4558440d203d02013801080d000e001c15040443d46004059500002c0c49024202190000e011000566034000c91018415907500d2000c9200f81c904100352211040f003805131f15000100d6600d116401e640075403480c64501441942c404030480541e00071a81c8804202d4200000e4040303584070007024080703990392541c0b2541b162900000c03200880d018400358074042080c000c04284091005001001800b040d82140c03035441016000c2c4101319110400d25000342c00503180c90602c40344218a00010305400986c0240d400b0540b00 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 48492549 1250 48491299 48491321
    0xb3006010b0a1b110d03051c0501051e2404150309030c0b060d0c0b0409150302030c220501060305010509070905150f0f03010803040501090602070e01140402120f0604 73
    0x4082c0b01d103050080d400f00300680090700c3c141c1600510002c50510300140f0007540b0650343c000030b0008444c0300b819002030084c000c1c1041c2082c040c503440e007400b1806003243c60a001d10b550240714814155156010285941520f0000520342d000910340755445502048a1110351200508042820018201d20459030013800203641001d20070400d0b5650000d04581c0f0300c2c040145003c5030b001c0811181d84801e0444c50301c0980c030511240410340c8072481c20249811900c5107142c1a401c2243d02c0c0440820040300d074003160340c00340080c150301040d0070030024100403841607038000c05100300900c1c4c0b4a90507030050500804031a10000761a5041000344466507000802e00420300001000c1005a6101e0b42c82aa4018000a541940742c0e0f4091160b05401c2c400c080103403c082c80040b0000c110003001000420403a00e00b6202c0c540003903600d100503600c5060b24800c4a4182015000412519509204514020000500c0145400d0202e6111032803040280c0705501c0c051903c3c2c0410406003400d2041c052010 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 48493799 1250 48492549 48492569
    0x3090a0201110a02010504030f060b040c030204080705010207030b07030e030729010b09090103140c0402030103060605010e03070608011404020c0a0501060501030506030102070f0f020402040503070b07030210020307020a060b300601 101
    0x5111381c00117801d0380f00301d20008006080c10740700c0c0d100317000050340100600c0e54010000c1c80f00b44844000100030350045e004603500c5009140000031f00f5800041d07402d04507580134107071507103603500d690040d0f00038400b1001c2c00882d400200680c00014000e01c01c1314001124220582a03045010040d107258840f058200c10780046042145104603034607041c0050440364040b51103440c0d118562980d41c240094041c856801600210011080100c1c540013082654000c0ea0703203041d800300c80c030704142c4d07180518131880c00891071142c01807007103100360001e800c40700101030030141c505072403090404d04c1c1c60703010b8078192956559058140815a8540105500850120025410b00559442d000d60100503403200400f24502d0810030000c6496070740568005000c0242030f25841c40d644d0000300026400650114014080e024076944100494804d132401031015500a00720541c03140d036581d00074810003d030f00340e0207030444d810f1005075503545802503448000b11f00e0380340303140004220080c034200060704206000 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 48495049 1250 48493799 48493813
    0x302071a1603020106050d06050103050c060304020d0308060f10020c010816050405130615020a030206240607020d060c0509030f1b060d0908071a0f01141201020d0203090a020111 78
    0x48011003040c0c1e015040c481d00c000407003085900d0140d006001e036610031500107956420030310a000b025800395040f20f0041d42900c3d00d8420000802a251000302d41c001e600c941c0002452020900c02d03900268803c1000d0f00d4045000070030000111800803004142005030301440c607010131540e01c444000c0d003000c604c42d01085108000100940f260040e400b4144c01011342004046403414030790409030042c000d0b40c2010b02d80d8100c1c004000d40702c00340305505a01520900c0042106c44501d041e0141c100c040d1201d03075051249512040019662100c1c2003664060a001c1c2d04c4800702e51070744100c2034203a40549034aa0350f0b0340403000381030405103640b40c2700665401c1115000f41c607a0111854440740c410454003241e807120750302c020740000c0402ea10003401c0c2c40c4011880380c041140400c1e0380c190001c2c2d01350040850750340d034501150089100b4000d80f144040c401300802128180a03290018400008001500384190710b0000b40c200e03081100c0782481c641c415407903101596000b6090501d840310050251880c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 48496299 1250 48495049 48495089
    0x7050903100f1416051312030302040f0e01030c060c020402120a0b0307050a0b0d051f06020102030a060506070c0b0a201011030f01060c0204140a060503281e140a030207 74
    0x3504c941084480248100018036040201703c10403420003800210340c50b44525005820020000e4100d40950611b10b00c03c03190110707900350081c680c541200c2e8000448400f01d030401404940c2031f074200d9800c903005902823150300303450b0368016403062054114810005104100c02d04141c549092036100e58007902c02c00d10103200780c0255004545080b41d080c500810305480e030b94011320788101c0c001c0451009008510002c6078882e41034009501400001c4030600c007264031303141005080d00c209040101030b442d881904001840c007a0001d0200300115081c001d44080305100c1403006c829808100c3c00e90794000c2341400d042e030303440c5100b01242d58041040b00360562424440702d2180340018010360b421301404403010b804668481d046100004107480f0008440c2c18500f074198081c000901800e48a4052a0701243c0461107114541904011004800c81d0303c800075200c24407104561089082400c1031440f0a401040c6400e041c8030b580110700c0010a207032881740c1002400c1074129040340d4280c01034013440c410 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 48497549 1250 48496299 48496321
    0x1804021903180b060405100f09050a0507090501440a050a02120114041b020102090a05030313030312060801050405030c0609150403050307030b1c150903080f07050903100f14 76
    0x41c1c132080c19140094141c40d445030f24000c0000a5002a021132030320790011803c0c1440340c0000f4000c5403000804c0c032964441090a6078519064013403d4001b50300641150240ba24a904c9d690820100c3c01040929024441104443c04000c0c11402d00f010440c0080c040610500e2103010340c40600e042d811030600400825402c0d180710306100322401e130030100441c03481594880d84220a00e00c2c0703802001401d51558100039020750440f4007000d101c3e48461070006498100481241c00406001c501c849207542513a8040c3c5000784180c0c01d05101342da480801054003a400d01c00c250040740588000c40e1a1003150303000a00c0c00c0802071480f010360f00946d01c0001450504034a0a0f003090381801c005490b0794903207008070b0040ca0311082c040c1d48441b050030326501520f0302c201c0c81c0c50340d540100031550301145000b44e54030a8441e041d00040009045100003000184164180750300060289865803402e204940020702d850303010781614100e0b50791081c00c003030314002620804060001214281c50549400d4003110 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 48498799 1250 48497549 48497551
    0xf2a0602150a0218130f1419050408190c08030a05270304060e01020c0a0303050405010f0504080303220501020a05091f0206060f01090803031f080a0c0b1804021903180b 74
    0x517001c0e01070b44010005007100380c0c1208001c0280c56100300040700d00c1d03210100c0d200006a400007002565440c0c1d8103e003000c0c2c0e010f15441550000c4090340b82041103040c00700081078803903c400401c0f0114944100252513140110701070904600b021440303003003000d4018290398001c18041d45024170301c05d40d2050710070003209a13411984941006c0029411a40061f41001100000300341c3c0540c0480c40401010380190142050750740a0380d901140301944502500c981c4907c1c0180b85243c0d100b400010190560b950450360101103a83c607000820071559100c034261f8102ca90729001260001c21100c6003810300300c000196a00740000f003412520000d00d006504c81001405441c05465211015551640261b800310000c0c036503081107c0d568a0024170003441e1700c1c0610076010a0040e907040c005002140018100703121908401100360503413400682d00201e40c09605006443d410b004061a1955518809031010b1600b4503490610100c1000d001000c13207010040ea50141c0d41e2410f0104045594100c0dc5 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 48500049 1250 48498799 48498847
    0x3130504050408070501050703060303080a060302030c130212010801060303030b18040609110307060201090204061406040612150602030903070501020d0e040510091503110303070f2a0602150a02 85
    0x100707074485060401c018407452001614543c00c01c0c080c4941140d1503440076040701d000c0e955420041d00c6082d02c00003910300c54400a0340c140d000c80f02c140150b05d04400012800255010010b04c3c040490101da40307542801d07071000343e044e50340311401c1041c0f6405001c1c010790300a04031010003441e80b003204085640c55010300701a0880c3d81e5031402508004280044000590000b0b00311441e507550340c1c0000303001e02003c140490017603091800014003c0d07400c18402da00060014000c1d4107241c10000c00316090030b00169420081c1e03442d02044521040428148806491290301a503981d5400000341072506250398045411135002d50824081c80350f01c80d0007106030640444020540340c4038502c0307512007001540c0000b00d00c00e18020512200d080c0040d0b090f41201d204a410a52801d0710404150f02c038000c110b40a4a5030070a2145403002496182c00d03003455054000022040c001320300005408440c06400c00c0300968080301d0715aa900066050030b0382d200e0502c00013940340c00140310004656400501c04 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 48501299 1250 48500049 48500051
    0x301110313030c06050108030417071203050d0f050c03040b180c0105090f0a06050310090b01020604060b0102010e0616030b031c0302071a040f030f0203131a04080303010f060e010203130504 83
    0x4541d042601c28021511071a80001052200d0358492030120780702c0c0d105205800580038080c00944e9400c034003040b400e080304ca02c0501e50a01c000b550b20180da40e03900c204002d0b212070344d07500c1d120100e1988034880c103030050354402a21138803460b10340350070381d00f08001800b410001300c00180c0c601d940030000512404450130070f1911640310720340d05001c90b542c02070200a0740e07448401e01d00040340d040d0b8440080c500c00d80e00d070100801015503482d0300000310b4151a00e0b00d4011307082040000c01040d01900160010401031000040504030200d00d0350410405a505801c01620346083d5040702d030740740c007a00441c45002c81c0640041c0050400c000017032486000702d1800d054020413014148400060a601c8144060012000615042c9044001000790b00811004a0510350300391903680c2c80002941c2c1c280c40310350403000d4035505010040032440c010b0702100000c4403040001042d0980300303102450081821602c80104030b81021006403900e001c800381c141c110b620521004031640000306080e81143c1c400d4030 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 48502549 1250 48501299 48501331
    0x150518060a18020d0e0307030318030203090f0a030b040f020a08010c05040e07030605030607030f0f0207200301060801090b06030106080303100b0c0c060f0a02010c032003061314070e03011103 84
    0x42c01034040d019040800d5441c082c1c546821a0021008008182c4281d03010041070f401910780c840c200310030071005001a4014010206181020461110b010038020060204a55603558410200104440844c0e40240303e10303500b011030038144080805480c4040c003d1241e10600340d8010320718040c80c032130760354605400c0000c40c1d085402540040040d00c07000e41640c006142c540c2c0c1c0940504443c031980c07080740e1318040c0c0449402a0380d10075528400d52141d1601c5552880c0c24413041070006204038150705542e520710010b0031050901c40c940c1010b110343c901030306a1821030101401c49102d40d2120045400400400803207200000051055909c1902d07035549502c07400c020a80385c54a810482c0d5000f080010b141045807800c80090400c0007020350090104021580c0124140c44040702c5401d51407a010b00e43d00040da88040103154480005070000d0440c0c9408105070050b00e40d141841d01d0b221400308140060a40d10400e000884007040d0000e0010345845804d40d0003a00c002071140714251002c0c0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 48503799 1250 48502549 48502589
    0x30303010530060108060f0901020a1b05010e1f0e0c03120307020c0604060c0506180c1e040f05010503120711011d03010903020708010606090b09091009150518060a 72
    0x10210128205108201e0f199503854007000c665034042658003101c04c84010000600724807050089034001140340d5501e802100c4c0f41002130000291030141120326549800d000907008030308016107814009040701441c10500219050b404039507210200b14215001340da98942c1c0fa4a00148001002280301c0800d5620303510403908a05080c330600c1300990285002400284a50f03001010300784072070050040c0c0c4d410b0785a0440000c209082c02140c12940d401c01180c8034511f00d000061900c02084202c1120b4840c940030740050101e0714188810b802c815524801804503003000c11031103e154004074611440d003c550340722008003652505416042200c1074892282d4414600420400135038050005d10090701145806900c0b04590b025000c810742ca4000009802403081074030501301c9603e003101ca440c100d451028010354600c000c0c01c9407104100103000051011840c4100d04130080c92500c103c070494105020441c401108c40c0e118001030303075010140000d0b40d4800030315a00303c5248856240b0206610 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 48505049 1250 48503799 48503869
    0x1c0807080c01020c010506040605090906010504020f09030a0c03030311120f04080c03030a050a0c0f090b0c03130e070806040219030b031e0703050c03010203100e040606050a030602180303030105 85
    0x801d801d1829400404c15040c2540150080350151108440600100e40c44200380302080104480c2d200d1103900410041090f0304050b0300824004072409011481c041900d004039190040301002228000c0d400801001071550621078140c4580c2c8511609142a1102c03200c0103101101030402c00488080038041020803022400315460000392805a0783c03689010401200140400c4400305500d0703007401602c0031107600c05d503004048440b482c1c5503000601d0820030321280da500b011100341c120303200c1002110281860241c110008118600c1101124a00350383c00030038510307026004034081c50041c80301c58009012014407000e640d00c149000075404802d900041e20301440d408030207107000c0f0100810000068042903d109490140b0b046072005024203080c1401c038481100c031030110310300c003500522602012200c001d41041c054540441c000c2e848600240032440e040d40221080c640c00100100224650321108890316400c40c059400c0d50316046c0801c42d010102e805100310742400d403440c0c9802c1410 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 48506299 1250 48505049 48505057
    0x90303040e0a020304050d0e010c080304021804051c0c030903030e03010908030c070201020f150f070c05070b2215030b13060303080702163510020d06051c080708 71
    0x884890400318180b040921000398000c0c0c44c240c405000354010504a18080c071105c80d490360041e0f4986100000030380724030211350000f800072a070003013080304c05490414095140324010790181018242c0004071030721043c224106a294482804100741c42500440d070440040f00032070f030301402c100803681c0e5010000381c011b00e001c40d00108050004014085111070000c05810002c0c0300fa02103413400025802c1e520303581c0303809001e15580b10f4100c40c001545c5044000101d900b140082c02e080003020703403c0d55540d040a032a50080f0b02882d0000c188022100e10000021024801ca40c540c01d0f4801c0c103140710130416a00f441408028149c4490402003580c03907450400c030507103008081c2002165100d15006103450300a039000c80c01845101c4ac0401d41c01c82001c00c04088954020b15840d4020107100700920040700c540485c1103c4038a4101c03036103400030500c10713228035540240d00107981e1031914146c2000c41d0100e030091402191703040010001203011f440708440e156000003185445905a01d820101849 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 48507549 1250 48506299 48506309
    0x4050c0a03060e07080105010e011406040312020604030f0804020d03050307021002040909020108220210050909040303090b01060518040209150406021b040207030507020d02190b03040605010e010b04030809030304 93
    0x29450000410301c0407a51040f00d14524503019580030135a24441582a60020300400d00700d02d030350400400840c0c680c401c01c07100d04440a46028140b594a484a0000d403052240f448050f0b0080b00402c0308240d402081c07048a1050340c10b00800038186900460b14100e04584014140403000021516880c001c00c1820703203006580c0c009550b11606d41085201402d011036080340814101e0001c141d204602d18400281909030f070292040015254082182d9454511022000c0c0702c0e0401c90380607151140d80449208600a84003c91036038414505910a40b205a0010301007002c00d124072100c20048081c060001c080840b07015803500031003c001086100e40c1c0d12314225a440001c1c00007003039500810f4141649484e0360403039090388945010710040e03109124000700012410001e01c001407a110386400703200c90000d0000c46003120101170142700180030b60032a000310b4201008010400c0f946000b841d0240080d0300217003140c1c0d498060202228021030200410302c07500403a0315200d58a0800903200181 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 48508799 1250 48507549 48507559
    0xc0c050a08100e030304030c112407030e0f060a1409040905060f1302090402090403090302060408070e2a0c030c0d09060e0114091302090d0302010b01090602010506060d0504050c 78
    0x240e80c541c0e1040e9940503034a0356440c51400c0142c1c011407424040207a81c85550161203981000301242c0d80c1c03200420034201d50b1540040b140b00300202c0c2d4598004c503168038412009020390349404608000e000140da0b88000d910501f00000020200d0319030b41c083e50302031050b5040440d0341703410380c804100c45030084480030344d0070901d40640d10040c4480007940b03501a00304000c280d082a101c07001806201d1400300006500550170070003080c0181881d8040750740c06030103850030229480d02ca030f0014429500c00c0d070040640b41d10402040c8018080f048615410503020415412400e48074401000460380b581c001c4903020300c02007140c0c8001700c0c003881224030024115060303030040040418041c0440d030a5000b11400607064401d646141e50050342c2162440d500c0c54806070a0a4000b81000046085080e103040001d40074400740d0030310386030300b0f108942a074800d030000302d100354240c00010b00f03000180e0b22510442e0304201c10b2002640312401110000410728001207500d50316401c1c80d919080148217005e03008 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 48510049 1250 48508799 48508819
    0x30309140102190c030f0f12090b09010c0306030b010306020f0d060f060e01021b060c0a050106121109040c060305182401140604050f011e081b07050309010c0c05 71
    0x9800d040d4000c2c4101000300342d5076958180d122004464a0456460040106440c1da0300c00307171a14040d40b0040e0380800540723050b002002101c11041c050328016201160001410001e020100c9003c1c01383c8845003410f4982004024650340f106080c4000c181b0014111940c00201450400c2c0844112202c1c0000340b1018818559240c81146590206201d03510004400d00ca40c1e41c010341c4003050440110607150003842c011450340080115076401010741c1c0d0141e200781c3d6004400610300f0701036100200540710010a8034803403030418000c1d00b8001030342c0a20901308034040000056099821101f52555031600085654456607610001c101550704421148944c401080c071900c044255401600604650a07030f0599a4810741c420701c0d400785400035840b450500c401d00031801c208442610f09001407600c000003170030000d034145004040e100c0342000144c2c4801089060040e922245034207070b004803001072404825849094607402621302041c100443d9075405000d006184c020384000d440c0c020b00c51006 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 48511299 1250 48510049 48510083
    0x20a051005130b0c0901170426130b12010605040e01031104020f04030b09011b02071a04090615170106050d05090c060309030d06080708060601110f0102030c07051522030309 76
    0x350f900405c1ca09070000d0800300b0b500c611110304400641c00346601c8401024144410004103483e00300d60101c00d002c100c0144008141140c02da41184020404112082d40e20441c00c82da090b0b03c501d0580040050050802041082e040490342d058116500a03c1020111844000042c013910419000e041c10880102c1c0c003100340b000d800d5066010303141c480e000b000fa9042c0f606500a04800441302c80340035800c840d5082080d940d44c28a1940740e11060001c2900d019281c26100702240c0e01500640c0808a8071400b150807580c010405c4011650b0368803d41d011589840001040346c41807610310004641c035180400d409140420401100c41002042c6544a1a00560b541c0d44d03504000c00f240d09107828458001070000000c50041c00f0b8555600180101b43d40d0380d00151880080d0141c0e05001d80701c0e00e03288500060f800c0c0701075402035118100c9195034440609110386031030300c2004d0610b42e0b20b012130240211001700103070303454001540b01030290010005042c01e1b0000d100854024100310424450900 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 48512549 1250 48511299 48511321
    0x81b0405040f0b01020118050309100c0609060504020109060212310329060307060c080c06090307020a06080f0403030f09020306010906030c0b0a050f071106130e010501020a051005130b 81
    0xc40f01c0c02a802000b0084411901c1c904601c0000400341654008020030b221505102c00c4002000b0443e003001026800e8940d00c0c0d804542c0300b40c0c01619219525400d0104643c0d1040e004cc0080219100501780000010440c40c0f55114420213060140500c2c064196013041d01c03256000c91152848881031040e640e8201108481039408400024002c5030078001144000000114001d50010340103110b05070800d142070303401241e803000035a90741409109110f000c8404000448c414400400950f0f01c9851500c14440380e5007850300300743d061141c0700040190155110400c0313a40260540b40108113402e80103510401040a460065058000c0170004152814290841e07012648070351012402030341e803002052024004d05440c8000594108584400b0741050b00286c0b00a5010750100301141c00342c0d80004031160310098800c003446041c90010400385103c10403c0380100340a0000d13001c03255650b9500da03210b440c03040ca05c014043e034840120303034040a04280c03000090351100c065055400c0c000c0d4408 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 48513799 1250 48512549 48512561
    0x120c0e0a0b0a0c0b060406030203030a120b010306030b130201050415050418020705030a0c080d020304030201050604051f0302060c0f0109051501140f0f04090605070302210403081b0405040f 83
    0x54051104840000703600508001180c01c0181c481d602e600404100d55070741c81c4000700c00742042c1da020351036603000b1025030b40c00d0005111034030749900d0b1002486920522001130710b24040d2aa41450301d01380003000896080d1030101d80c8038040e003140c0c10300b0120a03c01a00d441c01542c10119240f10810b0900c0101070b0803000070420f645485151035130703626000c5001000d0744180c0100a040e030f00207011800d030550240c000201e030740b0b00c11011030b8181a80c0030258022600201c4003940180c0d1203406001d03450401d440740540110a911042c2d4140303007a04211448095640302c02405480d0000314000110380510810300040c80c80d600171b0115060714100b01c2d070f841484580040c5a65030a0000141c00201510001d5007080060010b15400d02d540c402c10581ca0400280d140c0c206803510030a00000d0028803501c0d01ca40c03040d0b01e00503103c2284210f0903c0c150617150350740401ca01e6190034400400d03000200c166100d200c58031095032054024a40800c503005075849187c1143c2801d680208110081d0051 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 48515049 1250 48513799 48513827
    0x1203110301080a050708010501150c170a050301170601050f01050912070f0612180602090d0b01030311010c020a1502030402010c0b0a0f0b04050714180d06050601080c12011401120c 79
    0x35482d1513206c8000e1802c030341c804e100c3d40d84609281110004401d00441080c0682c501962031f40003044001290040c10740c0c04131070404e001910000040c0020440c58043c502d011182000404003581020042a041d41009149505000b00443e0f070070059510000410515031120f0152441c09030303540442c0711012413a004d90030105101c2243c800d40a085032051413030151951030154040411500c03200000c1d80a008811341080c03502210a01203024890002d00171131003a611080407448000703004d421103603810039450864000321800c01c081103a410381080f455000300c0005039a07403580e100595104e024034000801d820610720410a10760803c1d071201d00c1040c2110410700502c02000300300021aa422604400806e410f0050b681d55220044043c10840c421340030110300140c2840005101411440d40440b0400e8480b001c009055a01000a58000f00d00300b013198100740d9005540740c1c080c0d10500a0401e0a403502ca1403070420b0307200d08645205c1c049a940d04000d48850200000d0440000c2544 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 48516299 1250 48515049 48515053
    0x4080f0604210c171b1c0c0206222105060703060e04120e03120403060b0a0521010603140606010306050108010b070605060a0302030114070e09040206071203110301080a05 75
    0xb0000402442c411414058180303586500a2600d2a6203802c003030b400081c06140c1201041c4541e4500036107800d216004100458003d100d1078031030384869004860409024401c20024500c1c000c016101c0e441900e208003580504c0444410f1111115448508203901c0040e21002d44040b0040c100641d11008010a000303906541003559032030b03019006e9940781c0c13184410080c2003900180c0461922145041c240105250641c080910400000c9c80d000311214094410600010304000f08003991290005440050701c0390f183c3c851030321000a9061740c1d100e803181c00e0032104005a0300050f1080d40b02c0405941d0018000c02100380002c0c1c035641e030781011076440c2d000c07034902417000c51507601a0301c0381030403682c2c1248041d1a0020742d544007000b40c40d01621442e0842001e00d400320042e9028000c401e000c0030b082401200300e10340444020100303d0618200e9010301151014440980c03109070132100001d4001110309891550410114006c00ca440c1d101420040040000f10b0b05481c00300e00c0c0c1c4682e50060781 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 48517549 1250 48516299 48516323
    0x9061e0409060b030402090106050703020a0c1404050f1003030c110a09090203010f09051b010e0307030b1b0705100203040f0204090506190b1003050603030f1206010807021b041104080f0604 83
    0x4000701c01e1300c829103010790f0000600d00100030b854418001850500d1103841138501018107903880140083c0b9036081b100004591680340009800c10b8802c040c0d100e81d1081e03181c01c813801c10714800840d0b450180005010460300c5412002803103046481341500da44054007d589d0030703503200209001802c3c108400c0b071180d428032502c1424004540204004039400202400c2c4a02e11599240c03410f00711040418180b040b194007495542c2c0d020310160740114025151071b1100e01e4174001e41c0309280f4036000c01c0040440d041c0700340c03c00306600045000880c1080703840140d0300d8441c1d00308100078440c1c41d50001e5015090114490802101150f00e9000d1100859600c0b281c0d5030001c45202a00e4074240d8440e003020718203101e805214401d822103a00483d0150a4a203084001403510700c099201084034484e01c55150140f01948d680000300c13587c00f03038061025099542e10303050700c1c0002e06155504588030b2911000c0c0080c010b0150000c407001005220120380005044c44010f03a02c82e801241d056a04c0c006c400 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 48518799 1250 48517549 48517559
    0xd06060c0c06030e0a06050f0405060702070605070b041707031206060203120a0c050708070c03050c0a05030a060f0b0d11090105010806060403030305090a0803150a0b040807050609061e040906 84
    0x2516503151941c0070a00c041e8042c00d000046000704900081c5515511452a6400108185100d1036025402c00111406a480d0500b4252f09e0004050045801c40d40075250400c0042e42c442e00307444403907034003401d22000ca498905000000c60614056124180f100044540c10181c0052140b41e080b10366400030301c10b40355250320603610785c0100c070311003418600031200081117446160700005410700c1d242082801d05c4051b4540d0301840e000181c04032a030760754034242841405020402920b203544111801300d002c604050201e6120080d00400502c1642c03030b940042250b030003d40041c44074020260107030001e02d40c5414400c030400b0504403041e01a818160003c00d40d54403402d01944a800c010740014a464a182d40880c014030008101b640740703005001da00000281c0e03900c0154003a480d440c580a49444100040150076a91607000d004000c200b00010000313110081140ba04458080300d0050703c51150b01c0204025104141c01c041c40744841c00c65a144440308100904103841b174010081119540355 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 48520049 1250 48518799 48518807
    0x30c081e070602070504020c010e010203070c06060e13060e0c03030a03060611010504050a03050309010908030408030f060f092a0d0501290d0c0302120103050c0126060105090a08030409020d0606 85
    0x40c0600801a00f04e4681800503081c990001d02d20000c43c0c80c0001403035604040c0050890300251802c40000c3c0a0003001400d1290740d000d140040d1140303100b078401e18182204500c200c8040300b4001414141c0b83c01e1280c04141042c001c40d0482040a0113486c1c1c0c0e210030140040c000c1100f401400f01140c482c0d00b103400208014407400303202e0f039449030050585003c50b88056a8542000f05180910f6407038044804c0040d003000e0245004034072070201c4a8580c28038080f042d101f180001e000034003c55031a005040150744604040340c100c0201200c600450300a00511480d000b80c0c0401200e42c03000000d0005005c84050b4000e904031100700000b054954610b200d0101401c43c020b2080040e050706100a040d0380c25a54040c0c9080480ca080040c40d010003043d030091014002d0b417041d1382c1c94000d14601465540c210f07952001140c1401200075900d100864040c1840c20041e11942c10010003140341c002d1a00c0da003a11070081c2c803050781102e07142c2d5030303c2d0048406540840000d50300181070140000c3c440b401 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 48521299 1250 48520049 48520063
    0xb040f0203100e040c090e030d0606020c040b09070e040c03020d020c0d090e040b040308070c061802032103010902030402030a0b090d02100905060703050a15290a08010605030601020106030c081e 85
    0xc00120f5032406880c0845401c09003c02d03140b1f161140c0420080c4400e5100d0520951004004e00d03005015070003a802c0400007240d82d808101c0e070140800404208885902c0181c8044180f000c4900181d1440d800604a0003030007032000c010f415501c00103407000042030000e600360f003408a656681f202c2907100e5006400038502a90001c00c210854004240020f0055035065404402031408141d020a00d803074232000d943c1d5400051844046103480042981814003044210b6044a043c02000c50551400359407d44414442c41e034003107a021000c02c045607401e100c0788403038030b0300900b4100c10703402c104102c1d84c2c8130618810301d00c002d441101e0903448403a6440c02409220364122020303240640c0c6121084d806400d0041c00002c03000e0f90344400d0a00c008401c403040d07016252000360300c100820580140d824404070010f05c1070820302e040c01051041c0780d0083c0d1030340c152142454255101d45a00c0700603409044147c00090101e04000d03c081150040082c42482000c640e03e80365401d107420003003e90322455 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 48522549 1250 48521299 48521303
    0x903020306070e030a0206040902030f060a050640060914060405040506130516090f0302030307020d0c150c050610210503040803040905010510050306030712060b040f0203100e04 78
    0x807580014a403a0f002d0582820b100402070140c400711882640040d5030f95100f908604450303070340401809801d0250461180e4000f501303448501d41c081c01e040000e0310a005000c03401c1c44600d026201d85864042254201005502c082c0010510381d50303802a00d0798002c624001e03d0001000c507040025180310628980e00009000381c4800c0c5031509020600010f001c0040c5001d4002107000f00d084880200c6201d9540b02d6652801d080140310480600100030302e00c0c9500803180c4404194060001d030b54003200b152542d5904943c4c004052a151038020304070f820540c0103940b0340e485a03110380b42c00d540207004c441c0814421020745080c2c0e505c032005001c0c40d1344140910100c19880026201102800900c02d01955008030201c1c0d040c50f0b6141505459580f01d9081448a40c1d15140100628240700491b841c0c8901c203420500d066140c5074002c265504064410200400c540b88080c00c1404590b170300011501340003506c1030145560b04a0301401940c421f4622621602010a000901c4102d22641d940103079 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 48523799 1250 48522549 48522553
    0x702030a0804060506030f0a0605010617090601060813050a05070e0717010501050f070203240f01060806010516020603090604171201030f02010306080601060206040516050f01110c04020a0801090c09030203 90
    0x6140d40e100c5200400e8001c202c83c1e054400e061071501d4034601004000c2303065200711400b2600d5070400c0002881c1d02944011043c4103604181444541d074400328029043d10a207103031100e03083d6100d142d6072400c08501200a8214010310068000b482000308080e03098555800f40140e8039241c48030300b01d99042140800004411450005002d00d41c8035500a25408980900d224280b9441d500080e00307240ca80c1e44502e400450391030000042029088400742e0245004c00300345601e42c0f501102804000c40106410f04010340001d2a060f07000150040288054010741002d0b140e1400502040e914070080d10165801c902c2c410100c1d01c1c41d01d02c2d4045524040e8410982e44160346160340d04200c3d240c0d200c100328180342d03d545000c01d1501e001c020f10340c0240090790003860207082a0900c00d0078207003400d100d0b048130b080c0504248203584a100020500c4103082c64a804404641701000307003081000d9521942c0907000041e0081e090790302240b06410394112007010011800c0c0c80c4000d40300881c072407100940507 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 48525049 1250 48523799 48523801
    0xf05070b091311040902040f0305010501060c0203030d240303030b0301050115021002071502070f14070e010e0a061502030901030e0109030c0b09070510050307080912030105120c0a1d0702030a08 85
    0xa10400e403c03030402420300d60403940c20709407900c0d5040240e0700b0a4200100e440200b042c01c00a2107024018580101080c0c14a1503102d00031340c01081c6c13288903481c01c13201d10f96200c1402c200c041e1500ca0100340582c902d4942100c0319a124034009026004001e1038901c290b08280010900500c04482e10040340c060b40c004162411750800f0705000781d000f803013056401d401115513810162032140020042c051080204055013510317482e201c800d0240000e0052119440f00c101400744542001206064444102c008000b50f598620715002402d40350700010142000714a49251080e0000701603c11a10240c9061202e02c0041c1c11503400c81e0503156024001070148400140480d415401c00c0707810441d0541654000c80d140c60125184031004420b4500081c000010081000e6010402a800c0155400500400c005d0412061503500040c050395119500124900c4d4480000308499144150b0150190004030356442448907402e40391310464101c0f040b000000754030f207440401182c40d000d03a291155132071 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 48526299 1250 48525049 48525079
    0xf01020d031104050a030b0601090b0c03070201030e010b0d0507060909050405190302070801060f060912020a14030c12150106050c0a030309031403101802041a07020312070f05070b09 80
    0x10b004507400840d811501000702141035212000fa520240d0300800c00000c030707420075100041051b5500d510071101d1010505c0000e158550100880e030130960246808112280301d040041e00504000f0072903070380030007c903c0c4c001c00c11102003a4042100d1072600d803400d007195940b9580c002e655080740c0051503038100d81c00b401c4090104241c088005030003841115411500c0342c0000342100d60703a800c03002000320050010450164408000c0018140c01092900c01100540c0410144826800b460100100c4040c0342210740d01e003080202c0000c0402018400030307004480b540f54664109014020030702c41700500119466002d40100d500f090381c000c004014404d003548041b002407419020480402c0000d40030519280192000b4600900300501c0c820078091400c0200340c160003070740c000400780c54010b020030000e0314074204000490790012001e580c0d0300e5090b40700090400303140f10f6983c1428040495000288114945035080c100c1c410001c0b5802141c40d64840400d07401010b01c025401020290030406d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 48527549 1250 48526299 48526301
    0x10c0804291819080a120f18110406120f0219060201020c0c121911090903120f01150513050907030b03010f0903090510050705030a0306090b0f01020d03 67
    0x9052041c034050380407040c401e645010400e81034410408008a40520007540304060169104000341c4103010301c200c0d500f41d0342ea542c50f800340710002d00500951502104e202803030340c0c00c43d07207494204ca103040000350190005444804200e032020b45403d03e5541519040f424103228120a0740c01440c0c100402040740e548070b518956143c8070403a081002c1c03103a14000e083d010701494001e40029000581c84400f60001390f842c10100301000b51203070307000c5900e028558102007601e01c0c1c500c0c10001c0b016150400ea007407a00c10005038604030758100d40c40030100b03d1200c201001901c21400012031201e406d44aa400511002d05c003805040c01041e6005c003600300303140c0160000d20140d80214120010700342e4032000030300c0c284000c80399040865164450b400f01840d081c4158803129640d00d800304400d83c180d4034000e00d50b400c41d0140c030f80144082017411070300500503015201c139180d106045a81e41ca4440100030041e080a01c2101030040c100b803004901e5242070810f50440ca241079000340385010030300c40220 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 48528799 1250 48527549 48527573
    0x807050414010b0d0908071110081b07020102031e130803090102030d0f0e0105040503130b120411030307061802460b040305010c080c03040f030e0121050105010f02010c0804 76
    0x14401598074520440022042c902a247c11801903200000300c2c001e55050280e0f1003151100d00d0304010100c42000114281d020902c0320003103c910140b82c480005100603803a43c81041e45070340021180964841883c9107000081130040c1032107a851011540c0c400344940d41e405510031590140c0c01c24407403c2c690809940c040130400300c51460100348405900e590b603085030010f4405903403d402c005503205c484540320b01c02000501da040c03181494022803c0840385804d40142000708849066049040c0e103583c20800d580c00300d50804400c00814240701030b01c1f120248000000c9000d05c074140c0400d103040c0e140300010390340d94401d92107039401c2d000c42e440c10944160301c075000b400e1066414213010451400510240014601c241c0001401d0032148030b020f4000400104a6522200e0030400c1100152200c2e000502080c0d0608040b00201d400430016519081e4050a000b05c41408500345401080c107034108078101c60080e29901614001400c0882c207072901000340e5008140e6a4000c00d0015517001000 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 48530049 1250 48528799 48528817
    0x2060304020a050904050c27063003090418080d050406020c07081513021c081c0c030f0b010912020607060c0f03050c0717180a08070807050414010b 65
    0x4112503103c1c80040e8802d04165000c1d0750561201d42640b40038204502c12268a80c107000c3c00480485107038403038034420316000340214003910040d24025446513030041035840304c46240030003148030561064615902e070880103c15100b80d041c170886580d0014003030000c01c0a0b0341c0088c80c41d454126070700f400c1c2000e82005041120b480398204012001c080040c00800060071584014200b000611340603424103036400740c0210300722121003586200507901d90100203803103805846000141d441d20300b0312007564010680d9290000380c0c0005e0503480c28005500038a1a0513a82d2010402c00d0310100305241101c0341c161446010030f14142c0e0a001c46114040610085440203010626040705130741c8031415200d0b0000c140300401c0d0041441e5034603d0305409070950080c59080d007203041c49626211024291004420188010300001d40e0180111500d51180440c1c00d010302101d0340156211000c030750704c030310320b101d00340f840d00500781301151510b000c0c000c43c1c0008142c2c403180c0030b66900b010001c4045a00003011 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 48531299 1250 48530049 48530059
    0x703090302070312050a080a1a090915010f032907140f18100318060209030a0c0e0a0f0506030d03020a0504030f0b16020a050a030810030501090b16020d0504030206030402 75
    0x400a4000186200d48138070540d00c00da00d802c2104005011404007401d40310707226083c204444219250309075003091101b804c03500e400040d19104034440c01c140c48401690055040c02d0f0011074801820300b1004100e0340300300030001d6201079503a400d2194486ea000040300d005030000106510310310078076007203000400b41c4040520b081031456042c21036602034560088445000295507406180010080c80f41005508090040f140e200000c1d922603008440000c1044d40e012407950001e880400503483c50710342c03250440c000c55884140501d000ca60071507045100d6070803c00300f00c080f4401801014010304024000b4481036101e504c094010350860751001c400c2040502c0000007248102c61266a175a0107442c0c480042e050030b40400d016040320614440a5500074500003001410000704191044c0d01481c00f003203140c456592015840006910180003503092098540a104d103d402c2207000326030341d001101010342406405d13601c40c8020801000483c00034001040903081c218011079000e803004107 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 48532549 1250 48531299 48531313
    0x306040e01020c01060504060f0b031902070f0b1515070204020304030e0916020c0d030c11030319030f050609060102070e060103021b0312010509100513090c0303080f0106050f030703090302 83
    0x5003403402c9801061038052a81e4662030108094203152184030060403501d80c040043e5400e100100c0c4240c4806017451002c0455854a060099403581c1610580d6a202c00548406415820300d044450029030b0041040f0072222102e54003442d10f40754880d41100342807401e90429903107400300030003904010000d0b070502c13410307990458079941e41c0c509452107215104504c0200500400000746004c01003070031a0b003e041d13032400c040c02081d0840303ca103954507408000780400301e42500203e03003580200361b040e0f90859881140c0f040070540681004410040c0c43d0300400480c0e45d990b081105103a0181c8003140540c018000900c07031001042100395210703506040241c40c049512403400c600c031485020340485504013203545c1d940c1081c01c0721604c0c0141001c6409803000c4c2050380700d03544450014468035102d0410340381d00c000a9411900007544490708204640703421680d03410081d002081c111109440c43c640140045840307801001a07607a880311110515080d561190710540050214010a90962150714 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 48533799 1250 48532549 48532571
    0xb150c0d2a03020a06050f0105010c1b05040f060816051507030e090c040321020d110a0215040f0e040803040201030e0c12010c0f020c030c09040c08060a1b180506030604 74
    0x603107649520388203500800c01c025090604804551018269480c42d070290320040129070b03444241c141455030403000ea90825140e22105450b050544e1b484503403c00d0805d45259541ca00581c05071080715031802c2558045040a104000000c08a002d1260300100340002070300d0041d10f10004d80107182c804d0505140c40d4502e6000104500c10031548800303030207400541402040501554090794140070359500e00080d00c51030020b0744990f46e10f5600e0040080c081c500501e02c0c20200408119241c0180c02c0385d80f2000018240b035007650290040440304640b0450014200388460101da21403a00004010b0564986500440181c030150702009814860741d1080d605968031009003e0040c1040e000005d100e003205400500124040040e0005540043d08084219100403410707440b00c040c120707881d00c0e241e505d40c502450703c01515004940544114070401c112220107030b0000d020b802d03080850894036910050300f02d402401400207400030365403100c0204207d003004000b554002e02c00a101144141d820 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 48535049 1250 48533799 48533867
    0xc0a052b1e030e0d0506011707090501090e01050f071d0619020a030f02031215030102040305070303050a021b0612040203032104150c080c0705070504020c010b150c0d 73
    0xc5071a4088000d103106100d04254215908400c419400e5031400c048110a44175603884030301c14402c500169601c40d0611411103011311141d409004400420481542c450303007484020400082c002e1081d601c0e001c04510401c0800c2140c80c440c0610b03545800c480380c6003500a1101c0480c0c425221313048041441f90024401d10304a548020b806191f0003028881c50909000700807000e10100c0000b590820824400e045203100a02640601c0d01c1d08000445000c060129009100e20350028083d800380000100030980d0200091400071655030031114500d00c0507000350b6441000100666200344100929803c0721141c0c24111b60250008041d281883ca5a0031030401500d1100040441041540308120404c84894403d4980543c070300401c1200700c421080150500741c0150520b080042e002c01d00c102044002c204840150074007810642d210101c80c2c0070301e03000e0540d020f0701c02d1040200040340000b0302516425950342482d440c0c0203201440800500740d503005851206070b61200c00c56140b2610700404 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 48536299 1250 48535049 48535073
    0x207081c0201140f09010c140703030902030703050a0507030b0106020303130303050405150a06050915090f04110a0b04050f010e030304090f060807060807020d0815060d020c071401020c0a052b 84
    0x100520910303044c54005c40050841e076510b8400418072218614000c00c46204800f03680e00c3c550705050002d0001c020b8000a0300c0c0c00c0113540000d001e03106200c000320821101048581c2100d105805245880e620b4020a80e12404101d400900e2860011411400704e072081d0455508603025200360f440c2c6c3e01e0014541803c040e07040b00c00110f2151900d6041101c0d040c01d820490780031102090110b0388003410340001d15400405071050b581c0181c80b41c003081c281318080c0780d4902100c0008140b0207a0b16a90843c040564003d845114401c0f032504001400c06e500a000405d8030b410010040d40c586410014044000c08007080ca00120381d64a07000407540305020890400907069030303100c2e020a4581118000d203000480d15403c402c0240766820b00c01c00b502800e60405043c202190819110381092051070000d00981000d5a040c0c46500300001e42d400d00b40038000c10000b004e90995501089007800d0001a450522809400c00780403100406402035000035900104880100c01e0503d140e45c0c1c41304101c10070 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 48537549 1250 48536299 48536311
    0x80d0c030b0316030c0b0306032e050106020a02031002030c04080708010603020a050a0b1e19080108070603020705030d020f0f18041406011e030204081e0105070207081c020114 77
    0x15440c241c6038014a001c0066000d04203422a400c882c00d42544d0341d50350381c0720880c42000d2207000d000c03001c00c5440e6014002c417640404164030f890250b54407042104582685540e0015640e860b1000118030390340f0100302190714a8000c0d0090021300302040c2c93303000940c00201800d29000052102150340c80e0140030a80081a90400200b1517504500400c00d0407006540924856488408200010701095082d948906205440e1030340d481d0b140305034882c003441522400d4610b00009070000e60400d412107911410b0321824000c40d200107840b00e000ba001c9124070480030784203900c1403080d2111503695030020060710010101441c1030080060f0403031f005d03401403480481c080d206a040ad5640f401c05103d0f00c1c0800302c50121042041c2440e600103003102c240301d01041d4980a40c2110b030840795011390119001441c40c80c04590250200c0d56080418400400070040c895080c00c0200d0a003910001c1c20100340e843c004054102c04600c0d251010724112030541650546d501c40b0128840d050400050910505d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 48538799 1250 48537549 48537551
    0xa150807201005060603070f030b061b0109050f01020310090b030705030106060203030108011a15032725080706050a0324060f03060e01050d0f0b01060507021c080f07080d0c03 77
    0x1081d8606040190f8400502c0c0c0381c01450280104a00c0c00d0307019851104514036400c1c005905000d0340c01080440c8202c0f8030800c035450040d0faa08a01940c1503018060f880e000e070080c2c07441040d00f11403d0707090f0721060b107043c1c10a42d6840c44c01e00c20841303958001e8070080ca00a0458105e59030301c07130119096802c1603000d580960408401085910820b0060080401d42901001a1a0b0385040001d448981014608607000e8001c80050341d841c2e02060880000c045400020030700110014070749594440003628805072680da03904141c8261046000c113002e03964450041c221050400e481110300e50030155000040580300e801d1040c61170482c2c0031911208032070507581d00140b410300002800c41c0d841a10701d03600301460680b040102d0446100180e0542d8402c0b111451241d40c5810101105400314901502070600c0600014806070400004c00400b4400e4855141440005031400300616403010b01030300c150810081041e2038034451000b00748103485600c065085c800c4c0f03802000201d603c0817120340042 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 48540049 1250 48538799 48538813
    0x100519090f15080607120b030a021203040501020d0507020901030201082502070302010806030d09061101020c060a05061503100b1c1a01030e010e031b030f03040f020a050a15080720 79
    0x2d082e040c8240c020f0b00d0150000c100c1c81c18040310007080d014404546da04044e44c1c84000d403415a03021b000e46001c95400401003403520144607501501c176402842a540548914600f100007a4065420744502980050074100d05170f10b59001900d2214000b1b000303020105d540e5503c5020035685100300406c170314199000340f5280d821840050400c00300070302880c1c46075008c0d181000c46203611440120a07514903280030b45803a101084114064000d200e050445c41c00b442c42046540149580010322502c0d08843c1a0300d202c0c41480958001d100a44030342c00c1305c1c031800d4014408051314030010f003580d400c1004c9040400d501d042d0004200c0d00b0034400300da4644480041e1041d25039150080d030012101030402000544c0104420540d20f1042956120f0b840090f01d240f1100c10b08240709650000440c402c41316a00d00d440d2401c0543c0482e0700d03400328802c158442000c00d00f400c250398044165101d00c1d0007104841e40c41d04003901c408600a00ca9400c001d446890452041d40e460640301d50480900010400 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 48541299 1250 48540049 48540071
    0x3040f030b06030105180d030902150a12050a09020307150e0d080901020d02030306010e1c170d18030806040504050115080307030e0d0305030c0c0c03060103080a03050f100519090f 79
    0x703441c00600001d06200b0061b180320640f91000c1409222000307142400292400c0600c00f04d1003022440d0494481e40710b020400c0c0c05800e4000c0115450030024403800c02c1035940d012030500031a44100c0b006034050380144000d0140300d1400703512000781605414076120351505840058128415200100e9100702d021a50b00010350701004070110082590000d10704510384100004c1c0740b01c10000d0310707601c1846007d100c2d05840201580202140340c201c101d24018004c1c0010310a400d40c080160544c94902d40005042d210704101600d0400580c07594802c010b6031030f82002c21000d0403001e0401c0d01c055503550200f03503441e9800c03c070010041c21880003031929030081d030401505074000c08030854012280c1070b8024000903030100c11641d1101c030080d04182c44480c203606540c83c2c00381d80b100d0340c0c3d09803283e00004000e03c03940801816065000755010b0000ea1344000868071820003e444407003c1c0c40340d10400340420b10f009050300d440410044004e51a0595a140940541e01201c00e0040495554814800 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 48542549 1250 48541299 48541301
    0x1b03041d060d05100c03020c010e0a03081303050301060e0319061a04060e010902070f0f03050d0f0b03070504180605040804050a050105070b060f011124070f090e070203040f030b060301 81
    0x1d40311408650301c1800c140c264448648402d1a0f25905038042d503114001007009020b03a05071660b08a55400800c65100c05688039903403484c0406041d000702c2c02e11400110940e08101c40c0c00811541035803414116480c000007035400c2c0c001c011490354140035106244081c44401e030f51680100d8091500400e0a984590800c101c204000074041d0240d400d20400703010042e00c4007050703811074442c6080181d0795034290400c6603c002ca500801400d042c0320703442d00414140d126001e42100010a003040100201d41c3c8041c000302c1ea00c4082581d010303005080200800d1031301d540100c400c4180388500b01101c4030180d66810442c0ca044408881602c2c0100b000d102500b04a4000b2001d8007003828036a2810a25880d01650440010300d214850010114001220707403043c3d4000138651302e8078040754802d1281542044a252419003c1c03c49801b221001401c0b140c4203007050710342d40700607858408040b41004e1030483e40d0240100000190f02c41048006684203803140310100450040e0031142443c100102058 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 48543799 1250 48542549 48542551
    0xb040e010204030c2c0108031804090f0b0405071d0405010b0d02030a060209190b09120d050706050c090d0c090605010201050c04120609051006030b06120d051b03041d 73
    0x280450788180414800142100d240b0b100b80c0d000085840302e000158010350250700114201100000c0e94070000069140c400000781c094402d02003003200d055190081400100e0305c03005406000941e081101c07401050002c81c80d130350014012001e0302d141a0b15042d480401c1c0f0f42c0014000e800002807130401050080a01c6041c40e080003c5a82c00305421142d0000b96581d101c5a101070a010741c00255212244d594030402c941c2d50070040788500b0441c4d03480082002d213030085041c0c3c6005040200e48003c0488010458800e0f101d4691904c0d810711400c1d84a0a000f071800404006040e481040318008a035140d40401c80090f12405540d010f03a41080c4003c01603582c1a032100d41960b05000510005081d04000d403030590307040f9a009050192181400310280c02c4006003e40223020f0341e007000035a041c0e69001202a01e000d04c0c115041c50303c4e10380502c1403241a41c0851401d54021007007c45120344039030010003c081840f60402c102e0f40d888142c0504584c400c1d0b00211598005c11008204210608201 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 48545049 1250 48543799 48543821
    0x51903180506100e0906070504061805030106060801050f040b0123070c08061b0f04030f060f091b08070305030d05270303040606050d02010e04020d02071e02180c090910090509010b04 80
    0x41d1445007001000238045000754000c00090008007410030603c0c0158000340f000034035004009020740d540e20040038040400c00e01485000f41c11090310351005013800e003e01e507507000040e550384000d072003110118941090f901b0701c0001d85400c00c01c001d80c0030400051629010308280b4015000504042039070030740c02c00340c4e95842c0300100424082c11101249103c03e50301180e03004441c5540d04842480c182d0010005408401030080c0b400c0b00060a00448994140d00906803c00e503000050311200d8942e81c94843d0f110003080b0b039004015103000b9420603000304d5040603900c20b400c81e42c40a055000038000d5a0740d09000180c0c7c3c0b012081100340190350080360002e000503a804e600881003600024206d02000c54458003d0781c00059030501540c00d681102c8805070040701e05040c05013040880f03022082a030000b0b078815500409515001c08074020a5400307160220059440c110248040c48580c1c01d00401c030030f070a9802d41c20300242c45d01c09800b58174801c1c151017000040000c0c480b8100002c0307c20107040 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 48546299 1250 48545049 48545053
    0x40603060204261914030c0a02031e071202120307030509030106050406030f06050709080313030203010e030301261009060e0607091203080a0f060e0a0507051903180506100e09 77
    0x14900c0f0940c40466400b00c000200ca80024105480d810112401c003c22018024144000036900210320b1000c545100041e108400340c1d0300111855854800b19a140400445150064903040100d10703014500701e210603101030201c0c00271301e807810141420f40c3c0040406501048000460240d149003c0c03090b017000e001c00b12409c2000a0440c0ca03070390125064940024101f070313a1079001c41d0406004004440041020404032039940c000882540d102e000e8600c0220300941c01e00215110040011055a0680d503055600150791001210700000c45c022000b500e4001e40244a24510518103500484071864010360b800b1515881030000249410f20080441040040c0d441d014030561a41805600065815207031101d0541c42c1c01d0131580c000c2011420b00e1204a00d41480099810800c2c0a02841020240c2041065a41e4900282c8a42c440c08140d0511030002103180e02619010380e00452001d51100880c50080740142d80d1586800e000359401c07078030099060000c1000104803940d560340007600d400 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 48547549 1250 48546299 48546359
    0x307080f09060403080705070501060512101401050609010c0809040501060503010e0a050103230c090709030c0b03012402030d0603080c0c01030b0307030314070b0106081902070b06010f0509040603060204 89
    0x400404c0d1990207040c02080080c00a9000c049c018250004005000014041c0c0041419142080e65480055800006090900c9110500350040207e514103c8030040c2c03500786400c1d1150300464048810341c030100e4640000340819400380d12540f107a50b010702400e440c0c403a620b5050203120f5080010040c080d401482c14074006000080480201e42908681c03454844c2c1c803e40c11192039414180c202c91015085160301d801c010002ea400b41d80401124041c03901914002d485c1c0b50284294071003409640d1305000d040355004200040c4000c00c2e01e42400e00d1040e68248009148a03405480c2c0f203610642d030448000c1901e403072301c00050121202c62082406c04101c10300c2d146021984415a500c00030741848605e5402c200f035050044102d842c59079000c0031208035503854500203040042d040d0707030407040c8140ca04426500447c0610031940042d03001107251180d41d0350000111010a80e02d440541081410301107151075895074080c4101440c4036940c0540c546080c06407840e48090080048007016561031 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 48548799 1250 48547549 48547553
    0x504060e010b010f030203060a08010203090a02010809120a0f03020408010e07090f06050a0521060a02030f0c03040f11241c05010506030f04110d0f0210021c03090609080307080f090604 81
    0x100e403080d44c4019600340940c481e07a816000921061859200c540340303500000c00c000c40c03d00c002c04d5110050b40300741c0310014140c0344d8442e035030b0ba0b83c1600e000b010010b010030000c44500b180518450f109620403894098580390300d0300c0c802829a486183c0340842d545c024030040c40003804038002d0401f0507001c510100041483c03e400242c1200c120702c02c460140d00006081d0000c420056050358508020204607035060400041a1000303501c201c03001801c01f2010030200d50095000360450303004035000300012030050102e8440b11619050408401e50146140d40010403640b22801c0217030113080d03441102e5031903814540707003000307584000080009501d2030500107100c240d03500420740c0d030410070140040d00c041d0b449240c094022000706006a5000d0842c0d1200d508101c0c1103e060420140b00340c1e276040d1840003162050f641c80e0852580c078800c07200e03030b0700c466500035110340d10072803a41d4042c660204e1302d0302d8640c0b10390701c0036401505d410740061032034010022080301d00010302e0342004010300140301ea45403503 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 48550049 1250 48548799 48548807
    0x40e010b06042106090b15060f0703050a110d050406020f030703090e09030702040603150b0d030807030903050913050907080304080a060b0f15030618100b071b090504060e010b01 78
    0x15010303c4000c20f0f44411000b554554010f6121800c030b0f40300300e007084499400d043c104294601115401c00f00b101d03030070406190f0304200064406c15090400218140201aa420340740754000b2002e410802ca030b100c1440302d0a00f02082a4401d41d43c6544895944505161009040ca40d0750003e4003416441040a440041e03480310003041141e420500254040c1c07281c1d08114150710510b040694000c2c1060400320138007080a20041d1503a1005c5010010019603d00744991030a0050340633003c111107400141d8400d02035003004015920a00d8103d141407850340004d480760400400580e02e0715074560402400d0305d020080171000c1d20441e8001c6060a280c000c2c400d40e41d05a05000900d01c54540060b88059120207910b15070b04031000340200b655171500d1081d00303000d0300101c40e0144100f0821502c1c00c5030050a000e0759010784000c8024051041c01c0480c41101c6510028044551003040007a203600034108500b80f00141201c0d08001c102c81c01c0504100041d684080d03141c140b140d1516540d05c030700340e0b04 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 48551299 1250 48550049 48550057
    0x15180d080a0b090903040608190203010f05100c03080c0a0327020f09090a150617010e07050a12060b030c032410140108060a0909030203220b040902030402040204050d03020c040e010b06 81
    0xc1032420715a00d556011801008278951302c01183d5840c0040000b0403032085407aa04400c1c0c400607900340a40b0901010301315409842c880300076010480880108400f07940fa080140303031049580c180401c151070841540304103c02003856510507000f00740c0041045182141f0688211401110711901c90b040622a4030340713910b4210303070080100e4103060000408074181d400c500001d02500e402c08503c02e8622503030034040c0460080c805003501440e5070100c0c181c030702045540300b680d0501100c03003a04240c81c1e5902c0c005119140704590715202e185007010490b0307010401401d45003610914000028010655503207103000182a4803001c054002040c08600074102031410042424030f4903820b01e807903e002182400c1001e810040380107040c41c5207901410340000003410a80000010b0054540041700a041d110b4130f54004c0c5005540200410400041280c0245800c03900080c0b005140c603540f4000a584400c0c081c000702c001d40c00076450304180c0c4c0b6103442903da0744207102e0003c2c890310040c4c50001f841803107 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 48552549 1250 48551299 48551309
    0x110d030c14030421060b18100b0f0d05060307090504050f06060919051b0d1a06070302030715060807060e0415030308192912030c15180d080a0b09090304 67
    0x601c16844130600090f900a0404a500a0800300149850320580e941c910000c80d900044a8410800020105080350846a01c00342840c445424a505040c80c0f00190a020f010603a061042c1c0d40c0100c0c0400c1540b0410740a00d203d1320091001e00088054030b414240c00030080c0344034165074070400902080195810002c80d03801480041e9607543c5085e03102500d045400072900b2042c2c0410b0740d0010403665480300b40e00500d02e0341d5030490b0300c450b82d00b0041d061098090003401078005000c802c0008901e0304c09020001070341d0b00041516500c40541a2400140c0c1d0700090008501004110640c1000d00c12090464a04045228200d00b107407800303041c0f5480644000d6045120062524907400e095005140f9407004910381682d404020503060708403948035001610030341c60102e010742d0700040002210820703c00d07070024020780c001450f0b181000702c2005064900202c003030388132010001018405d42028a003151508441810004941c0c0b0490b1800082c15014900392418440c03c00e07400020358044070 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 48553799 1250 48552549 48552599
    0xa0c06030b0a0308092d010e0d0203100c1112090a060309020d0b0601050c01090b0f010b03071202031e07020a1b030305070f020103150303080105011e05030a09110d030c140304 77
    0x18855010444c00c480000e0042110b80130b81c4011042419103142d06800fa450923640c030b601614100c82000158101004001d6050b480540c07030000105440d045410070030580e04107000c0e1061540d9030075040c8040200c041556440018040703000e40b400101c41c9000d401a45410000d00c00c0c03c0d0f0201d0360001c0c440c0d0000d4440300ca04000035185a201c1c00449404502c440000e21254285103012a0100301c15501310041603062000404d80344010360136203202c3c40c11951101e0800c5201c1d000000203610150020051080d13204801110002c0718141902440e542e900030002480907040080c4404001c44041c01e00b850201c40410102c0c1e8030606540318180c110400410710780c050310060b4014181c074081000707113403210348001050503000151141210402c0c4c13103a41034143c24034502c0e2042a0800301d00d00c0031410500c049091441298008600c85100c0c0c14a400d012403110002003590a00704000c40005480ea0395103000c0040903a08001402012001181040e04111240c0e02500042c3c035000d01c00 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 48555049 1250 48553799 48553807
    0x6150b09091b0d0e0106060206090607081e191a0d0809060918011d01031e141c0908060108191a0703020703021509060a020705120a020a0c06030b0a0308 67
    0x301c0c041c420440c41d10310702480403543c1c032070244440d08064004078140c140694a040342c0002c07240d0002c1505481200c6100240005544022090343d0041014204408003103000c0701c40480c1401450903103004503242120054000fa2104d2034500b5100c54000c11910700c030740900c0c450310321380319180e0484400c0d40c0440c403030380c6990403100800d00f1801409840350340107500200c669488030350140d0442c1600d07803190300c141505402401905401c8001e01c0002d0104c80c210504114801d0881d0f846191903105844140380c80040e29510352402d51911111803010300515580301d00c103030300301002400030450b100c0903018a40c9010b0300c07541c48202c0c406c20a4611018440b00504114500d01000020343c18420609903c0c00d00b03010040094210b242e0840140c440c2d181111046103403528200c0c030605514001304540c0da02d0440d0302011b500500b0b000c90340c0f0f1060110910f00c405407071000d0b10748e20f06940d0003460200c4041c1013103061010203a009605041c40c107483c09071207465904001042e29081b0416a1307403 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 48556299 1250 48555049 48555061
    0x914070f060e060c010f05040213050f04080c0102090909010605210304050103150f03050705120a0f03030b19080606210c04020f070b04061d030c150711120706150b0909 74
    0x20038411321380981100d5281c00c0126a80d0aa5544800c1c0141d000b9a007001345000d105071104115a0107030b410f9140c8100030310000d000295402c0081100384c4600c0005401c0800203004601c005509813803021850351540414070050601c1c060f24106104814031000c0000e103000613542c2c5a1240f0f0040c1410961110407001a05507890040d0780140100103022180c140d40341000c0e61604414021a88a00c065403a003031009200000c1c140000d940000c5400c0100780a650305030004c05001960b540c111030f80028403040c4400c040c10080050681001070403552909204205801d400780944502d6042c8003c151084d200b400503000c42224010f80d00140d8807525904003919600031400f004081c0904081004200001c98001c1c46000d050a4040c500901000302c85a40307900a0800c450650752000d45001508000703c1c2100e5004983c5081000c448603070620b185052004503900307a220060001050350030000d00d1f120b5040d90a00d0000d6500c84641030801c603503c2d900c41e07030301e0a0380304900301c40101744 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 48557549 1250 48556299 48556309
    0x1150507080406050901030f0209090708060f0607030309110301090c0308070201180b1b010513230a082106090c07030e12010c08090109020d08070302030c030d0914070f060e 76
    0x180454015500700d85682d900c80c0001d00b241c0c451034078a070000b82000c2400030075000302d000f504c5884000801c41c8000c3da030341040840d14560002c1c11300b1750040d100032a000b500d4031060000d120f5913000369000b14900103070b0305004140b50064242103000b40e2500c0710324008550315400c103006580e80003403255910399003400102c0322070140238015100300342424400509040b1110043c040307140d140310000005048a50300d5800c0b07403000c89240c0644045414070000007112503020342200c032140c188110b021049180c04238603090f01600c00303c90310b00e07001904070f000380e417001c94071401701400710f070103c0303251800e035011804c403010283c80e81c44a1400441c60a0405015161907903c101000e08000055410010240d010b806182c0c0101c0101c0e112001052a04406010704030b0816005440c10fa4900f415548607642540a60005d6085010602c0005803512080c8010820b0101090380420a65031500301314000b4011003200400960149030308111600460305200e01310360f0071b414800442c01e55031010503 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 48558799 1250 48557549 48557557
    0x70212010b0301050a05040506060d0c18060909060b01140903030a0c1a04081306090806130201140409060302040b100e060a02070302060c0d170108030412060f05090a02030606010c0803011505 84
    0x240c2c1c15401e000030800301c25040d501c880e10440c001c004542290f00c5010921001c11880d48001e00503c01d0b070b40017441130f0358400740c002030301200d10381000602c10380d95642c000c200c07449401d00311144d86d105c0703900c0c3c0c806683c09a03d14081024110f40705146c141140d0009940f44074001c060414400d8003501042030000c5045d100c030b08960604044502894103103030000951b405034045480041d0a4503010601901c552511800c0d074849500421490302e400c400300c1401d01e0181d100301d0400c072142d5400303020141c8078030103400280000b03040407404034218810482500c80c5a101140038296141c84d10f100d0319803096080b4270104041d1111a601d5038100b00890801c0003540001c0e40003040020340a8980310001090018007069545154880ba601780c444c0d14207207802e1041c10080d40c001d22091215001504862985a115900c00076442510300c2d802802d0303c0003103694074003e40003c3d48100a505003440815402002407070301d49809a990750b0b445503107002c18010f404a070082070008080f081d00a00840d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 48560049 1250 48558799 48558821
    0xf2304020c011406030d02010e06391905030601020c01030509010f1103060901050406050a090f02040e07050a08010e1306050a2705071d19091403130f0b07021201 71
    0x288183c0050300b121000095054500360300a210f40c00010481760301c1071040941c81a43c04014152a40710151790700400b030000c8a101008282c0b00c44400101500d007a11070b40207110810000740c4424a0301752444418501020340c80c140f00c000c0007000420b03079003c0b444030703004402401d0004407900e03031900040c01404a10600310100d403a140b6900384c40ae1003c03003d03510610301190b03c01d11981c4c0303880900080e2a95441181e070040000702051140d0859078222074280f11000a0050410341c1d104116101410103030307818004118002024100742d43e0020b111405010b81100404240c00c01600d5040000c0b11040040d2405544101003061600e41e80c0040800f00104141a2142c04c0360800700000f48042e000c080f5114070801000055a02ca8202500030408600e42ca181e01a6942010500b01350700108404100750707958000d210000e428135440d000c85000070001035855402021590000f10242c0c0c01004131802d100c1d05c2004004004001c0341c2405a042e40e000400324224200380f03015045140403 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 48561155 1106 48560049 48560051
    0x807080316080712050a080f060901092003071e0305060607060906090c060504061209020310020705070b0c0a030806180a05061908030a02070f2304020c01 68
    0x200c0c00169008500d110f29002403079541155561081c02d0b00004900049084100e142e0f00c10800707940151a08800100c44c01c061001855441e0140316018410380ca400380f11005c000000740050050416548158881c02c00e100f001d424011515462004001042d02c0f41c46840e100b030107024004ea0010380744501e032981c00d850307100240c000c070078060b610b0a460758035000000e9a0550100018152a600e0540311420200000c0841c040b0107500400789003003507004000350381d0205501031324000740d21006a45000901d0b0042c10300e0915408150519408240c500d1200c00204990b0103862099030b4009140d6150300030400c801006c0300c0d0540840d4603010000326807280d680c0c401c80e0040c0d00140311a40102d109010b01c948400c15400c08483d5400110f08100006d80401100c00540070520941e82c08234289107501d01030000c940510404060010b4405400c0e840755411560310640802c0 = true := by decide +kernel

theorem cover : BRFrame.Cov 48381299 48561155 := by
  have h0 := BRFrame.cov_init 48381299
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48381299 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48381299 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48381299 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48381299 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48381299 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48381299 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48381299 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48381299 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48381299 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48381299 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48381299 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48381299 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48381299 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48381299 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48381299 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48381299 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48381299 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48381299 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48381299 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48381299 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48381299 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48381299 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48381299 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48381299 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48381299 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48381299 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48381299 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48381299 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48381299 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48381299 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48381299 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48381299 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48381299 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48381299 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48381299 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48381299 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48381299 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48381299 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48381299 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48381299 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48381299 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48381299 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48381299 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48381299 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48381299 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48381299 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48381299 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48381299 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48381299 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48381299 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48381299 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48381299 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48381299 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48381299 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48381299 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48381299 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48381299 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48381299 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48381299 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48381299 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48381299 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48381299 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48381299 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48381299 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48381299 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48381299 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48381299 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48381299 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48381299 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48381299 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48381299 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48381299 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48381299 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48381299 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48381299 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48381299 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48381299 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48381299 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48381299 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48381299 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48381299 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48381299 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48381299 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48381299 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48381299 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48381299 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48381299 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48381299 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48381299 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48381299 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48381299 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48381299 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48381299 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48381299 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48381299 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48381299 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48381299 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48381299 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48381299 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48381299 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48381299 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48381299 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48381299 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48381299 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48381299 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48381299 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48381299 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48381299 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48381299 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48381299 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48381299 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48381299 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48381299 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48381299 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48381299 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48381299 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48381299 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48381299 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48381299 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48381299 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48381299 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48381299 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48381299 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48381299 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48381299 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48381299 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48381299 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48381299 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48381299 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48381299 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48381299 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48381299 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48381299 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48381299 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48381299 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48381299 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48381299 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48381299 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48381299 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48381299 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48381299 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48381299 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48381299 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48381299 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 48381299 ≤ n) (h2 : n < 48561155) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
