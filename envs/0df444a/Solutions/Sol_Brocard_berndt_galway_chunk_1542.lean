-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1542
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:29:19.796543+00:00
-- url     : https://prove2.me/submissions/dcc6ddaa-41d7-49bb-b122-f2e012884b58

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 277158273 ≤ n < 277338129 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 277159523 1250 277158273 277158311
    0x304060b060f0d0f110a080a0c0c170c010b060406090e1b030f040510090b0103030e030f0715080a0b0105120403020f030315040e0109030e210a12020607140a050c01 72
    0x3104203194980c1691030f40c0c1c0d40c1c40d01c5a48003215025500b51b082100300340c8001e0690500070490000c00d40c1c2c5e11480740741503010f1800781c54510760001042d07012103d50074881c0c12075041050003410075030901a41482c03030701c1e00c2029102942d10740d548030b5190a24251400306615409003161060b11a03270b800184000001d034008501c41d4202d044100100e0400f032401528200c001c0141503041d40c58200400c000466249050741100d4061130468075400041c00028142a03c0003a0b1030560300c0350140005143c1c011001e015504056601c1341843d5984119018003600d580c80c2440340040d10403c190301c00300040c042c01541240c080e1049550103480600d103107140da8029160504400100901100d26207420f01945440c004650024000703402c0d2690064022652504820b1041d010b660489038000700c1c25145140501008040380c03204942d5041c00140c06100107002c00040c003541c07000590843c041c00d00003802031140312000c1d1400224110854503a009803041072600e54844122451481d91001 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 277160773 1250 277159523 277159537
    0x315050f1302190e0a12050c0f040e0f1b06070b0106082e0e01080f122b05090705030604050a02040c17071206051e091509010803070c0e09030304060b060f 68
    0x292444d00e01c1c0700c602000381802580e441480b500d48072542010000344041545400113006640744104410640001405403001a24814041c41000c5449500c401b00244169035803a0000b46599111f10403410711540748180c0c40d0141c0481c250400400400d441258081d034011448401038403a0035403c00c010026900c000800c80203a410481c007488000c070609181401408550000c1c039811114507200e94031500f00511140c440d000115078814000e07104101c410740101080184188140e040d91044021700b401d07603140400348a48280803420381000202039011300d800c0002000a284198200400303414184582c00800280352014409040540e1005024900d292900c2c0040c2451032032860413954160b11040c86000d41007502c103411088000d1a4600076002e84500055641d40703801c4130000c0300a6940d0300e03084600b00c0000298000080050f0100612940b604aa250799480d030741c0f0441c18060300d41110350b030007c03c0401c00142580d44034254a500140c0320f68146464000b110700a504101 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 277162023 1250 277160773 277160777
    0x108310303020a0210180b04290a110a02100e0307020402040306050402040b03190b09030417071505041404020a0903051b03010b12031210051f0315050f130219 70
    0x4102034140344e4041c04007a281c1407032000d040100e03502000c12a4104403202e40d0240070314641c08040f40922401d03422418100c1d94200808114448031100480241d104880361580c05140c030007010388101d4030f0002c40d031030559240d000704520304500c0101c0c030003000003420594041c0310130000000180c5950001e80002c5005d134000150701e01d05401440207880c201443c4601c25085880d0008504040c0754130b041056400c81d620780559503401041601c1e601c00c0d500300302e107894510030441e4008480000c8440c2600c00000350850401c0b01c4180a48150041e80075402001408890144441c00e10b580640281d02d01c600d002042aa0f0b2a240d103800c1c10301c4c81040f19a11400c0c110460000c3c1000d00842090b01410344000300040921002c407512406a05103102210600e9004600b02d0440c160b000d4001d0140208a004288541c5402a200c01070380703030701036010030304100340450740144403029001142c601402540075192400100700191131030070381002600303900703000410b0b16100f160300b44140d1201c0c80e = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 277163273 1250 277162023 277162027
    0x2102030a11120c01141c090b010f0608190b04140a0608010c140703030506010c14060f061e01123206031612030c05061015030b010831030302 62
    0x9a0180700c00c0e031080c03500016403544142d000d04810b9074403103200300d40310104050780e940f11900c0c2d04094010080e141400d200d46402c7c45041c100340f021211125040b1000b003074049a0b0650364400950361400304445001c0c3c5040000464185c07141c40d41c005548a2030f00800026440340c0d40041982089030582d603020328039651308024401021b0034800c92400f003140342020a03104004428030246842004030050030107850300085811a405084a10f16242c1c0c003048a11349202101c42890351010111002c003c0d26140101040160038484407280361081d03038280140e010441c2900540d4003200710340c0303000b120b07039074031003428020310420505c0c1c180c4110358800d07080d1090002a852070030201d025210900c00e03004131955260040446103172200700d4130b190801d54099440d0782025038020807421005803079400351500b0040221889054001910b02d1810104442481c08900310100c89070221802d001c64041404900d1030302544451144444440740d1006600d10902c02035100d1224446040300442c2e00 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 277164523 1250 277163273 277163303
    0x40206072f01090605160821151903020d0f080903010207080c01060510050304060905010b060a03020c0d05190516050f0a05120f03040f0f0624090e06012102030a 71
    0x110a01060041c0424174010b03007003c0c103442e9240c1d000010f03800e000b44800400110b40c030040d1809a00d0f045000c2000b402c0213071615004900b101d120507001318030341c401d104041c410901d9207140c1041006070394016052698128165445080054140360195210300040c8950f040903a4240000d22149200d96002901d5030030040766242511195003290b03100b140c10301c01201c0c1e02548442a6076209800441c08110340a85061880c0100130b05c01c001900002d001550702a09601500281814408881166a0070000c803030101c03494003690103490350856006500c59610b610900161071549805603414681c2c0145a6a00c0d1a0800319030594040383c1082100009005e8140419503c0000205007a45480d5030001441003c3c0320051000f000014910b1494080c040c20b5100141c0e40d562014040054a01c11301c141c4c2c01018047c119131281000468000c81c5030106ca00800000d400c0f89801815140d0800c0410020017020320f001206aa010140d401c016950800007000024010707a400807407121 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 277165773 1250 277164523 277164527
    0x70e0a1716140d1e050601030303061502010501030206190e030a030215160c02040c030b0924040209130509250612150b03071b0506060f0307030b040206072f01 70
    0x1c00c550100e6460440e5821441468a0f4018421210b03607000d0040510240b4024004141038104000070b441442014008070402d80c150b48013400b91105d9480e80041c1101c0c1d040200d00381c850900000303402050911112000b98004665801c00000c5070a1201500002201081c68910700c8441940140d0102407a00280201501c8007900f0040391a610002040c80c66400303000d2080980c00207000b555122580030031280300354042003a01c500180089020309080ca007400c980c2d507162080045013007200002c40700914141c400c0740e0003018090303e00c40c1c000d610107684100908008100c00a94051400129800c110840d20700755141421000c01c02420b080001c0104141c021410351011985418405022001e0680c3c1d000c04607120041044d65950b1108401c407403900034603a84481c0c0201440c201c0c810000301080c440d1003600b047d220141d101c0c074868101542c484040c40054403800329500450090300300302d0000c0800358080d01324a064028119207440214080c1c03040c0c1d030141c1c038402c0c0300c2582c190303 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 277167023 1250 277165773 277165813
    0x40506060409092001140307050310080303070c060605010201090b060d05010207020613030c1a03190209130608061302210114070c021003051608091509240708070e0a17 74
    0x101c0a10f0710745138004c01c00301c0e014150302c8060b1000c42270000100010794002080c0c03d40d003001d0040c80040d01d46070b003498200a0440b562040c0701301c0da05404c00c0000320b0300354414482c00b4030098200e0108050340e101d080500076607144228058540e9502007003000c0240e25084014812011b000075031007082c034a1400c100003d41c4143d04071500038200704000000c0103031604103403074100d804901c20000656858012344000d00c101d11140f504074404500004084065900140445410b0f40c25200c90b075940f0b0f02801000300082000030340c0704a21020b4525640046506004045800300001804006c000640f0049003005c8642d00009125061401c0071800c024101c299915100d08052102c0d050500401e50380c481114119010001e00100042140301c082003a2111145e44180b482c42a0905110154646000e01c0c800c8442c0c140c0c2c000e5041e102450303040072a107c0d01c0c0c103517104540c54944a200303d5000c8503050142c1c3c1e025810b1f880214030a40c030034404c00c11980c00c1000034100b00b0041207240b50f110b = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 277168273 1250 277167023 277167083
    0xb01030818010f1409030a1203200702010207030311100603080304030e09040305091e06040b03061e010e090442060e0c031f0602010221060f04050606040909 69
    0x8032814000115000030592413103461098180c1e44500ca03540102e45007105809010301822041d0203d140d00641641c004680c17200981004c030400e00a2030700e1840311348102903000380140c3c0010010400b203845582c1851080304844141c6e00302c07041020317001041d41c0a9800564219000006020070142c11005216002c0c105490350b9209152540307001d407890054600c824025034603c142070440414a408800e0341c584001d042c00d07215a25240d1a404070341040380c640323001d00b031990a00c00310703500c0450107019003140c1650b0b280ba001c041d000c24413025500113001143c4e00000d1000d00040c80050352500204580c112800d00e984040c0d02148205200400050440032072809400788030200e20104903942c05161200207550b00d885034a0302415203038a012000300c1c8000f0104000c00d8140d8190002c100160400281c01e40c6001502ca40e500451000d4902a6110800f032111880c40e040c01c6d0003450340498010001c50030103642e8201c2100762548000c080703e292090f03100c00f5400b081e55a0712000e032 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 277169523 1250 277168273 277168277
    0x100510030b090f0a020408060a060f0503060f011503020d1b030b19050d0302190b06010e090114150c01090b0a050a020f1803190b060301061707120804030b0103081801 73
    0x154a071290040b5000000203000540c0e0400c0c0345000440b44d90903a01242d0007404180215606440d1511b080380040c07466008050b0b00d1008054005901e00c0c2c001179a1f030190004500200c02a4601101040c010a161050105041e02408600f40c1c49040b8451003c51466001140c3d1008440f91002011101262000ac4c4a074412180680c104a02600aa01584c000351488800f001d05414260b14003404d030b008511124403070405000400540c0481c281c002c080c00e8880806400500c0d040001d201424010b580c000010440c0da040303207103040c2c402c0350801d002e00c092891a048044401c1400e44030308400a07600d05c0e0415081c0415520207105560b44030409640c114104000080154114482c40e400ca011703000c400c54030014079035824011070700080103030798070303010b0000c1c1d43d02d4148080071080ba02940709518000d0005542500702060b29500f416940c05810b0990600c180107480c4c003210780f025a02440240070100000c0c0d40344c101c044c081e50091503006d8540c51560102c1450341c0f40c2d2002181 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 277170773 1250 277169523 277169531
    0x3090801110412080904020c03070c140112090c0b0c030a02061008150c1215040b090106021c0c0602160516150e120a080903010606020a08190504080610051003 70
    0x14100c1e040c14103907002c1d00c04091540841140b54148105603020321002da5502c1480044c295086540001c000c298091140000c005d50998410392403071481b040c0001a404039501203441c0b425011554054802c05120320011506241c07280149076030358218800400e4150310025001d800560108a415841244e28081061080c1070030000c0e900c490200305c0c0d000190302d1443c081800e200d502e03c20780b0200b030322075003644000d45055140c201c0010004a030007070041d450800c8000300d50500703840450603101c142d0010045100003600440440541c14014020001204800000100303540002c1c0380b010402c80385200c0141c1d081c00c116041201c1d03c4810701041c420300130304001070301e803012245a09403844c2c1800035046003c3c1c0c0200b0b07940c00d02001c0807001402140c081004100c1000048d00349000b040d0000c111454070f400c000d07a40c500f42c0b408003600c200b0041c828411038490124400c8900011480d20900346540d5043d5685440001e441071111160311000034009420424680389000c6d00900e0180 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 277172023 1250 277170773 277170791
    0x51c050d1103190c0504080f030a120b0906090c1605010b030d02030403030f080703020d0f0606110c03030313050102090307031410020f0307030c02010204050d060b090c04380703050703090801 84
    0x45150b0803110f40d20106540c440143c4c0009501842c243c9000340441026128a4003110b0350507501d0f60b0001d00d440d070100705803008a480402c0f80b8490700100384c0001c2c040d6941c40c1c5445007008051140100a000a420100002d40c0000c10300000d0407900c1c1c0c030690001c9945041c8508142c00e0108120145003158028402040800e6110303030000c1c4000d29508040071503032200e40045010740b00c0c0048018001d8284168140741c07400782d070f221a042303c0c0255640301da00041081801e86404001d604540d142d4000c1c8023081201e1161404001140c0c0306500041c0340c02d0190010a04181c250340c130642c1e2040701171688025040c000d00c0346904840400d4003c625245100d424110207004c094945002c0659606000c2d6040d4000d50403500600401413180c60080380c145003307030180c8070740c00c01d840c050074020001c60100c00940c0103a9050380c8480180c040030300c1071146600561110344e120780340015100a042c049544041c0001c0c0321040c02035940c4c40d51a4080c0c02e028040e071031070741e00040306a0300d059160 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 277173273 1250 277172023 277172041
    0xb030c120102090612010815061003111204050f0106271a032a0f0a0e1e0112021c0503090d0c09020403062307080601050f190504061202030105011b051c050d1103 71
    0x1c41c6c240ac5403410001444400d07906030605a0007241407000140c07403c0028002401000243d518002240741e00a110290700e900d9007180c120100128040101c21000d291200403c0b642c011403a0a2660b401050300001018000b0340f5210040030111241ea0000500714140d8400e40788080c4128bd0550f400240f040300d000c0868615100c51103403039081c0c030959001c20300860110f0500c140c0c40107501040c3c5a1540c4814042110113490700c0201d124000d1142004c2e40c42da2094a201c0149420102450820201c00103010303494070f44800483d180e0400346c9020869900074400b41002d503001da003001641d0340260194248840001280c070302c80403074040410448a81c4010801c0d4803690078a0a139071584048c00c4a01c10720b01403086003203c1400c100c24003044059021000e80103e400030798070b94401d58040f6045601300c1c4028041c107400200409000301007045240c5e0315584d041e10502c200c035000b05c0b0308110b0500c61258010403c001440c001580c4000500d14081c2c5200101d441e8040c6103142080055 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 277174523 1250 277173273 277173289
    0x20304020607150b0a14030d030501030c0e0718060e010e0f0f010324080c091803030408162405070302090d060c0201060e07030c030f0b030c12010209061201081506 72
    0x100400028040035441440c4003941c00c000004d0102030a002c1d076240d10744104901c21500000e0a500a1203403101c4012514880d0240c98100c03a080143c908840781840c450300051000140b50b1402d0002c100900c01b9119442e16010f0018641590381c2e480d079282020005290101203600c2d1407045074400504080c5039614449280c28402c2404e0008010071481e9100110882405400710303007500300f1070006461000440c1081055404955065860355101c134041da100070108030001080c0c0c814800a40019402c8004210400b03081207105203544c819921843c0d04428807010100710710b682104850500018015036400c207009080a43c200455000402c40ca854407503001317000c040c1c4483d10810703518000e41c00400503203a00511241d1a1030840c201501810702c8400727030400645044100d4001101c213200700c8222180c0200a840a808140200540c0603501c407040000340d5802c02000d4495a200380061003203c502c580e04160030342c5400203540c142107641ca00d900d001159402000704513550b00203 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 277175773 1250 277174523 277174537
    0xf0612071d041e0b040e0f030910090f03031b061107110f010f1407020d38040b0709080f0115081b12070504090309050415051f1202120601120203040206 67
    0x800511300710203000090103071488a20700e030824041e01d05034103004c1c440807009100c501000d035040110b46480c0c081c1100c600d5140d21980c03012038100901400020312400249807441900c0c500740d03000c2201a12072004840e0b52007450790f0318100001c0d402040040d5000031400c0d803039044a024500caa00880040e1a90703a4661000d002c115208608042864044042e1040603402800040052001d8905801c1c00b614020700b0032038801243d01d00d2494030583c03540d4a81e0404500d40144582e48440e61803007058a0043c28410601000d20307004a2500c07820410b40111000c21070021a10080e000d444000c4106182c004d008160031017080344d550071300c040d1141500c0581c02d5400c03004000c10781404a0600b482600700c00da0160a00044200780b5500940520903284c1c2141c00f000b9100550100d580182c0c030b2882004e8001145d84501d1342c42c020741214040d011038060520600c101e03888100007080b41e03c06413241084a0710039007440683c0d648400245451549210110324606180d00041c0c0b040c02081 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 277177023 1250 277175773 277175831
    0x150507111f23070302030f010902041a09120d0f170606040b07032c040c0206160f0c081605060c07050a06051b12010303020c030a020f0f0612071d04 65
    0x100e0362032007a044046140c2c040e0500c001d0300011800c088100501075401910f111074410403010004c108a000c40c8229421203c80c039614541600c0c43c90003413012500011801075102da884400c0b001e260200780414061030080381d498110b03c0701406406403862070700480c28408010114204002c98454904035410748086010307081c0c40716583d1034100c682010380c1000c1900001c28182c0642c25101c3c0910034403011408807014481c66010807c104c1c0d035244100d900007020044a801d0400c003c1c01402442a486114a410080b600d856204c05800354481c00c400d030b00d03980b8080314100910009001140e00210100201480d02007151142c039500d400c2140090080c6a403075002c80c000b00980c003400b10340280f500c0c2a031526003c1e0b1604250ba1101c00740310503070241c011880d141070546400b140c20002035500400412030240c00c00c05000c1d600a40c07024480d000001040086414284991110311a0102d55240c5050f04140e403011010f0030409010030b40298142000c4c07030389109120415103100303070142c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 277178273 1250 277177023 277177031
    0x8010c0903051914030c0f1e06070e130903020604050c040c0503010320090106020102090a050405010b1c0f0e0607110607122004080d0801050a1a0a030207150507111f 73
    0x740c20b00c0f01282c96610070000403444001107207024a100440d11101d041d1148064500001c1c18601701a03010a0420340344409800500000d803494bc0106250009424068003690100008016050272102c41004c1039016038000d20030803041000812500f60180810741d401d00080c400d001001c0d00a0006000060060000d0076445e40200c0581059445000e0000c00d0b218842d65640b401a000398003007034040d405840e42c5403002c11541014024203040798410000c0303038580900600000014602c504003125a240c0b50355074014800014080c5603440032180003d400e590608e81c9000d00003010880000d903040d00200100714580350404041c81e404000c800000c107144a40049415030040f115114540740140400e01088a40c00001c84002042454030740c80c201d0390722207041003030700300e168425900507402d00500c585500d41c1e80c0000e0411000c05040150400002c0e544d00c812b80c1d5020350a60130b03585da642081005541d406140c01c42c0d81039001002e460842c61011300104c20f1540300308908402511 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 277179523 1250 277178273 277178323
    0x10b0c071701090203060408040302010206090c010e0d03020304030f060e060a0c05090108090a022e0305040c270608010902010305010506070530030a0614031b04090f050f0708010c090305 82
    0x81d00189549503008041d0381d401d01c0c240c40d0144236900280000e03401031140c2000140210b800040b500042c880c161078800f4084104c804100500c400c00d4800c80440c001400b0010010344544130000b5058410b03840811351000034680c640c9080401082080602d0400280031071480c1c0183c21184144820f11304201c0d19510600c0c514035103054482c0c002d4205a00c00260300c00507141d0205126100c017080c5034040c441481d85d000b202070746c0c015a000740c448405100d04011010007018005694420026180810510b0140310000c4810a610040845e51584441811981d05204403030140104607449030900e025515495560030f651140c8a16408180c10418404c5007261541c60f1428220095542e032031a0260b00ca002502540c40f0318510307401550303525500c034034001c642102614480307006100c1c107400300810000035104518003914009c910340700100124405205041c01c0288070402070510502e807214281c01c4410380b00c01e0310200300c102c8505000191002c20740210340c2d68082c90110800c40 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 277180773 1250 277179523 277179569
    0x5060f0f0c0f061b09132406020106060503220507320a0501081506090a081f020c0706030e19140d0f05090603040c08010609020d05010b0c07 62
    0x41041009208548007003101e50140c03100080340310b160500c1c04141c40c0340340c440240c4600202c150080448400c40300303109228450804040c048031500c4020008034004104030801c0c59144c8102503e8805604010400d2118540900a100084c20f403458154a9460b041800c403661039041c0203c80d040c200442d581006021081040e80050000340e082c1070000d880001c1c0d01c0c01d055140201e049414140001c081d04c4501d0509200c0302181e0040c5c44c0c110702580d9815010300e040c940c4041c200c0d40720b00c05000fa0b0406803610405100039010981c000c01440360705240c05a2003003800c1c04048c6045004005030900c01c80007044070822220581008030b002641e081d480e504107404020306410b00a651036402050104000030159200300e410705407441c0c580a803004036000a440000369001c0340080141c0185801d0420003103501c18080c00399450550703210401a030035500b40d50700c03080380e0070303008140c903031042e10640315941c010f0007001000c915084d2035961441d02d03106140f10355203400c012001070481c912 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 277182023 1250 277180773 277180777
    0xc02010902130204050420070b040501090f0305030f0901060605180f120d11010e0a23070806010609060216120c0e040506071101140c090a0b120615030103080405060f 73
    0x3590040c00505504003001a25000350460300c81c032440385082030001c014035100302440c0743c002c0e004a0000791400171030340c03110351030074034040e004031101e40d039401c1d200022a01b01d549a00500e446036403030302e1380c13410032280c0c510b900d190141c4102d020342d00d08002000a5a0003000b103494a0480d1020740c000501500001a229812034180581145008070610203010002c40c410307940c86025110000c11005c005071050032184d2000c845c4072145d11946c0d800e004201e03807418034dd04194040c2800008072503440e11490034200707158010b940c181d00840041c402d103500103d028000d42114801071843c01c0b40341d07141481503a064420079690120403100b06080c09540000c0f07034060810000140c4003410285092603480900312a10030003d20103a00300e00d441d15040c02144080180c00380c41c110305464081e01c03d0a00d41c481d0700140e60050069400080c8990780034090300380310641810414181c40c10758240841003520611800648000300010310020740c0110a49007075032400c0d1084e81d01e500420000964038 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 277183273 1250 277182023 277182041
    0x906030e030c0601090e07060807080112020f030a0c0623040b0c01020c03070305040306050109140a05180a0c0312021c03020c07030c0e04060f02130506090402040e0702070e0f010b0d0c0201 83
    0x1c1c3c0242c1001244402c042c0d041450010801d00454180070b9540104035440c030415500180001d103104010401c2c090074140d40121180001d080040703004010b0b000a02d09444001c08984880c1481400c000c920703000b51050b0603120855080001240707059a8010032880b8501510990000220302401844425410344038401c00000880b5a240d5080c1805840c0e5046484100c400904000c00030482041030700403050904000340804040d515143d070404041c2100510042c03120002401000c81c06c04204002010640500c07001d0295509609102040314180e500d041c1c155030090041d1018a042040d410302030503882d140c0107854041c801c604a0500342280e2001d00804048040420b4244248543c680940c2c0300b000c3c10000f040081c0651000ea0150514107510001640c03810010307403c215004061501000b8001490191107006241d440107068417901c3c0141d12940040c00510306114449800000031201040785615011890b10b0700d11030034000c80002601c0c1d401840b0100e00035040350b01c0e2 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 277184523 1250 277183273 277183297
    0x6172a03071d01050402131206140c0a02060f0906011a04030b0420150405040c09090603240203130f061b0e0114030609011202030f15250906030e03 65
    0x1849a40394902030400148509120542c0c580c040000f8a518140c8201ca007070b030241c03515001c0c80c075161045009003990208070580755262110f0b080da83e0a04c81103a854810002e03a0802074860245002c004c1c54180020b0039038a0084400080c84261100001c14904460242810900600c403850004540d40280e50004000821400500041120780c039610a2006210a440c02030104403c042041040c10007034100442e2078104001d01c802d06094002c041d00f64890b08004003902d5450320f03007074125680382e803003981d4080c2d009011841842202c0c40e90490942030400c150304500348424400520031600038010580340d0240703801401c0081640000d140d0000c20316150060500150b0b0142001407000d07445400910f10080045040040c10203031b03400b5000103086110b8580c28105080d241c44800301003a6410700c5000c254040d0000100104050014030700503c10700d50030040000084018440400d40c008550320454402e0b150307012020600711203d034500030800c1c0710400210ba05503c103031b24280c00 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 277185773 1250 277184523 277184533
    0xf01050705060408090f09100e060d020a080c041104030804120213050f010608011707172a040605060406120515030d0509101403070c0303020d020307080a06172a03 72
    0x10030b0000d10b0307005c0c02c00a8400d40300d8920b1000c140b4100560740c1c0b400c440c041ca402c1e5030680107000c102942102150300c00c802800400043d0304580006140c0300745035010350341d2a071054030000010700f40ba0142089038800403c00394109030965503407885501803030003851349031403c00c4c000100755681d41e02908030a588102e810800e0f820a68201c8000b82c40c00d0040c980402c804c1400001d40364090609441480c100c2c4019082160030090207030908a6940b1400f00ca92056800481d041d440c2c0c200c40b4000c0302e5241a01241d0b00040c841881b00341d50203980071500c509000e200803c00381e90405e414030008089940000f426942d003210141b601404980560f815102d00c04041000c9504080100310102080300d40c1140c201c0b00d150300b00c0f04100b149a6017600c460003880424541405004020171040c07281c2009810902039660340c2c41283c1040b900340f00000c2208041c850f00b00118412140580380c200303140184190510940c41c1e4543c06d140303080001680b110704520000d41010110380c403010000342629 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 277187023 1250 277185773 277185781
    0x71209090501030b040201080705090307061805060310080c19060f120f02120a020403020f010c03020304080d1218080306121c080403020f0105040f0204020309030d0501030303020406030621020f0105070506 90
    0x44d0b44042110200c0c007003540480429003560150043d20f5003410001c0080010608114003102d181c5407a000d400c4c19514404804a0f03039981e0080550300c22090707201d000c06110300d44011035103032a6600943d6401a00929880b00003000030006c064240c070514103002c841c80301c81080407111a012024508912441c010b40309800b0303e0f081d0024030940501c00c1144200c4c0d01c9685c682e0040741716500c03000354002d00708400b010b82940204100d03526107000b0300640c0d052035070b20486c180c2011000018a4000342d409003206102070464406c2c0840420700c42110940c0455070741d2040084c1c030000e410203200c2c25010341c030720400190400115440340d800012002c41c60b50a044054820401500c04802600070325031212002001446014822500210b64450044031074007480004d6101501800860004024030489461203000b0107000318400c0c1d90050740c892031701c50001d04440840e00441843c8403031a07013441b891101a01510b4800d07804a030400c90407a98580141c0320307071203148401445805500204 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 277188273 1250 277187023 277187033
    0x90f330e19150f091404110d1b0e0c03040b010b09030309180f0105031204030209060406050405130b15061c06080a110f0f0319050f0a061d030f07120909050103 70
    0x80080f80c1d80d01080207140743d01c80040e40180d50403c000b0400000385500083c020a00140c101c0002901c05081001c40308541c2d192141192107201042e4180e00340300d4410040316031000060380d882820501c5450035410159070346240b9480610410804030004210301000740c0d01841290860540200100580e0403012000b10301001d00310741007203041000400008060a02181c290241c0300042811480e150442c0d080040f03414010300402e0300160381d8140810a034803071b0305c20903015069401c080741c1d0700c403000c1c82c052215000041400151903c840214041900c8100c01d503482004044614030510440000c410300621a0307500114044c400c0402c01014490380d0441c0401002c4207484105240100d402403040030b0060701d0f94940c2550040c040050a0302c0f01c500c02907a441e01ca9004d681c501e040c60700616103401c0482c4002c1c0d915550b60309002094244a88045d40c0c10400039010b10300f8032480c022605560b01401300c000d440405101c0c0c04001103486178480700007400c1017070000c101e107586074200 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 277189523 1250 277188273 277188311
    0x2609071e08160303230d05090102070b07020f07180e060f0a0c03060605090405061f02010b04051302060906070606080303160318020603061009090f330e19 68
    0x1820060300400c291507800d000c08010341e070183c94158859050030721940000250012102c85da0341103440c0103226100e90080307240a200d02840142c1c0c00541c983c2d4490400034003101e00a04880e00395840080785140803480403400341c3c212800481010b4102029547c01c2c1c000c1c2001801c900d00c5402900104640d0060181045001c0c010191040140503142d101c240c0c00c0303030520f020301c8002c5074061040a010340b0700754101681c0100d0103402403100c02c14801000d05402002088407015075100e90240c200c0342401d228482d88850710341900e00d84034540c0d80100d070041c898604002e000e1803000070268144441500b01c54018030301042166668a40750144c01500a05c002c5201c0020b400d08001180720301c481c08288140a40061440d4a15200d40d41007040300010360070034005101030352100040c1b02d0420704c5200301501c0c500ca40456143e00a5003440c00004252890b5030056441402c481880c854001c0c0b800140c0782c0311304000140c2c6c0ca604060a0108100c03840313184009003081c0124407640c00c5505 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 277190773 1250 277189523 277189529
    0xb0d050d02060f090712020607170a1805150a09080d0203130b1201090f0b060d02070506010f120b0604110a02011505120a080310120f0506072609071e 66
    0x402d80303259896000b00000c0c0020306403900c41455112403814850981e0000000e12802d20003400e0030314149059880804402591056040c040c4010400038a0a03401c12070748058148295102c15840c0c1c181310000d001141c09042c0c1c05440200881c91076082c030300aa0b0f070003000d03010046c00c681c00a14026002583e03640550817650b1315998035500024011030010558180da1010010641161300b429000401408070a56030001a0b8a8800021090b01c2d140010300d02c1700c010000c003603500c02c03050070980d1800034181c0c01241c0382c02c0388a504000b2023404480452103168031081143e500e4880200080c05070450b12680c05251600007080021590158483d1540580f141c0d12910260343d00d80810078490b4a01d552101e940d0020010403001814910043d130740460f09c3c800c029440d6880f6400c1d003090389803104040f102403003160002c1041c8a81040b807940e002100d86000d00b0074801c11203601c1c18103515444642240311031080803e520203404d00c46c1702c01401180012400404404240c1801c5030610700c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 277192023 1250 277190773 277190777
    0x70809030c0a0303020c0d050124030515090d0804020409060204091407021603060e15010b0403050105011203270806070c0309050303040326070203160e060f21010b0d050d 75
    0xc1510090508001c01c2d0102c81c1c154014003148842c00090060022501074100e440f035689100040d88283e0040780003841b00c8070038103c022070034210301d45289040d001c13140d0100b0040010082000410780080c14980741e4645280000558899101140290030349a00040c2014000f24010882c035040d40e10000401c3c280042d901841d44500034180d0302d0340169801d52401d0f4041c10003d1001c01c5503904000784503c406022509440114400c0c40401c1c1000c2c1c2141c00504030010b001c006101d0240a402d01400d002c1c05800251519542e01900b007a401420b003220071030003046007500161301c40e00302c00000d05128041c1c85413460488001002c880d045502207020030b040400110340707400c002041c0c9041d42c0d03001d50f00440c0f01180c06120801e0300b44060030609030580802c50100161030074825289122200d900005100d401c01c211808040c03802004203010341030040c440d072242e5841ca83c14000024400c131080128580000c01c0d1350140c043d00080c03540101ea15180c8400300300000404000c890030035 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 277193273 1250 277192023 277192033
    0x807050d2a12110a02181602030405101110090c1d0103020303030703150f06050d06350106030c0b0306010f021903081801091a0703090201120506010e0607080903 71
    0x2504580d02400c0e204103000d4860560303100d0001c803080c041c280e192041c0f2010001c580000103903a0004200f0902d40100d0451450244280107a140c1c0240b03030460380c92406c2c0040c504160902003c6503418000720b030310700100250b8206142c108101848070a4a100c10f9420511200d40340b801d01b00030f090413620540c40300110000c440d082100724100105e06a80e40180a1865a00c1d060740480c06006202d20000003c03618420024112102114140051070b2980300e554850092410700c8045075116813002c1c0700b01d00c0324840140c5418069030030310030780301042c1c00c50b1550117100710480d03004004a4100500d071101c5144082252810031028500c41c0809a076442c40800744000226120071540c1d00700e084840c2d004c1c404a000a00958140c1d51009103000240300c0d0707030701d014491030a4800c42902900c0b20b08010002030141c090000109622000b01d08050004040c681d000811a4006001d2111101d0317556000c180b55a00c18014400440d0000b0081e6071541064200b01f0080d42c1701d07505080c420b1060b = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 277194523 1250 277193273 277193327
    0x906150d060f080d02030f0708040f0905060f090f06010305040302011e0902040606030c0c060504031e0f020622031d06071a1005100813060e010606020f1b0d0807050d 73
    0x4009143d06913201d199000d1410406405080001a0030001d0308445d480c1052101043e4008030703c2000d0000c00d000003011030380342403120034000704e140e48510640c01400210300300800e00c10f44d07040345030304244280380c001055900c50408074010206502c1040d540c2c0c80880d01c00c08408101d0308080607032402101c1c10403034551b03211002d8048920424415000c5a18498001c2c0810490b502c200da00500a00300301c6003500e2180342e407010b11004801070f4800b25096a80400d02158104031032540b008a141c2e9401d640c00784048081202134200000404000c41290f0f40d84141c008030fa91030110b0300014248a8542e0450b00e070031280034003c9031200b80000e031090000340404004010b510200c80c0b02030010300d0200d1310248210f078810300050040e0021b043d011001c400045181c4600000c3c0c5100d4000040c0c4241011002410b20800070312001280c0d00143c2555041800000700f000c190a04454181443d00c4d03e01c0c0c00301990042d008081d10f18003401842030319142d0041da003032900010604580c909200 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 277195773 1250 277194523 277194539
    0x6180e01050709031205041d19050f13030c0c030b16030b060906030705130e06040b0d021309050f0102040602010219030207110405130803090c040510140906150d060f 73
    0x1030200c0b0b00100041100b10100701060440310044101c4400c0e242c0305140c2610743c203000004030b0001c1100142c034800308007080051411403c403001108200d80d13061105003401c0c2c0d01e181c0b03d100c0241032001501c0c42c40201004160041d0b06001c40385a104428142142c1c1e40e0600180c0c100c1d084400340c036400c4201c4140b0340c4d100d00c644522544800000c0c080d60800c00c082c02400516040103001000380b00040140d00718100034900d042d001045424810a024078014003808244d803000c94030640030309a00c0213580016510510488020007880c00c00140095050400900c1c141403100b4000055100050100d48940e040d00281000c12480340100480030000c007040b8100c1c402ca01000c0c2162031840c01000d000c1c64150801500301e2950081c100501c80c490301d40840603401568010401c0e0700c5050444664245401000d0b4812524455148035501e0040d180d10710301c0c4803c1010b4861800d08001480d55a1122a44003220203201034054440780c08a840d0801407d9500a40200f807010040c000352401c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 277197023 1250 277195773 277195781
    0x7090602070e0c031012050a05010f0207030e060c1c080405070b0903100c050d020f130608010f03060b0d060623090c1b07030812250c030e010e0406180e01 68
    0x10b400800d90700e04660300d0422083c0746810203000200440c501c0000000d05d441040c11781c00d0228004c801030420a203491405d1400c40d40e500800803c003030f006000c03880109030840780300702c40030b00b042d540141e2342c80c0442c195600349640e110250002542c41281000c03019132141c40184980e1003603088405031500c1e155946c10074000c2c0d01580f80c0c180d101400001640782903800c088050b0311182070882c14070310a000074400341d030000400e014074041c0c04030b041840103250501c040300400950901201d254180319218078034411600000d841ca603101c402d0341003030762a900e0201800f560003800810015444103c501210005407076500c220050300c0402e18891714044103480c1c0102d504400c144c0c87c100002030001160b00500e04140c10b103024520000000c41d00d001b00800c0340301c044003c0e88560345000c0c1e4002080b003c440c003001102c07400401045c075586402480600c03006803d4208803400415540040b10f0785002c0e690f0b2207820508050380050200309248508100b030440180c14032408080031901402c031 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 277198273 1250 277197023 277197029
    0x415082a030a02090a09020a030503160308100515070f1a0402030f0114060d02030c09010f150306080c13021605072c0402010818070e010614070c0302011209020a0b030709060207 78
    0x41c4c22030010501080b05c56105054040c03001d41031104d80c9075683c03140d60940c1c01c20741038084000c051000b1001010b50003030300540d201d2801410000da49060101140e441d850f001d242e0001071000080316028400914050640e40d5400020304401303100d602c14202e07036034500b90750486c003e1040070007044244c0418082d43d10910824058074080f03542c0c0000701324a860b07801c4010b0307825002c1d4100c0340030b25899040d13119019144444485040d1490100e807415140704517410001018a0100180014403001c43c0d000c03000003040312010015085200d81c440244a00d8168551803819666480100000403a214080f6904010359000840d0380c0d001c00150400348011030050007581000080056020303040d8150440452900d9101d5003c0d540d0b030302c3c0d10303010035608441c200301d4040e0010802c4a41c414102c62000700180c01c070a0802d42e41d56110180305006020003411b1010300409220310308103039480515000d40007003a400640ea0342d411410f40542c410b1322a44001050040c0205041e80001039000032 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 277199523 1250 277198273 277198279
    0xc181b02031e03070c06020705010905120406090e0a0204180e0705180c180d1a0c04140411090d06091703060303040918060c050a03050106020f0c0415082a030a02 71
    0x8080d482c600b081da0958401800c0b40c0a000620795100081151072014104a42c421800010a0005070420328035007000440340e440d01c5001040140312040d8054000411900c10301400c07401c0ea120140214080c1c000c0e500903a02c100c00c128800340c00b1400310340100c1043c034400802c0c1c45045031580d062140409581402410407a00742d000710307521413840b0005004044020401c044846d20010001d1080304000005440341d0641d5084072501c5805070701b1042d00912000781c6a45810b141c4844e0b00d81c9100c005003100e00c02c0e40d03603951511112401d54201c5a1080c00200b000d40c12035010700e01031b00140b0700710340c0c180c40202101005001513507030fa0f003c403801560000c00540c1000d1030003010300081e22540303203039280480003c02c4900004d010381c0913420610b5019200d03141c450040500080c21108141c1c40141158071162050a2040c0d021032043c546a0058802044007803034a0925141d09285030301c070240701d10039424200c150041680e01822240300001fa11039102a0810070190344120a41c0c0181d4 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 277200773 1250 277199523 277199557
    0x705040501051e130f12030c0b0402030a21081003030c15020904020f0a0813021f0c1b23030601050f040b09010b03190e060a05040c181b0203 62
    0x1080d90700803805000303884424411920f03402e00750074040b80f20750440664002840705041003440a1400e480300341e8040e120421a18090709401e440052a024500720040c00100b125800f0078103546060105841e055000b280c3c00c0c2d0302000b00d40d450b00030490106402c0f000135080e180403503d4880c00101c1c040450b40c0640d980300c10114075450f9008200c110b100034500860b0308220030400c07030303d481c000781c11185242c1041540700c81c00d60001520912000f082000903802c00e480000c010380d40e554100c02070500d107100a03e08502c0a120540f02c11a01c2000076020f05480300000c0c42d2554105500c2095480e54540c0405d0700380400100a5001c508240581c1d0580041c4014021420054881c040c00e100003040410f0301400100801c8910000303070010100010700100f0402d0790f0790100b0007041d4540c2c80f40001c101d850048648207480c0c000c0580601e800c1c40c2c5883c003160034012242652000b600381c1180d0000310ba007010403903030020b12040d400c00b007005020b43c1c0010543c50022085e0703145401c010441c01 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 277202023 1250 277200773 277200779
    0x90b090405030d0c020307060f0203040c0902070506160e0901121202060106170c04230103051501050904020c0319120615020307060e07150503060a0e060117060d0b1f0509070504 78
    0x540a010028541011441b050050002040075801405d0508081da0001a41d83c10181060000b40c003c580001c83c0300c0e40101b00d1140010400547c0315070011101c3d14a88407071040c002c2c111240c0201c00301450740302452000118a041404c070b48059041d22030304000254090f50724060b40c40e24000d101e640301103400201200140710682c00d861b90702003041d201092a15466007503040c01c2040780e107400702c07690481800039445560980300ea242c11601060128241400d4140000d140d84130300c2024500603900420822410b81c2c0410627130710000c048881c0140c40d604604d2008101340c0540042101090070010001194030f001c0040c0118151654003a6160290a44608002d452010a4281e040c130030880300042c01044500340307620991156507920b0344c9050500400c011500150011007140324032205220103a80c000b125510b84424201712464581d650b0000035082490140b0060035000800003045210690354003482402e04802d05050030507500c9030280025034130b00300c03010008103904100c03c2c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 277203273 1250 277202023 277202047
    0x40e0105043305040911040f0b060406051305030307030c0506060405041721070905040b04020307020601050108340f08190f06120606030c08010506060f0a021005070207090b09040503 80
    0x41000ca254400d80d00d0031190f5542c0c04201219801601690103100c3ca2113024020310b06800b8003001d03040c00300341c24001c696080c0300007030b0103129034072400042c808000740e42c008110502000c02c00a11006054a0b110f060504010b00001c414982c01c540c6070003180c0025406242610800d80181c0d044240541020ba00100c03040356603100c44000e03404486038a10050318502c180c0c040fa0710071490b03a41c035004064940700c284010307502c01038441d500c035500510400c05082d50004102d411a8001d182800d295150b80104a18264006420100300c0d10602007040800401d80c821940380201369585604076184076034100e4074104141d400701154942002001502c00c200d03000a4425080d5050025100340c1c0c4280c500d100d03112641003281d03001c1c3c88180070000c1c440103a8190004240d460002c0c401883c201c40068400e09c00c010070b01c1f080820125840803514400c020316035040036035610801c1141401c2402a5541e07010b03200310f580c000e04004101c003140c10075816550080364408010b50a07c0e60501e00 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 277204523 1250 277203273 277203341
    0x109020c03070f030207060e0a0e06061303080d0204060905030102031312090806010e180601080a031805040c030b030c1e040b180109020301061803050d080402031f02040e010504 78
    0x200c5641031205002d07600108148203802107416110360000e040813403506201a0180764501001442076a031440c040010b17415009080e640224100c80c0180c0c0e86040140400400425820142010348045421051004a41e000388203580c031a860324075079a075641003098242d2108881c02030102c08403001a800107160140d03c01d62aa4003800c142d4510340e202c82180e4a407031002d0340b06200308041141803140c100c0b100c01d402504814440090301d000d6050510082da2116a000c008007041012034003001030108841004000e810018028895480c0080b001405424402c401c1c0b0f21038007030440190981e281000304140d019158600c8041500303010b0342004014214007104542000c8610340c048040c588030368010307004e014180c600584a504101008013500d030f0400349810700106985060001c2400050800c11642c01e80ca881c402680e141c0c80441c1c140310010100540462818006000d0001c89401030001c0d1540023110003404d0b070340c0d441008159032102a074151203010002400700548500d03a0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 277205773 1250 277204523 277204537
    0xb360c03010e060406081b04060b0a020601450f05070806030d08010f0b0904090b070c060c17040b15090115030e060c030402060706111207020c0a180e010609090305130609030b010902 80
    0x700050090344e508ad543d84c40d50140b60f060300140c001c0c2005101688108144c51602922005d00c00040419100c0012a0003103e5500d458003046014044200d4059034114024015005105120509014402903c11007040d00e000d071090040d2516022502d2141c00780d141264000400b11043d0751074202403035010b5108009103a049074890080ca000300d888490444e008195565440158000c13505045e02111030f801e0500041007070000550b0411020089210742140d0051801407858840c4850308025400d1800801d810410700300000401d00111010040300702c1c11a00e0a20411050002c400d40b6541c00f1646d8800b510018408900581010030107018114491080003481d940750580440e003030b400c07079610b07030410040c440100b010a690511100c041c003202500c801c1d030070a0a15600e50148841d80f03000000da80e40e550103207110101d0940026008144e03480c4108241c10203810b00400c00e500403010314003c1d00004c500021a240b00300710b14402c0f40d03081102010640d003000454400b030f50000c0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 277207023 1250 277205773 277205779
    0x31116060f0e1207030209100e01050402030c0c0a14150c0304260d0506040b0603071e18030501091428030306030212070e09010b360c03010e060406081b 67
    0x800b59125220003482a5582c255103000b0881c0614620402513107403001418400d2109425401304112413100d000c090541e10100c40140e102d036101440203025004804414483d40710304074404041c081c0058014100011001c00d03910195015060405414401d461601007a034082001402040ca102078114076400c82d9403000380d1405840841760159000100d80d94016591501440014a018070610700001000e458050640c50401d034054411208004c1a104e81c003201d421154400d40300b0003071075800040d4064485107541c8c9034101640200a0480200e0b1040041c0c441c41c0c0c0c000c80009081e040c418685d07403e8460aa40907030501101d044480d904405054030751101200580d1080034104d05522030000a00f00076107058505822241c01030f151401e41d0740f50a03a0300455448054214104030f103041c1c0105070880c0ca0000750f4200100e01d00340c502ca0b4800000a003c0c8881c1c1420045041314a40186a0301585400007007000f20390315445035444036030100c401c4a411119000d001d520680000b = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 277208273 1250 277207023 277207037
    0x216170c120a02010c09350304140306010503010513260a050703080601050a0c170904050f0405120f0706051911041e03020306010b030c07051009031116060f 69
    0x3280062401c00c038009140000c2401140090701540e091241c0f50714403a2600d84201c28a2401c143c1080380040c42030940505500c4840b440c00451780c06c08141e100e031151328102d03996981c0c0c42c203038500c91041c0c0038800f074444d014003000000d0b140707014000c1380e0041d101c190020f41102c00503601c24140e5004405006079000c000e2451040442c031a9010300f0541c949500c405545110501c0d00801c0c400c00240705505014041c040000c040d64000e082c41001c941c024418401100b050003180c03002c0c010300004590041c00d09007001840d80742622050301442c441e004688010300d17000c0303405050b4050f4075107132001480305120314408a1f43c0d6070000c5803c010b40c201580c202c4510b9150207400d81d20069450040721728001001c100d03140c4500362909040402480ca00c801c030b411580080c1e10740006201c3c43d9608900840480c21005c0301d081104c1115501604680341800c0c40d03c015405456140b1003900410001010f4014203140403d00071480313041701c540d82c0003590800c3c205407540114000c04104000d82 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 277209523 1250 277208273 277208287
    0x7080c06220e0402010314071202090307050301020412051504120e0d051203090f01020c0d0c03120e0c0906010302160b070c050a05060f0c0f070f3f03021617 69
    0x8001c501c03030090551804810003500d000d0002605031101c8045002801c0c1d290300c100454141c1c051842c203040300da001809aa00c251900c0000d02c0d00c0070301d80bc4903615502c00500003500100ea00c9070308480364070503410344981c0021082801c131400d60855015040c08220302c00ca01d1003074845c002344407580e82e00500c403900c6400d864070b0b810300e4110030804803062000000140309a10341c041040084031441a0000d61426401141c02d07070311540d52803001410f00400c1c0488404042c042c0710756404c103103555601045204144010580e03140b800010783d50042406001062340c651190080300c02140d49001c10303444070000e030340c1d80f81917800001780100c0400c19040032981c0010f005102e80c0b102c6a0242004102500385241410200640071b0b0090142690410481200500841c190f520741504900903462141a40c00e100d9103642500b40042c0005d8a654180b06900403178900040c804d0810030080d246a40d040c410940403441051076141040c8401444800001c80c000000f0310303100d2030301400e1401c01c86 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 277210773 1250 277209523 277209577
    0xa0305030f0c190f0e030a03020a020d03050903030325090e040f140d030b1e220f1118010801050607081c05091b010507080f16080f07110307080c06 65
    0x3442d80d4100000e84c1c0001021102588054030803001c040c110050040351002e99030203035844011030002402420488814402d050089060f03c0c100080039050760350342d00d80485545082c3c01c4c46e410031103800070214040c003d2035100e02c2185068907000310746c425007601c482e1208803624070b0040c0215458540c500d40c07a04c070035900303003d800c1c02c41c0625107000c180740d000c000c10454003884201103900f001611000418403075075000208680b03088004610100220a10024800b030b0003100c2900c0c42c41410110201c212640b504d0060408030b40b400c548071000403500004540041c002e10800d94404018400f100118401070028010b03040030401000b1502c1141030a038081e654111000c0c481c40e00291200e080110381c801c0315440409091800f1441d110050360707204624007607410b502d0f5140030080b030005054486621404041c075044079a180c1c454102d111140740303650120078100c03000054401c10700c03090b060014481040e82c000101030300c01c0310480810b110458000c052030750240301c148510550030003 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 277212023 1250 277210773 277210807
    0x61210060f18120c080d0c02090f0402032d061006020c401d0f01140f070c05070f061206080303010b2506051602031303080f04090204090506030f0a0305030f0c 70
    0x45a1920681c87c0c11600400041c00c0c40100b546240c05030003010080140e801248100704120666a00b0b030364070505480c80f0204145895585511b03108440500c212000711007248011516150f0031202c1c060011414032240048131030300070740e05208070317804120310950001520401c03881000d405242c0a22010840c0240c0c0c10301c0301c0443c0511540c1941701121134040c000250070003910b9009000383c2050494401c0c2004005080c0d00540c1c9a450209180d54401c0d0003040120790084111544c80391554004036119801d84584004a42e003502c0328005401c00e8020601241d00740d8000e1429a0306c0d10000850075840034240e01c0a81c0c030008240300e81e041112040b554001d0189800050750320b045004030800840d003a11590941d44140000c50b1508440190103094a034402035694403841c03441303a0b00c880b82c004d40d001303408440e00104000c10b00200075170181c0d1040c081201180e420000322205070f07491312202c80002e40001c00c1000043c00403100c0e0002c49401c201d844909030310304218524005010 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 277213273 1250 277212023 277212043
    0xf050d02161505010e13081312050d03150b0304140a0203030f0d0605011713050f0322050402040f1413020d020a120606120b061210060f18120c08 64
    0x28a40941000c2180c042e449101c2c0503000c00701d08006682001719184100410209004122000c0080c4c0000d2445040903424000c01e006202583c2c46d00161500c0e03612078103e403014100107494111b44210b69407443c0503950454410071015480d68903103840d001403251603014841d4007440b0704405403006032001c000030580700513400710403526507003072440540503074005502290401ca0408400c515020324003907407507005000302c580900d41000f43d02d420b90500450548140300c601011030006a007100040702c0320192164500b41000c401d46440400007240618003a818004480180501049180d02c0b119131038560014042d0410481660485081c0c2e442614803110301d64020855000300368025029847d010080c03034040c469a0300340744004160321500d1540000b1541c960480401503140d4000712401201611074410191801c00c60001c0070520b603200c1c0500003806140440c0c03002e485191501055480b80c14012810b07803508803617202422006a00340e0710190140c07400580060104922506 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 277214523 1250 277213273 277213283
    0x1050d0605041115030a0b0102030901050a0807210b030c15070b0c040f060e0306070e03030316050d09060c1b0f030c15051807080a0510150b1c0b100f050d0216 70
    0x640d2401c6c5200c4000d450001100605550042c440040d15a030010291202054a850400348681d22110211912480c15841a20220111450040d16420754004c02e48801040e400c031283c075440d078000c1c406080702281600035540d400b484803030001012054042d821540d0032258a0506803900304000768201c04d0b9101c100800c0212048110750700301400440c1d8020f01d5070818005061080300400e480c0d200c0100614210048403480c000a07078000c2c01903c0c206e202c0140704010350300142c031301203004040c2025420007103003a9100107103c000c00ea011048441d0390000d800241a002ca17981039a45031046142191a002c2400c041108000c80d0300c14a03214141c1c0203150301e8141440c080c03683c10107596400c020000d421074003204001c6080041c00c003448484018000031202c41d51400400e41040700c2d0460580c1d85030002d400c040f86021924402c4c0f880e03000d03050070003c0c44203410812040d610342050034000700d204460124030150041c1c0141550f207007820405468060b00b21080c55600000c0e100883d1 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 277215773 1250 277214523 277214527
    0x12030c1803390d02030604030f0306080307080405240a030504020f041a010e10200c22050109090f1b080708060103050f0601061227030507120801050d0605041115 71
    0x1011406190242c0000016107a1107036030b01440c0c0110752181c9000308041d00784104081080456482540810000c104c2c5100f1f1b2a00c2c2c007464036240c60300740d01ca4811144030b030442e031340b132240440141e039044030a001c04c54074424a401d40314242038016040050051741d015000315801d0142c0c0c1c1300d6010340159080941e102d451000d00d07540001d840180003020341da009031100c100720321000350080316001c41030b02030120f06c0940100b9007421514011030f1585468004080240100000c1021305141501100d03103103050040e41e8035800c0391000c40b05e210340e024083c3c00d00d259181010501e0380007080f90207624802d0b0f59402c651030342c00d02c4c1e00d081d100d030340558055070020004006000c0180100700c2c40c240050054101942f501703000900601c0904446880617659a02c1c1d1000a180c3c02c800d20644641c0c0c0040540c081c8440c20050710315044100c00740c0d28145c4c041d090380600c0c1c1c4600d28142c10303944000c1c0001002d440d40e0300c4030742c01400020011544000c404244000e42ea4503a900340a0030001410469 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 277217023 1250 277215773 277215853
    0x6050a0507110f280f08120604110306060310090501150e0306070816020a1209080c010804150906020c0102070b2703030106030203151306050312030c1803 68
    0x100602040b080721a110b400100c0390095040b000b2800e480d0041d610020b05040403940a044110480c1c0400014030304c03800300d07120341d00700a08103020f4441d0b504142e2035582659101d01c140300a44000c115050f680300800c00000b01c55203001d5010316080420002c140242d140c55483c030204481c402c1c7c00c500781c1c4299400c5c1e2101242d9111465900e1000c0c20b8016210604100e20301030200c0c0009403002130840342c0307100b800d4007081c420444414038a42185c00703401c107118140406411480e0500410600d0300a00620080325402400341d40e004903409034686c110010b481040c400200700808013242c07615002c100d0130510304004d002030180c40b400348007101c7c2d40782000c650305403070020315a00c528200000d14040300005803001c0b090300d04482d40c5003400744c2d0f655120240e8058410041035800c0d40b0401204005e20280303007035803290040d6142901114454882e0302d8680000340011144950f411208000c0e8114503244503075400c011850140c1110080640800c0f505680006000300300404500c0040702 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 277218273 1250 277217023 277217027
    0xc0910080a0b0a0807052205070309213002030f011d0112030c0201030207050105040506010f06052802070302030607030e0d0e03032215020a06060e13170706050a0507 73
    0x110002d0007003290400b20300c6140c40b12081c0c94103076501c1864450b00d40d05a5554844144032000d20101d81e1000013004a407030301c1c000180060061842c10394450f02e980528140002c0010510134a015039500c40001195070002c1844001040d488052640d02000d0303500c0850352861b001460190360044000d182941c148a0290319440c880e440701368200c4503400042203540b03e8584e828940b05d8040c81c04a201c0703036950005a000c0d1180d060b0003400c2d5880d0008101c00d2080c0405c85505039040c3e01c8105003c2555100100c5180c002c12044411403481001150403940e515444407800510600507034843d10f40ea500003a003000300403940303100844e880d00f914018890040c42652800d403198205610615500404a5905d020f56000c0e40d20500040c40102440c08040195000802103803185109032171030500000d485046400084030402d04103480400c0300c02099240520a44551141c041d142d100d5071181d16150964400041620b01c0401c01940458424051144100391529010855050007100 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 277219523 1250 277218273 277218281
    0x60f0c060702030a05070f030c080d0b03010e0c0109121401110d061509090f0609020a02010911091e0a0f051e0f04020f041e02070c030b010b0304080307080c0910080a 73
    0x11400c110b400400082001c1600181607648441e000547c581a4042034641600c840400c850090f020020100c1c01c58200c1200b6046004013801c1a0000c0c00303094100301c4940d40c0e5607451410b01c2d0200c2e0004205000308400e06401140941c05840f42c0f401c0c03100c03068103c5003181d80400480c4880f03540001d9070303174280659006400043c403041d40c124042c00200c410041c03c0964900400c4411502c900051110700c0640d048440075200c0080119618884200060b0082203412003c8a20703048644c0e0f140f01e54604415405c4c810a4224910b5011616001c001c1c490b40748010030319941d070741c2c1d04c000050190049200355441503408103a00070b0700c0b0b0301015a0342c054150040000400441c813404100058641a29000c050324041d03e01003041a010301e0f4014984000310404408a0310209148040c000181e4440040381d01828060341982d032245a600e02c02c1c03004903400751980108002181100d0f21944070703a64010196903070182480740400000350010130b4034ae0100009000d00040c0006c1ca00c0e1481 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 277220773 1250 277219523 277219531
    0x51515090106050c281a0703060905090705151b0d030f0b1f03020918010509060a0608040f0c0b0c0601170106140d0303021e0a08010605070503160c05060f0c06 70
    0x1002420130707200f07944043d550503003d041070b4100c0344012504140e8130112449264250340c88815a40410001404079001040442e001c900080c100200003c0a0a0710712070a80200c5c60701001c1d20f915802c1405002031581041e80410101c2c0c4100400c2103603c41c954051410740c0d00407400351481c0c0749581e400900b07403181010034441c00e0380f0b0081d00110715a260492614090084400c0b50080f2900440940081c0a41d20415820401c01a10355042d1040e004560381a50003c440400c0c46480d4601400414080e80c0a48404110900c0104000c1070034024005c1e005442881c000d500c4644940c283c0082e90850900c2a455034010401402903003150701e031740340688014074020800d040c40c00f00f481c4241c3c06030045050260701240d03890800d051194044a210340c02070700c8044101c01c0c41c0741184001d075101c24404d10010b1106800403600030701c2001143c010b680c01c10000e6091a5605031645c0070865001c5045030f9100d010b07080000c06032a800003070312003000160038141d254400f010302e480c20301034010 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 277222023 1250 277220773 277220777
    0x10060602060609133e040c08100608150a030303021803010c020a06020c030409050123030105060603010e06010c0222051620070803120603010c03050603070b07051515090106 76
    0x110402024038501d114481070250410000c0c1c020940ca0380c00f101ea0303040098007882e241941c101d400b129000c0c5d00160300c581d40d4001d0300d08100310640194110f03044403080d100c0e074070b078030f0108001084180c0c414414281c209201404002459081c040025880920741c1e2045021030b4012510b205000c120145e021403440d000e400901c10880c1d20355009407a00104040104815404508a410606c0c2042590081e0443c0d1500300480c3d41c440840c6010007075407685200301c400c13919035490a9803d040c060f507030080c200034161504603420040f81c40480c4400419150410141d00b4200d40941e45d41755520120300900d0119030542c500780030128060300c038000e0034007201c0c842203000ea01d8030507407000010003480e07034510704a503414100305122030600525510030742640c440400c075260320038035007100107000b418114000c01c40d80c90f1043c811780076501c080700d10a6041e00102030810101d04030500418001c2c2c1700324182c9a070300031702e114980300303e51080d0344403440c2c0509030050001c5401d10349000d03400352000d4 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 277223273 1250 277222023 277222039
    0x100e130201110a0b130609020a08031c14040f03030b09070816030e0604020f1203030403050a08070f0e0f01210507090519050d081902060f060609090115050903100606020606 76
    0x203840311141148017400381d040c00700d0504e00c200b00740140c590101b02141e500400c0ba40c02d059440501d00c1c1c1d00d4000c01c1110000000403003018020700294410100d0305801c5007d005d4482d6156110b40b940c13481441d82c00d805040c4c5801280c0d0b0603654002c00c0321321880c0300b51589440c42c1402100441901d601a02400a241c0b83c42070280410800050f0745a00c140c2c102d80d080807024810004c0340d000c4030841500d440920021080c00101600f22000d801c8a01c0280e860038402e40e0b45650403210340551521100228484240098980c1040c10804040f22018140741100003401c0c40c0000010b101800d801c1002a80d030000c3c800e406900000d0800142022550401002d040c2d803074034041e20b6664850240720b42d01c071310756100401c010201030712100700b41d80100d10583e181012000c0d4460364200d5030141021300003c0010070a02e0b103c0143c800b8608041e00083c0f00303038204210898418980c200b036400b4050280450a80e5560801c0003910a5a21900100340300d031030030343c01a1401e2030280c4503503c83c0c040 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 277224523 1250 277223273 277223293
    0xf0d020102120612070f08010b04050a050601171b0f07060e030a05220506070506060307170a260715060e04110f010309050607020a0b090105010e01050108100e13020111 74
    0x7660543d070040380031510343d42d581040c022414504203603544884841c4c0000d2100203007682d01035204070300c21802035405010655511803800e04841c822991035010580320034a04aa850600c2d00c2c140e80035100c4109000070340820461584550420311a28828480000781881008468094006440720764002981840403082024219001d4204c1d010315041c0054a40106120b030040200024600500081d540307640600b4419121b02e02203031654001d02c04e0f0980001c091003c2606405104079620107086803d550303a888801c0841064038502d40c40341981e040b4680c0308035450041950a2103003615001c031644002030fa0064442c183c3c054504070000100300b00214025042c43c00c83c3d5481140c1000c10148844016001000309400207440d80c41344204101c0314640008255100740d024484901855403400802e80c2070319001d0003455851041040104010350007900c42c50b401240c0408002c01003500c5482d03441040c001166205440903407000c0e880e0665802015016150880001030442211 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 277225773 1250 277224523 277224547
    0x3010e0103032106060302030114010c0818030a020a081c0509061b01090605090d09080c0303121b071b150f0513030203011109030c010906020a0201081801020c0f0d020102 75
    0x190510000c0c0c240604107a15004149511080840c003000000c0100b040c5a102c1c80c00600a4009000c1c0c1e122880d00780b4052481c5601030903a030500c195000c079440749810740c491503200d410280b10310550713054460801c6010060340c03003072240000b4100d8000240502740e05180d00c880c0c1c12254088040501008000d0003450f500c0300d100700e0b03510203081004201803e40088000740100305107030000d45045c5c500341c10301040c8180172032403444121130b6550343c01d801ca45820841da203c059001c0d00720351550081151120011543c00f580794007401343c10460482e14083c1260318401c3d405880100c80b00c000885004444011059210000c1c21010494200c0d0407040368001e80b01c1181040754405002000c01c60345044041861001c025580c090000c0c013580002844141071031300b050502904c41c3c046c0210300d0060354402e01c41001214600d60041160300724580056031940f40103051194800f500810b202d21080d001d0008040b9035201318010b11003d40e50640345418081d102d01c4403021039004000711a4520 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 277227023 1250 277225773 277225799
    0xc17010e040b040c050d05150a0204050a05040902030a02060a09030c15050a121e0501031104050603150405030f3c0d1a1c0c1d42010201060801020301 66
    0x240d844400264181c941d820041c01d020a00c5d400b1981c81110300d203d500822001080a110070032004109010649500b04080140d02031405290341210902c0c8081020b4039180c0c0000120a002500b55041d80301c0e25008a820340d40302c074a4010100c1c2c2010010030030402d02d03030796000051030074519040e0400b001c00401040e44c4580c900b194208401c030b00c582400400d10b07920040707241050b200702180c03d10b0981c03200005001e003480241c83c144000000c2d204282440d00503144201c000801130150354032000b01c0c0c0d81344190040c10548042c0702c1400110071207003411b03008280901d40750b0311026081600c0700700500500e4500d4244a11000d540442005200c500750036101e03124604071020a107034001c0f2011400c0d480046856607427000e21000a040396400840c0b5191446014451806220303449007903803042c480314030340418128403c100028140403d00051141415145802001c400701c00d44044480c0800c5480240c40d441c08012004489680920078a4028409131000390f04542c90161240108 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 277228273 1250 277227023 277227031
    0x604020a08060103050717070f02010e0c010c0326011214010902092a040b0405100302090310051510080121021e03030c030c010615020318060f04180c17010e 69
    0x1250b11400440e080303c7c06a0100d0000e80c1c0600c5464051b49000d1100510811a048610b40554640420580030180c04146007048140c10703102e02d1420805030742c04903030320410a00103040c0c110405486d0150303d4041c001060003401c40048003c1c00301d0450904610f59070b6200c5450344603a25089421005071a07030680141d10400c4541c40401c1e01c44400700803071200090008070200c042c030010f40840c043c44500c0107070003610000d99401089004540003035049229490000740d250f030001180c61602441600001c0d803209500c040d00890011010100303266030f030825a1100840e1020b0010f00c2842d01c00741858046c00c070515080b103c1000795070045075042c0902c0789901e100610040762560a5141042164443c59201049030b5451022007113032402400c030343c020388000c43c01c40c1305900041ca200209440f400040f0340c0000781011041c5082140c0b592080107641001c2c40c00b40b00c0001c4048201d111240d07040d00865010441010f41c440051841c542c4614090300034100c8801800140b90194a103030348 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 277229523 1250 277228273 277228277
    0x3030402150306030c130603031713060f020c0a031d180105040903021603030305070e100e0d02041803090e0112080304120c06050408070203060a110702060d0e010606170604020a080601 81
    0x10b00d0319460042410030304080c031913582007100c01c100e81c20540c05a43c01907048902a545144c0e114184511400e0350f600c087d1480e10044204c0840d82010a48941c851407070501d00d100014504010010054101040081c064000c14032094641c0044415000d06640250080312568111034800f003030b81c005a401801203602603a619240001018020052412030203250344048a8003590b0b464010043c0c842100c1c07610018510040d1903c25007084418400000030380d0312800301c00f11340e0106104e42c1c0e8014240599005803a54a414040720035105442c030414000d50314170039101d04010701c0c038600300300682c00300300c607456075101d00004074540200f40d075040f5074000700c011a204c100c41002c0303511a2920390003420003443c11003440204040d080040c5070f458829400c0e11907543d01d28102c00704030b03040c0d200c030300c00d100008000100040c40e0020081041010207580010300c018482030403400c4411940108012031031008600d6031781c0d5a484400c0d41d1100d800c840035440c20145c0307040109044805041141 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 277230773 1250 277229523 277229527
    0x70309060201050709030f0f020405091b060901050a080915090c0108150306060d060b130c110c0306130302030705070905010f080606100503150d0b0618090706050a0210020301032001020303040215 86
    0x8100000340b0783c08c810040d00240309001d141003450516440e048448001d00f00901c0c0c007442146141001c50560f082c810050b11541d061034103011060350500d4000b0001c3c259400b50741381070354a07604400c030130300e00039a4604020800c5107511000503014140141000c81040d05203007181406940c00907009903c107506642440c01100c1034900203000e00300b000e43d556407040d00d11540c0c041d1903540c0d92003800225121f40d500314550400c03607030090b10b03011800c2c01690140c1040000400c41d0903962001c40216110b40704032403800309581c40b010b0601e4007a8200c80b088a44900c01000f500000d400c3c240081e00c84400900800d007001e100145000021000c1c510500c4008800034004440b901a82c1c2035540f406010740d1a094039928100b110400110350943c444c03190300407a440c0d5902030180302840b032a50a0020b0100a080c610141c505030030000100045200d452602826030b11f079030002d03500942c0f05003299042c8090311f460641d0448034003500281150f205200308000360391408007841e0708800002d1016 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 277232023 1250 277230773 277230803
    0xb040b0c16080105040c09051603020f0d05091c050310060c15142401090e040f0218040314120a0c05090d08030603010c0201060303050a0e0a031707030906020105070903 74
    0x341c2800010042440256000c0c4400124190190042803086202c0c80380c0040f42501c4100500495100361100501054850440d604643c06035000380b1042c0e80c1d02c0f000f90305044c4000c240109a0b4801c0740c006c40c454005022801c00916542e104191a480c142400ea08510304014442ca08500c14850302013000406401c60040c000311945a1a042d0b400d14001e000c130b20a01c070080846408283d611050310b440401580001c010442804174078484141e4540c0851071521007128407040c4045d2040d1400d08014040ca00160303180c100031001d072a07505170010250310b4141005410062551441003003501d0802c05681e10704c1003811451b40c40390b80f1100000d500750440704110380c1c03130244012298010510014020601c00204003840c400e0074110000c0c40080c49480c1c0490a8807914400240401c20a001d0754080383c0c0214508000345101800021256a4a855102d11f00039842d00310034a030400095074000f4154440f05000c0600701e24002031095051880000b480c40c1000e1201403d1288040c0c450 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 277233273 1250 277232023 277232047
    0x4020a020d0c080906040305150c0c1002030a020c030a0c0312020306010e0910090e16090c05031b0d1107020f0108040201021f02040b070c060908010c08060f0303070f060e160b040b 79
    0x107074030341400203080c07280c440b47c4a1620070b6030340c42034014a1b61076202c03d800055440c103a803030440b034100c90000054480070001c0c00c4820045c1d0400742c0200380307585d02401110341c0298100080c1242000380ea56640b80a90385041c0075040200d11000718083d103004100b0092241d030052101d08800e034058607408225501c0c8007008080b418a038008200217401d0080d130807030803d4000703050a5501d82c5408200e0004d1354420490085451a2160340c001c124180009840d400c481d03420200344402e80a0010303c1c5c4503801d0f4000702100d900540f4200c1060002c640d480642c24480100e510211081c20000e280d410700390001303544c1340b4141c802102e42845c021044900f50481d501964000c00910b0811a01c551075172401a060381ca00f40108030011f28078600018504205001740f03604c590329611814039545840052080c03d4003000711042d0948400c001e000005a0050504081140070709000160091b141866134209151a08401c44000e1240c07010303c12006810100d0f0229100c400c90390741d0340c0e4056091 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 277234523 1250 277233273 277233277
    0x121a0a020c0f06011503020c07120317010609090b0f130e0309030f07050321090f060715090c08010e120904060509010306091502030702100e01060b04121104020a020d0c08 75
    0x301c10900414250400d07003440012280c2c1610403050754149410700d0003200300d00328012000c0c03e03416540400d10420004e09403080950615010f890444008440f80504064121088c1c0c1300344001443c41000300b14000c001e200d042080c08080711561500d0704c00d040054960050901c400e6440741c1d40e0551883c4d00001001158071284000e4195203900c20040d040645030013051003030b64000e01075050164074041320b20406051710030354558103508102081051102659031201c025400803400c0003200e0205544820a11452240b440e01107000d4143e403402055980746a840030080e40e0404100f54410b070b4002c5013036a050b030607174000e00da212110800000d0191000741e0005421201c6000084240819504400507441c000c0f81d02e1005003d8881443c812488211060300040c1c01c484000c202c6140c198220b0701c81c100c841d1001107862501c450784c2c0f030503139031140e400040c0a8410a800004225a004015181900440f030071801c01e0906600a51540c5880643c102000740001100040180a00c1 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 277235773 1250 277234523 277234537
    0x30705090a0f14210a0c0e0f0f150613081606081b07050a0b09060702070f0b16030314010b0a120603020d0807060f020d091103060408220503011a010801121a0a02 71
    0x10454100b8280d0f4148004400f0060080b090901900e80000741c11040d000d100754012448030020003e0b683d5145030181c40046076190300340d4412010011813400042581e43d0002501c0c4003000b401c410400c04d154100521525800720381404301442c01c201c05482203102918070b51841101c1340f9510016864983d04140240000402c000100c0b401c1c002d03803032030000d1140e10072401c540881300e565803503c02940c40d80940c0c0c424030755100c00811140090101400c0501031043c824200031404680485000ca81d44101349c00111071144045819270704150b11052045500304006c1e002c0192a043d41c0204100a100f500080c1c9484c00001c0d04004102e0366138400c3c0072680300b2550454541140c0c14804000d401041c0054811001a80310b40007949404030f0305a016681c803d040c989807a022131007907696203083c12041403041d0301030311000a42da2020b00402041c0300d0b56040345941d0380d010500140c40c0030410303007007800140011340d0800700203502c4c03540e9140b511002111040c5282c0d61b003212100a032003020 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 277237023 1250 277235773 277235839
    0x308010b0924070309081f090201020f0a140d0509031b0105120c04050901270b240c16060c08070c0306090c15050c03040905041106030705090a0f14 65
    0x42d0240120041e00607001d00f500c01e1307840790511079440c1500f50303940c031a07801000c110650300300d12041d0071001d541c07020f000c8901c1030069030031b032030a401410303414411000401c0c1c603048840d00c2141c800031400c2c00b007115160f1841c00c08034109035a0401196890045201c3e00703101403440412070f1502d80c001c03030950304415410342da890a9850031200240f080d802a10946000b0540b00300045580840c1141c2d00500201c0c41104c00c0c6034040c040e500d00f020300090781c08640c010b403a1042c08400743c400740990f0301c400078806140c1d540d01c0030700922184c94919504c4901d002425280d83c02d02c0174036884215003c40c40d410400c95600c85006040400291409500003171645182051034000c0010701c00681c01211682080c490310115180b505131110b01c154600003159820400c030a0080e1a142d0740840e4020b80109840c400c00b11605022940716401564840003140c40495100d506180110312400940a00148401340d1464940344141001c40305852034403ca4620f480c858400e840c0525500b402c0c2001 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 277238273 1250 277237023 277237069
    0x5070b0615070c06050a1416110f150918040201050f0a0509040c0c0c151709030702030322050607020d0b06120d030b09060f0303070b0c1306091409040308010b09 71
    0x41c040901560f21181400000c05d00b1005e0450401c1c0204095071a58400055103c0500030708c0d99401048441001d60264031125404017103000e07480d031310480d40c840328140240680d1050284100f0140480e040707000d0b10840308480802c801030745d01c0b501b600e482c940d004000075140c0210a809569a00440c0003a0340c0091500c08682a1907502c21010000c8500a20248040c552107858003412807070540b51190210b0711000030300545154000701540d00c0202072054900307182d09940001d003554017003203606400e1400d610040b50504d010300d120750000c04044400d240342c130341540d000c6920540201c0000d000e540d43c2400140017512000484a9030681c00e00c00d441c40b00c85188406401007a070300d01c48501401107030000408504003c140310054044c0140114144240742da1101000340000b0700d0300c0403494040c407492080c1944400c014014006680f60401990306103003c90071494a850100381c840c1860b13400b4000401d400c01c8030306055400c0b02511b143c1d10414a004901d445201c00946041c0d9022 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 277239523 1250 277238273 277238279
    0x30b0d121803021c060515150c01090614010e0a0606020c120a0b0117010c0503010f0504020304030207030c080607260103110f0904060218010923120a11040c05070b0615070c 76
    0x134400810007042d2141c08100001e0f100d00f145100031885010a86822400680d009507a103030842010300b08821441001184038600350303541c0b00a07215158451101000e581d001031042c00365107040e25034041c6004104100ca00d2411078001d55803000041d035680102c251342c018140d404010301c461200a030b00f05400c4103640d41c0da1206e80c21115828400f1058a500e0840032500c41841102200c0c121000706002d26009418001080029030010b0001c600398460103078000000381c0c0c0141d5007001030407000007910315440e00d100702402010b601c400e08a8542000c4103c0006000262550350550f900161449418024980070810b01000701c2c440951282080d4104410440c0c150002c01040304200c000400c2d10f8030650054502503034501900b42c0782001c41c1054071030607008144011505200404001a202c1d40749511410300340c80b903e064030905403995803d98981000d004000c026231072454085d1800a81c1c0d19030910f04c4001910052086d0950b04041040000c044280d0b5400f0341c2103504204d803141d07 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 277240773 1250 277239523 277239559
    0xb04110d12020106060c030207031202150c040f1406070b040305090607050c180103050d0f0318030c0501060e1b071b060f080a060e0604091407090606030b0d12180302 73
    0x1148401001c0190308144001c103c05104600708950140c0c190003c000048c00c540e100c80d00c4155204c8070808500c900010079148488829906000318102c410302c40d501d901704a00800707409042e806c200ba50700c2e0100080c007865162001210350f20742c0c0082000e040ca444c0e0386000c030340030304c00c00810f180c0c4408041070010a011022652070520b900031902c0c12414800b140d071440000e031b000d110250060304a51106d00c0c070980200342c01c68101c1e02d00e280000e40481e0f14011170081c40e08090041e0300107504000030302c3c2007010912071071000c0e0800c0c0d0000d034210300d042d031044056025001e8034071440c00d00c040b40c0c03001001409107031441030805c1e8994584109440360801800c1c410082c044200254880020500c00c2149209110030744003d00203004142c0d5440040c0005043c2c50402211a500041c80150503e441030000c0c001030003942c0c202041e03072494403600400355000d0a03030701c9d84138120402582c800107003454003001c21490f89090000c14500c810354101010f484650010750418510781001070b81c50 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 277242023 1250 277240773 277240793
    0xb0910090536010602030f131509081e12070201030f060305010902130b030c120a0b01060306140402090a05040504020a180203041e05061b07060f09060606110a0b04110d 74
    0x5800a40042e46011003690103196200c00c3c414503025800407c03500508480c42c0c4010300c0d0100f505012502c40c0c581d11111500c0307840c0d00070307420400503c0702001401101c409000400a00198840d0740461000d6010601d031100b039104990018039000045400459010360005410411661000c208040e40e90504502804d00c4500c101c2c41458044140700d040ca01c9403045051255015000305400b1000500b40a5034908204442800f445002903820010300049545806031003d9900813800503c3c201240c10b010a81e4050948911300502514901c0e41307590030302c070048600c21100429261500d0000c200d0715032040d00995854280d48152500c00d070703c00c2c1c00450040b4454445034001005031000125824001e040c0201a034003c4004070742282203a103e0411010080c4440c0380c5010386a50f5120700315403415007510086602c0746090300901081d4802c4d00010101d0f820002481161911015118500c03140000c040c02c001c5800b003000c0c800700d0307403690b51460400340c501d400d1141c0ca42042030420b = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 277243273 1250 277242023 277242079
    0x108030c0c0102030703050d05100513090203010501080d050715110403060204060207090b061b1e0c030c0105030c0d0c12020403031206080708030f16050d270b09100905 74
    0x3910801d103804119502c000121120103800d0741e10300d41000681c1c0910800303003a0141010044005525020509590707426480461445000001406d40c00901c181400d40d10160302c8041e079504440c41d840b008070340040849142c20703400b000e40407900148880460040100c090660000440801c1c0031041003010f500400603549507800721194196540c02400a03a254600e8003900700500380a1801c414030001c090425480d0300c0402c2d47c00f8528141c451303000f20b00d10348080000070707401040c2d50b0f00c4904060200c0c82580701c0070304e045484d40c82d043d05e00d10f0041c41140318048400d991035503221084c43c0b260610000091040c8015560340e44e59040c001c04018020242c282c4040c030b03102e0001162000080c96100300c42085010303506182d41a40c1240c280d401c421a80c80007141d20b010304c00d00240342030001c01e0050342b8549624030106652a00300041e4940d00c442c0c040741204042e8180580703000b05060340c49c4004110f52401c504000c030740c0120340903013540e4402508044402006011003400101240710 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 277244523 1250 277243273 277243297
    0x90108040627060b030303070c14010902120d0e09040c1707180506100e0a23040e0d021203010806040f1b0801020a02011103060901052b080703080906040c090c17010803 74
    0x126130755030b0080503241e200c10788004000c11703c4105041e0000398141d0f0704004d4542200c0000600002540204a860a82c52042400c0f0781000ca0b50841c000d4200180a00080c0107442c01c0030030b80b40aa0700da0341401c0081c0038a403000101a0302c00c681601040100b48003400400c07403da9605c42d0040000c4010388802d035019446032036002001c00101d4410014281819801058a1292480c21540e030380500d1450481400c1402003085282072901ca42c080d40220040a40007450b0400d20301c00024203103580001500e10000042004100c400b2000816642242e00005121088105440c0c841ca201100b10f02c0c8c101d00030320041c00050f400406501a24242c40306030001d018401c00306c0c0e02c03071480348802c07621141d1200038840144a54101104404d0107050b0a0380701d0810310040c8a40848d281c100000300300c0710b4800000d01401003560003500250006000c0c4020121802c09564550703401c00140549107003180d4800d0400542407158140b24a58110b045011a065071100303545626503101680b1541 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 277245773 1250 277244523 277244531
    0xf0302031e07052503050304030803010801061a040b1602090f09060a020a1202030601051b031806070f030f030609060605041a12070f030b04020a031406040204050609010804062706 79
    0x50384541011a81c5403944880034004101005084c804038a01041c00c0f41e9104030f02140c040001b0f0810802000914024240c090f104c0d03140040707c3d030949003240c00904018649928500c40c1e600c0b00070a46090f42c800c410340b1a10f81c07002031814200320214410184d44003044000340000180751400150103480464140c9000340d480046a0061b842152002000a0303142000e908140c2802c0e07001e141c0180d01490010300c0c020740c52114030044511908240a00d41001952076100c103024441c0d806000c1003511502d08044041e2180058a6984a40075052120b40031003180f034284254012000740814507402c01255488541c0248690041e015180305102c094072444414003015055030804490741c8150002661145002c03904100c40c21b480205241e2268440b0080740d9850000d01007003c0741ea98000b98a203c41c400c00140d03c03001070900c0f4043e40c4100b10903c8181c842108845104600f800d0014103030300c0300d142080c020b00c0c1403039180340d40c1c03042070802484402ca100248103005000e420140 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 277247023 1250 277245773 277245817
    0xd0b01050d1d060109110a0c0212010c080f07090302130203060d080301080c04110405030c13020705100902010e010305070504061404030b0906090709050c0412080c0f0106051201060b070b10030f030203 88
    0x1411141b4201c0c0100420005110348100f10b846040010700282c8054421b184020b040c803d01400d41e07848041442c003260302c40342045502e801240400c2d501c00214688003445e1343c659000700e440781c084605015120381d0000002000d58407041d00c00c200d05507028103125901d42e902c41f5555261000c095025101c0e03030602041010f20711401e020340c6d0503950018058039241c1d01a0301080810200307005a0140603400340304c4503010541c18807511452440e400c1000c91026494030005095480d01d0f00c038141031501e03007014031880035448002e403804c0d0342150503e01c074102c0e5442c21801003800b40d90700042849100200f044070041000c510240a04042d4085450085c2c031292400141e5808891103d40404203000c104480080800c00d800e10b18061b118041c580030b040c140c42c0b8103048080540c0d1219070b4480d0f90401150400c0720076418030141030302c0200480c5042c454100424410160080c0c81644508003040700d103803040c00c01500842d4031a00e010300b00f03042854043d4481c0c03c070b0300716080e001800840c00 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 277248273 1250 277247023 277247039
    0x18010e0f0c0102070b120c09010c05031314031f05070c02060d0b040605090403020303150604120f0506010602011509020a03020f070b01050405070f020a02040f0b0607081206030309060d0b01050d1d0601 88
    0x6a20b84812004603a031b01582d80381550041c640060b891241040048415280894403e200a010740c1c100504442c12640c20030400301e1806040e20b07102030095215035035481c041d0301648004080e8601407907011405403030388102161200f80c11035001c2c0d80582c0000310240c100013503903c0070700d00f04000e48052091320b940c0d00400c03608003c11100940903800c1040080e0001c0b24402c58140c00303100040c07282d401d0544601460b80360700c0320028103e500c4007a00560000b8480100005401003505100a00c0000e1170700c402070700c241d01c0a11444404580115684003a540a6019a050717484181403454072215542440354050078203100c0c2c07034020b915050100320400e00c2000c004828038802d0b00200059132195003484004c0881580f01080140d40b01d21240c010ba0340c030802412198001d0b618203443d0110711486400d0958041e2006100fa0710821455056403034403810348400e1404080b0000700d42c01200010f070382d28410032444010052034429070b011245030014118110034010710485400faa00d0b40c4039 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 277249523 1250 277248273 277248277
    0xd0306170d1d1c030c020306091b06070f061401030c06081b07050c060313021206010608040f0c09110403060b04050c0f071502030c0a14030403050318010e0f0c0102070b 74
    0x8601c000420180d036160806050181104036048042c0490356090009020300f03540b000081c00c1100010f00500e40714080d881c2c10411140c006840c00b0103845030342c0030094400e10111050401d0f5006580105003007040c003110a00d102401ca4200c4d0041c0300d1303003500d107241d0030510500b40011111420403c0340840c0c40351042c0411032054580c4801c2c425000d1060f010300703810742c0102808650601c9403100856180e182c1201541c02030020012210800a142c8100315490b0280c28110070a41e00ca41d004115041c0c0c0840c8140d0450740200c80c01c0c6280c005418403607111820750b081040814200f1341810790136041c0700010400c907406203804009100c044810042503840c02d42c1e13031030b41c13031401400310b0009903d80f030340204481882880c6c2c001130341d5a10190300042ea0000c81b0000c07031080010a000503016000102c090352507400d140f0b05461441d0541d400b4110340406081e8854031f01602171a005200400d42c001c96000303a606040b00c070050300381d800c00d540e01c00c0200c40e07150040c0690130000840d040d070001 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 277250773 1250 277249523 277249543
    0x90f01030302060c0a121805011a120a050709090318061e02030a080c0d06030b151023090a170106030320030d0207050106050d062a2c030d030617 64
    0x145040062a1441c0b11b5809400602d56045291a030103c00c880050424403030702d480d4003c40030680b007994484c102003141a135201403140020f41c10000c1c0010005802080030425034800c080300140340206410110707100034800708003003030364500ca14000c100907401c0064000c0c062200140104a07055035082207840b4003c240400d00400c0651010a52500e140c2c00a030005d60f00600000900139940c0d1605210b03c00c05842c2120985140c3c2e68141c1d50b030601007d0010740c03070024100104a07200e4031001c800061044403401d1200680891402c140c0e40c0c0740500c0300000d06421081490078401c0d03400342030082c10b4600c400c60200780d854101c1220019642100301c0c01c1c42c000006036080c03107266980040a07500c002c404071890f543c0e0b05004242981c0e0403980041081c003400000865586820401454a508216401c0305150051001c4005c591100122320380079112207007000348251204481c250203424020096060103210400d00039507500d6031014003210441105071a411218891090321500c07900 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 277252023 1250 277250773 277250777
    0x302070317060303211005032802040b06040b0a0807140406050f04080a05070602101e090201030605042310030822080a0303020a0305150a090f0b090f01030302060c0a 73
    0x28950301d105942088080e40c0008007400780c9107000464400280c2e50403001c5400020100400c0c14800c00d0b102481480000d0003041d0300400096107018040d040002c894600283c08500e000700c00b40031920f43e600020104100507010700c6c0c0b91529510240035541025418100089180380002d848900c0307000040941d06040780c00c0c0d480d00e410440d084a540d0b0105031124090307001000000b030251002c1014101603400344020700003090034140000d082c0300100d448a1945810b10f80070150170004410020b008200480c40054249142d10059019040560089501600d403003110609124400710b1004c080c181508055802c2d611041c58071340b40c0380b0500002c0e140d40028490604814102b01000b002c0d2084640d540a0300c41e9115081454048d850308100c000030f0300030580c0001f09826004241e00000342c28040c031704a59481c004210810b0031407090070441382e00d82c1c50000c10140640c0c0900880ea80241005040e482c3c942e40c0d8204810003844100c0041c1f2544001800000c4620240c45440010b5 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 277253273 1250 277252023 277252037
    0x10513020415150e060415081e060f1023090f0603090303040206070317070201090c060806030c040c03060b040e010e0c2104020a08030705010b01090501020a02010903020d0f0506010b030f0703020703 87
    0x1250f8211955860001c0050700306000f0080801d0141041034103003c154015540c8000c603150542100142010410700c07040b1440c1c8207002c0c00000d5071104410b010720b020698283e1040e10b075001c021504e09880c0b400340c140c80b040302545c8040405250b00146851902541c410b1400174495050000c00d10044076030a1098006001080047c64218001c0221900900d811034041c0f40ea1800a06000025610300740035131341d9804408200180023840000402407810328904a25114004c0780d01c9641d0500d40c103120b107540d0b000558005003c0e600182c003a0004141d000c3c1c5842c0c80e1742505c82d01034401c0c05039110701030b6003400091401640d46d04850b61024490701d01c070040320a106403403550001c040c0040b644a45050001300b1b030b4132400c00c00390110a01450011598001d060005400c040050b041070b4115000a480c03500580d80028040c07080b00e6040d030b030082d12040503040c45032205400d000000c1890060070000074921310350310050b60084855208000c1c09882e0070200364224415a54020301040311 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 277254523 1250 277253273 277253309
    0xb2701090b030c0a3308070309080f070f0c0f0317131d15030c061c020706060303170705040f0509070c060606020714030109171b010513020415 63
    0x10607000044064000780c01c0b5441d0b16900e41c0084c08002c0d29401c07540707030b81410303071040818002021484030f0000d407800300c0300195072140c6a00030001c45006014105050b100c14911041003c036200b20755920703242001c002e4403001140340014003a140007000390f40c1c05601800200d03203114100c00c1103003125804910000b103d82c0c20b00c0c048241c1d8004001e04841034624050001c1c0c100c0d5800e10008003400c08000c071001601d8610240409581d080c0c2105029502140c8207000300c0d01d401c801c5400011500207420464200041c211019110b8080c000b4211401c0071000402c140c0c10258243c01c0942201540040d03036280711003114240160720914003401d11081081255042416060b50082010b140c6446407030804c0d00d0b120b0039a0141c0c2d0210f4016400b00b0b800700591501221800b66070401200244541241c3e6110a01241c0640e6009048038000158051120721070000034441030f1300030303002070040d80741030203160f140885000010f074021401c04040e0141c104503581d51505440c0340e07084d68007600003 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 277255773 1250 277254523 277254539
    0xe010527010b060a050304050d08090606010e0d02060a0207030510022a030d05091f020910030b120a03020c010906031404030e0a03021f020c0a030c0303140d020307030b2701 76
    0x2800c502551065541c0306074224041d214500103001d4490107480c1c1541e2400c1c1864810702e0028503104017020000041d0500900d00c20208032590810310900c0c101041001c5080081c5400f01d40c880025401030b40025a55041074021510310110380c003071000d030340e0070348207144141c0e05034816a02008002d4020b82d40d0024800303404c00c1d600014a1031001200d0030500c008044108580040e1034840b8181d01001d2550000320707032008196590483c0d09000d504011540020035400a90305203407605150315219074840b19216580c0c000d00ba02014001c0b01c1e40840c0c0c50401079203544440b65281e00080c2c0e1160040382d218000e0041000c07071200484070020300e0f03603562411111086d55048450340074141400000141e41d4404108590500103000d0014845100001070300e070900056585000350010f80082020510340304d40c1204407609410213190700854040c081340a40300da4020000407500c04024050070700d03450b903ca9110f00d01c09880d0448584501031560902000109100091000c1d40006101c590 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 277257023 1250 277255773 277255831
    0x1d03042c090c090c04090f0902100302040e130f1a0a060b03040317070219030e0f040603150504030c02120c03070b180d060609020f0307030f0624020a061503060e0105 73
    0x710029100c03414507031560203180964000402c01021f0716241c509003403c1d03107002654568156000d060840c5040d280200a00e810400180450010b0130003121175030034810448981941590710103444c45100e5680b0140700d60240c0282e4482480c2807400b040461500c0302c54080f2070280d601a12039030a541058040c5001841000700300b0003c602500d40c005548488017041e0701a4036100381c0340e2103e840c1115050213000300d00000e02900c03c504052003040443c0d51348a0a041c100000c900108156031241010b50710034055a00c02500716640040b04182e400c4080345d10565440202d06480f07800e50f9400a403015409001800080c0541c00c01c0d2900305460040b41071140346105160210b1110345d1101c9200898011011090102500104201d1200d03414842c0701483c0304e044c5000c200c84da05000165100107900e11404a12030365001c0f20205c4140204812000d2580c4484140b1021001ca4000c0196003502e00c01100e81c10b04003101d880c820101070041c00d101343c3c5001070b80c5030520030700c2108003c8a = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 277258273 1250 277257023 277257031
    0x10801050402281e03031d0d0b04110915040509010b01080a0e070306060609150201090b071b02041d16030f0b0c0d0c0c1502090102060105041d03042c090c09 69
    0x4143d0300b00d00081c07044195003094040c8460729110f81e030704034074508015114058002c285600f090f28904005441c0e6070f264440c4401f1500060001050b82c3e4a02c0c1150301a15101303001540a08100108400501c03c6c20520801c1c0c00c007910305100c2da840320010321307080e0b540100c0f8040c04240340000003a000e900e5544914074151502048910055680c1c031a00c0488009411100000c1c0300703a0700a02c41d141a01e003941e200c4400d070b84002c0004042c0c64541d03601c9020060414420809070425000d003668aa50003004101c3d0010420800056038004c3c2d001c5109124600c85450b020f4642c0b8102c01484c401d64003002c9a4001c40014100e4405a07100700c0f08020092400e00c00340018442c241443d162445001c00d80c40d05511000c592685d182010381003045009000850303980100700761642d81e680841d000d41155400c0e01c021071070018a00042402d010a85800e00d510720004ca0001360b012030b0840804514040c50401404081e200280f00001100844000a603548085404640f41c14400005940 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 277259523 1250 277258273 277258339
    0x90c070206120406050c0a020d140c010e0a0b010504150e04031e0e0114030c1c02221a0f04061b0b090c1203090f01030e0a020a0b12010801050402 64
    0x586011540061501d4010b10380301c406401e494410001004003074411590860395442e407081c142152080020f6480c204250440c0400000341c1005401415210982e4042c40c2c580b0006e000c0c01a5000d05a565901d5507003007a170319556687d0000849050500c82e551002480303208072002caa050030f698050300d860240c401c80c20440f000512420600f0b11894010600d007035643c81c1c10140c5000000100903550b40d02c01c6140341300081060200350030078103084038030604003208020100020391610400900501c5111848407000c0603003017800e01044044682030340e14a140303030424a183d41b60114058084c224035501c105008110501065010380c00c00c00b2400c41d003645808040986545020162006440781d6a0310350050100510900e0008400704e0f51468850040d82064148000100c0f205202d0f400903060543d0b840c681f82001c14280201b0030714980203000c1100b040d5440100c2c0c049540300040c21901c070392401c80040b0314010f040c00303114002c940042403240341300c0c08100e04043da02d04410010f10 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 277260773 1250 277259523 277259527
    0x111c020108100306090f030e18150a17070806010f030804120c0803070311010c020a030207050f04090b07200607171314030d06050f240c0109050a200906090c 69
    0x400a0741d5800384140345c40c801c21100859420034500039010341401100b240c0b042c3d403500320242e021000c800c2c0c42d036842031170301e058000b5541240340810301c100d4090300405e00800f010800043c0709500026880201d650130411140a0baa80707507c414241c0049000082c4820300803c41040001148849180c43c2801206041d550a5031030805500d154800f44048020801d00341c510001141e080c03092005c5a00740f40050042c034039065034001c0d254045c601480784503c407411291b06840d10307217502c6001c1190f40202ca04130503042c55035000e05484090401c89810070500440400001c0000c2141d601910841d00c03021100000e840342c00b08a0071000f4103034184800c80c0c40c10304006c81d04404c0c403020700d00c030b8001c041c3da500d1080420802c1a02c882e034101c24003a1038030000f010031980b110301140c1c0c0c1c51030002d40902841e0b1000707214040b061168860781c2580e5030901002200740000400d9030f0b4813240c85030050b50681c40000015480c61814581c19507408859070300020b8050600700482a805015001668 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 277262023 1250 277260773 277260779
    0x9010908030409050a0614102f070e07020d020c010c03050f0a0305190c0905090603010902120609010c0f020307030e030c210d020309090c0705150112111c02010810 72
    0x1914503001035014090040d241c805215145c001442044064680e1301f805107041700c130f03c07000304101d055142801000c0001044081c5070004a621036034054684003100b242d250700d6152461503860050303000c0d0341c1c0700d082c00c030001c0755406000240303407100c0c0c2d80d0a40151495294280055480c0650340c0003c0c1c1c14400f0412403404c0e201c0e01040104828080c58400007520705000d000c1036502c5007180c01040c010b91030042144480d5800900d14011203c2c1158194240d031b49550209024181c40a4000d411803d6040d60802184d40481e100740320b0401803000b049040e2000d10122001054440054090b0308100084804244111480000450301604441c40c2642c4c44020036074003601241e10074a030645640c404521801e01384900d0800034001d1005504210300f240000d141c8010103450f07003640758400203001041203414000200314040e030000d000d01030f40e9a10541203603101001011165920380711490807051421001010320140e01880c1820b001031594010b40340780c0d00180000c07244050f214400 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 277263273 1250 277262023 277262039
    0x3021306030e120f1e1804021c1b110a020d15060e010906060e030705010203160c0b0d021c11041203050c0615011202030118020a0512070e0307080c0a0308090109 71
    0x2803500001020082d680d4201c002da402c60189505d500c103a803591020804080b40c951140ca0402103200103e50069440c50501c4000f00c803d002544807086240c18502c0d21840c0d0100d183c01d043c03214001d40c1700e140d110382c903c0c3d2042c0e48455845800039840102403050300d01241c0c50040311036420703404a0000510640740c03580c0781c25010b0241d104c071480340e44589051000660080c403481c1030f05c5041d001003c011b4108030020707440c2d0164110403400c4110b181081814410900400401800c00100c0e9a0b512001807200001a5102c4003009552000d042240803418103244508080c4280d04000d0300c4c2030034144039020b0301d514078844054080007800d2040829651062101502840d1300b1075000307284450810015207440c0b82c3e481d01d100c00c10310500040080400300d17080ca8105981441c00180d07103686039013007a40c1310300503040c0240902040004211109401c4000c00202032011400c507402d1aa41e0000c06a481449440c41034008020703132400c000207450354003c0c061809050405800058403070230340c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 277264523 1250 277263273 277263277
    0xe0d0b010e101d010509060a030c030804060e0306040512162a1719030c2a09020901020307020f041404030f080a1a09101706100603021306030e12 64
    0x6200742210105202c0e40e56541c81c0c1d8100100101a007032081800800710b110500c0c0e0051041c540113800da540050100d60f01c8074405406168005a05c101032071310790034504070790b42041c0030b5200841d803081814903103440c00280e481d210320b5110005282c041c3d1100c0900d100d580013030404c0c0000d111100720303040c0041c203540c0c01491542c8061075031030f2000b904207034040b8141c841a4010b20000450000101c940440410700c0030321007480810708001031505260485070108481d101420191110348100b0b80d0125120941c12503103021112036642d03548400391081240714508605c0d0240e8002c000c01001401c1c111024664168002c00c00102407074822100c0e922000111000c0b03000500c0c81c404850502d80050000b6003081c0400010460075052140e41e82c7c8803111030714400e10610342c0000244d846c0c0300c02e010328005048140401c0d05041c0d41842c50541c1e410080c0c07125042100f203880d001c19060301c2031080c1d070704002d40011a00b546510b024015001010340e4007140c14a40605e1a04030041949200 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 277265773 1250 277264523 277264529
    0x27060c18060e0301050c030714030603030f271203070212030409020a02150907050d020607051216030215040206030105060a030207050a0f1a09100c090302030f010507120b060403030e0d0b01 83
    0x5035007032241c190b80d0405084820081020310b109a00b4810701480341e602074030040c021038503903036002da4a07141c00c000039207503000d50401c02070040400104c0c3e4504040d0040c0502c4480650700301150100e441c0000c1000f2038544440c04000707540140314100142ca02961000f5480461500b580d180903200c41c039103c04c1e40e01214102c0c000d42d01903100c0b09a2410811040340c1e00001c1070f006801e01e141002c0010344408800100a13201b90404180d40c0244801030003000203641c500510340b41c0d1214400908021014210701c00d0307003d030242080c044a141080380d121031007154000e0a00786507030f082104005680d000300c1c1d29441015400d01000303002030b40410450695500507112500a1000c501c0d0524800d800500221045010503042c1b04142c42c001070301070041c00e00c0e43d0011074180c218080c00c90b0001120f0740042d41c188202084144001010341c00f042c0200c03083e0f42e1300840701101c000340c017040d2541c281036190800d401304070800100e4172400101070803802c002d10001865829442e4921094403c0e0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 277267023 1250 277265773 277265777
    0x4090507060c140a02090a09081308070810020f0307030908040b130e0a2a11030d0603030306080601060c0611070221060a140103021507080a0302090427060c1806 71
    0x48201403d0084514005002d40210b00040515546039030109078a41c20150035a1903860b12800250100044030041c0d40824880344400103c4942e07038900950340324280d1103203c030b6034015112074201882c8507000b100c40d5000810481f038a9074551140c218024100d0550550350440148008900311030703e04c0081160307402c0060b80f620650309100c445000e05d14090050b10340300f46420741e80350228134010030b050880032600c0ba02c503c1880f656402a02c0c0e00b07081445001044c00002078040040c40d00350b10107800c0d6030003a642000200d0f04c8007012982c0710340070f000340400308400036032100008080e604400441c0c3c1d011205103062504a501140d80c49802001500012811080c07151645200308096580079134000c2061000341540742c044d8123004d8040c00068040c45407500c4c1103811000f410b040300d0020303920110380360382c070f600da100003c2c0203410100c0030a00c902d09120900c0309400c0011000c0607240080c40850104040360382c1c40000504038914803e06012115400720902c44500c404100200210b03 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 277268273 1250 277267023 277267037
    0x1502010606030c030203090a0b0a0f060e0f06010201060e2809050322060c08090619090e0c03042001030902040606050a0306090e06010611010f06030f020913051002090409050706 78
    0x41c0c40502610180002482007601c144200040d0b104002403008101d40c022004600c00c0c2c0380d40c40401e02811002e01615811803d04070005520040741c00164494021424812159100c1800490076100039119112081c10b821000c2200543d03203906480010381181500700c45c01c9004001001554580c10081e1103503000410b43c0051280da80003c00c0b80703200d10852041d420303820000c02030084d0399a98006444d0280c045194103540d216070044ae0551074042002d039070404007111009060540e1401100c1002915001107000c240d40503043e680940d6204c403c9040340d1818000d4a403980c503420342d10728100340e219410310025844510940024107088c0d52901c1d40d8035042100501610807650000100c28504892180032000214240381551a03d01e80904022464504a03000d440040c540b002110302d0050b0000170064481403800440e4401d640d00c60f106c0c0e4940142d4001d83c000083e000d030060300302601686a81c101030303008205880b1f0080001036040c9041e05c40c0fa250407002d401c00c4000c0341c11 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 277269523 1250 277268273 277268279
    0x30d0504111e01050406120e031204200303030f07030b09010609060905030616050f0d020d0b0f060a0206060121020706051005060f1207091e030201030c1803110102030415020106 78
    0x40b0204841410404151100c42d841c040e10000340345109074801c45007008540c440b200c03003040300303500002c0c50a01014116a181d601d088248007814070152012910348040b0103444030044490344040c500610001e006c3e600359520180640d0600c03000422400c101b665405125085565502d0501c0c0a0420b40d901c104589040c08c0000d0318040303581e04100c2c401c3d4051010840c03445e502035840203641c030791840e10b2034440c440c51084454a000381d014110f0404d00208190502c00300962001e101c0d0718040300d2218100c211401407241c3c520800c240c480058001000040b49940510a078508169100102c01400103415000b0740403a000518111040c42d02d035000d111100301c030b5840c002e0103000100e40d410310302842c414104100d840303000810303401101c10000094072180181c140000030804d50000004075210320f16101403841c801d0000724003007483c000010080e10f10900f060a4840703143d09103449036505680740c291045c480300d8541c90461100700710100d00010039030310800c040302c03040e00041400c0d41 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 277270773 1250 277269523 277269529
    0xd0c050c030c0a03081305030303010627050108180316050a020a0512060a0e121603030f060807060c020402250b0106020604081c060b210906130201080702030d050411 73
    0x24150156100ea4807001580b034203503445040c40800c490b4464841503540155013401c04000c0d42640c4030a906000210002a9151704010744400041a600004520030390300ca4442003540c0d113030f0040c20300065641c40080c03450390701a01c682000784000c2048900703104101e0311450b000e5012580484440d04962654811800d0800021001c1c1c04100d94142c0090308d00b00030943e882c0402030400c0605521030b044510541c1d001c0c400c0041c2c800b00c0c1642e0540d6010190845210f540b801081240020324000b0b1814201032a441140140c6000c000138040d140d19108003100d09100201d001d0342c0c0030f94200201c0c09001004030340d02501c040210204600b0400b1400c1c028683c04050b8881d00c20343d0801c00c200000980c40d14215899110400c501501c0d2400d10390020b03005080315045076001c0300001444d8944000e11807107001120f02906610200c80c0e80b00f40b620798135524151403260007007006a0b0320400560040c0019544103078280304a90825020030111420340b08152402c0e5100d40030345461405c40c1c2 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 277272023 1250 277270773 277270783
    0x1306170105010b0a050a0e030a030f02100501080304090906060f0306050403120902090a05130c0e010f0801060513021606050408030109050a150b0306130e0303090706080c090607060e0d0c05 83
    0x480a000204410740c5010708541e0684141e400c00070800000240740303c0302c030b4062905840b002c1ea0240032980210030a1a01a200380102d804242c0584600381a502440085010b818140d901c6080a18101031034030141d4806001c0849007119a0307500d4140c080b8501030101c0d2a0401503010b4500841d03241042c0c24050b2041195160780705440d402c014030702015881d10610b441e0420064523000130f003541c3d2101c10b8495109070403030050245041d039000040441c141d6160780d050b1b600442d90318003003076540c020080c225142c034800d040d040007440707038660796000082d8040d14102940c0c410105480d031a135901e200c21500b048070121781080300400103000f40000e82c400d6503488840b040301008800c410a03804240c00496104d01380c0c500310004002052510b51810600016078083c00c244440712060f00d0641d165042250464500e01c103c10001031070611850669004240c1c0c00ca070580b511a0043c1444000d902c810300650329103440399161b254042c010007030784661b1802a6034141c46080a4a001800c00d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 277273273 1250 277272023 277272059
    0x270302010e010903080412021804030903050609070f0b030c0702060a020106061d03031b1002070605010e0c040b0d020d1d061005060408120702040b04091208101203120b1306 76
    0x7030700d2074240001080c400845047e0b51030244e1000c061421072001070380c41d054400c000900f23140c0750004d0100301600b201c40101500d120724103884e90781c0d0f0307009110b5030f43e9102c620a044852080395000c0014941c144025504050449510b5141607120703004105154025804100140c3d0340766000c100c4960300030a0406841013000e01c18078900c9030344c00003d5032805600382007242c3c0182031141e59801c2608020b1940c070f0102d1460103545510352824034000811003485126041320416001851001c10307101150292420178140e9402d04105007007090007500140c07018200250356845051031560740e11481d075100c0304160010400c0c0d2030940c941c84040755040d400f01e40102410f000501030140301061003240e0005121b02c80d91612043d000280c040c0a005601d142c00914044c9910305004004a101c081c4650940f5140955180c2c500f11074000d40342481002403288a20380c0440000e4800c03045600b50804204002c04d4a0915500007081e4940d0841a40baa03c4d5440c0803c01c07003100c0c403031218405 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 277274523 1250 277273273 277273277
    0x509040c17070f03033b0109050402030402031504030c1a0105040c1d0139120206040218091f0605040f05010b030127050910060e07020d0f270302010e01 67
    0x468508900d0241c100f400d40401401d0080c1c2d40142850b940326a00d504400c1c4c180905200c80c10584503108058a44200780c8450005d0703003c0310042a103003000c1c000c903405541c0c00f400a080e20340700c9000420314143c0c060030071030801080d4070414000c02c00c903840c2c417a44800303451602070039945008104401c840b480b0454a05104126806546402d15000c40403c0d128080c2800185c50070800c00e0588008681d074002008030039243d0038005181a44a02c00401920404861440f103034070a8043c1c1e0358100c1102e0003544810410030413107890814984468100807602e003112540b000450b11040c10b0794291040443d51752345c600d410032107440d050046152040c0308010801c420f50401420000500c8140075982e060030030401c102d40701000c4e140a0b854030740e1496808116600703250b000d02d61070309280d80c1a50391a071705080c0302007405850000490300649040d0010410306c030f0302034001c0e100c8403002036000c41885408244226105d001c441080e19549400210740e095030306500c005008003010600842c1 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 277275773 1250 277274523 277274533
    0x60e0402010f030b150f07050618071a12040323070308011403160b04031b0e0f190905030910020d0c0f02062703100b1003050405070509040c17 63
    0x10150342c004a82200c204420b00d000f150448030340c1c000c0764015000380941c03200d00034005103404042d148003029010b400e10030740a4445a03140c1c1441032141c5400c07045411200c0e08091010004840940702080c0c86d1101021140c1c00c0402d5030700707101c440d48412a0300f80c3c0414468503c007506241c002e8000c00241c04215a0706040400c2a14014400d090501907400d4a01c102e03224080b49039010003042070100442c011100405407034808070300803504a84402c0300c1c1080000c0140318402d01c060041d2051327a00e010700c030711a20707501c3d00d01e44d4242c240050928500b5000704100c03c04507003d00d01600106900440042d942d905010081c440d214412183d9642190046014000b1455124000213229900110450940c80942c000a0079920401d00c0305961800141c452008440392444007110300300088050320885407901d00b1460a560910280c2d55110404080031921180298841a0464061270441c2c0f011034a440204020070408d98060f03941541500007080301000419400d4940030010029007 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 277277023 1250 277275773 277275781
    0xf09060106110703060b03030408120a030c02031602270a140f070207030f050111040e041509030203031902040f06050c0f07140105070809131a030606150a120905070504060e 76
    0xb03602c40c0424007005094035143d41c0c01c1012550200140e4002c0d0824205a0318890500150b880c0c1691101c0c0c80b82010908105802681034004030540c0e40c424400d65440d9a5098540d00300700b198607138401d09001c4480c0c00d8440760341013408030420f548251078101e0001018010301030020000e450050082d500d1000310340c02c0204056000c03a50400f101d5001c1c4403071110b10280d15210340035244140c82321600190205000890f080d071404006c0c0124021250344061040304450344050300c07108407024025034000c0003c1203840c10481149041d14203218001428961074561420f06081a03070b0015002840c082691100c120041c0b110500c40219200105203440c6050552010100200c0003103051080104a44040c491320300304544240600034141480c40085044040040c8120a44441d0f82907000e007480071a07050005e41b0301e00583c0c0c001c04000001b48180711210203a40a14080b40420110304000c002d0180c1e00e002c1c86148610840c00392485500380700c10302044400c40d42c0192502c0030903000340 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 277278273 1250 277277023 277277057
    0x5010e10110301031a09120d05010f0801020c070e090c0307090b090105030604030e10030b040c020604051c050322051b090a1e0b2205011505030402031f060e0f09060106 74
    0x41ca4000743c076600c5c40043e80d158610075085c0001e03a244035403125000613411090342d021b81d10541c1a40c0d140140100d10a8031000287e00302c1c001c0c0c220018841c2d02000703042c03050700850591281d01c110141c0032240100208d00102c2d040c910700c1da10070071500b501c5495401951800c00c0b0040e02600065004000504c1c081d1401048294035610f00c03030041185020b059012803290b044045910070181c000e0200407001070000359203050440d01a07416000d6004000403802881000b0a40d40d03116599950441e02c2e991000310500c511f0020803400c0802050424000500a0140460900c6d000d80748147c1c4210380700911420f1301000700390700e1009107415164540c1000381141c000c1d0701c81c0c0c20f001c0080c0360400d031400f2801e1801121004803503c0154910544034001541219041e10f80d14450300d4414080c06405890601064800952582100031540b803c02d502c2c001c2581e419a4024010900540d10000303510210310943d4a98011280642002070b582000c002c01e50040940d454a0603201c8140300d40 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 277279523 1250 277278273 277278293
    0x120d0c020d02120a2d0305090304050f01050f0d060816060201090327030506131a01060503180c190608070c031d0402190905031501180b030a05010e1011030103 70
    0x3d503204002c0d01007000c5186034480d040d11030212040c50078082c5141c0c00c1d02203405108100094490009041c40001080d140e004026503040300d001511881e44480400010744441d00300e140782d2080c0180c180700800700701610b4081e5600810115000e4100c0ac40004145031101445400030303801c0da8103018a10000943c41110951443c1729800183c2c035000d2202c0303460360202e00352b5102030b12702d1180c9404c1c00404e4000185680d0642d04c101c108110207c0b810911181c0c024003480754001085090000440c0b001c0d0520707040c0d2401e4540c80a8924083c4a100041c02c1c02c0c44186c114020701c481e046040c000988c108041c2c0da08034400d405c0c40c1e0080351040d9401080f070f0b00000e110400302d607655483c0c001c1c1901d0300c0d01907900100d05003a86841c000c06c51240100050b440e8402c0c1c0b0321910500e00c1d40c2e40314041c84005281a40c07108415034040385d45c86d43d1001c3c040c2010f00a02c5405208920100020690a03c181c1008170fa410025180c0345016480b40820781c0e120303501b84504481c040004000003803001fa8 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 277280773 1250 277279523 277279543
    0x60501060f0914120c18011e0b070b0705040e04030203091e0f10030608011e05100602060703051003080a0809010507020313140f0a031a160507170c120d0c020d02 71
    0x180419950484c0e03001c141004074400d002a00504140c41c100044441ea4400342c0c180c40049503159409840c3c04041c40207030265200e0080360308410011800480c8200a160354408190306180389802d0782c90307820a43c1c0920131141070f40186c0000c51f0046403807a1090f500400080c10f880742004840010002880d00071090350841e00c1403050a508a11260003034210300020b200d48070080100111f03d0103054400082a4521440d403454100051140d0101c0780701d0b003081e24081d5009120f02c0d912198140d0080178007174400d8007038191018000002032041130050030803840c01d503100c00caa421f0070b024250a640c1d010744502d0030b40d08140040b5107111a00002d00302210742e644040900c0c10310700c2c030110b065000e5581d02d0700d8015080700b00110602125040000403491201c0407038000d0780e1494105c1c4403420010a6082c002001040085c0c0400e407a2034024111446000c0355a10309001c03100340300d25019031586505900000800c4c80c03046200503100300d004241d4070780040d0283c1000490000d4480706107030 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 277282023 1250 277280773 277280779
    0x70e0f010e010207090c020106080705040618020705120325032315030609031207091202060a0306080636030a0f0e0303042d03110103090f0807060501060f0914 70
    0x100e10510581c0f08202c4a802000081d0042103030300705420000b40a0300c46800341c58150703c034100c0d001901e4200391142030f0440f140000781c82c1d4480c08500da0030b0040d5000c0d14042d265881180101d403640400c40c801180290036002c07540c80d0005401c1000f812812202c00030805140c5003441c8144d03c526400c400c4441e5204082c6880300d50f0b601d4010b0404041846c5040d42e42501c919070030000001800001010030004a1410b40e0701c40c1c1d104c90049441c5105070040084001cad000c0f03800f00050400c3c038090f280c200c400d4100807603050f48845590f413801e40d0440e01d03c4985617140000345241948200c4002117607c8291a2904041240d100c0c3e80d540c2c41140340b49000c201302d00902c0e41c6058414200c6140d0311800406a0b0ba8480e45d8000803459152580c0300b500018400900400100090715206001c51b584880d15100340051030f0015801001c4d40300d000d8900585240410000401030790081801034800d08001805504001d0020100c2103603d0041c024804160800d2055100c030072a880882d800031 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 277283273 1250 277282023 277282037
    0x619081f06090e0a05070b09030706030c11060a021b03040b2d04060816031a01030b030c0d050a061404050a020906060d020703020c150405060906030a02120108030304020108070e0f01 80
    0x9035262001031825510280c1d900d8a0401d80d514620408200503d03094020003c40301025210100703900c00d44501232595038144d104070010026113000e504160108a600c2c141180d9030910455440e00b442000c59403080c0881d400a405620141e40386c0840f21917000950045041c5403c2c1900104a0b1054099000c2e5104010840c0340d480c6c0d42109982c0d201041010003a5251a0390b00800b40c1a070714150b840f008031041e01c0c200c2d80750441c46032084500381708a031016008174510401c0154000d220404c205c40d010b0040001c419220789450340c04400035882203000342924000d504000c030444c0c122620458079124900144000301d040011401c203101d404640400c0c490300d8142c00110503128802081d564680085015400c0c5a00894417248034082615402010301c201d05090782c2d9441207005030395004d24180504207650500402642c0e021540b680c0051515620203005c0052500907404100243d0000007000110750784060030f990050280d050481c108481c00000031107003034a20904504000403 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 277284523 1250 277283273 277283323
    0x30f171504090807050d09060c0506160333050301140a0525030902010f0203090a09050c07020a03050a150209090106050a030b19080c030d2c040f0203061908 69
    0x4a0b44221000c40d0b0140096a889400d171400c0c13910f03901e40e50029004540c003400e00060050003900c2202c00c0c99801405091192f035110403c032081601d0040610405560b000241d2565000c4c0d030403000117498072031155907402d501050614942c10160010350003a41025501211040801281ca8005006d440081a07943c0d81400e80c1c4000e0b400000c2d0011040103005449001c181c00d40e109240c100d000f0389c0c3d180c842050502003070340c0e030b481949102d5810010b1a142009140900d03400260800c500d413003070030b140884940014090400f15041910306400a208046c10040040300300c0c1301c1c04d64a07100550400790101c000a0308840c05100350401d0110000302c80001e1846075000c0c00d00c4020081a8060000c211035107800200114043c0301c04500c500d001040c00c61500003440700b819940b507034a00c105003240d803288400b4404444900010611580000001541c40f8044d90000c8401850010b880c0d1610104201028003110000c03000e01c030069200340030719100070900b141c0541141210f005400c807 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 277285773 1250 277284523 277284529
    0xf06023301060503060306070c030203032202060403032604020607080906070f0b070f020309030a021018081b0d051c12050405010204150f08070f0c060e0604030f1715 73
    0x30100d1038540c4410030000086a0140c10002131406031070150100c1d501a0380d100d60568100d9161078000d000f51b8801d03c00104030000c0e4041240640c000000007400f503554a41c0440d142d5002500100c01248042d80108000106203e2a80920b034a504048403d41010313008604c0610550b040982244800154240382361100c00499207000d070b110115024070080c43c1046241030f001500d044001503102c03181040c0b50341c8000191b0764003500082c05480d0306486a802c00122540302400a01030152200d104144070996140d498001c00d8040302810801c045212900c0e80400048422481b90703159848100108000283e08503c0c0240c445038000314600300340080e200c40f04030051040304581072408001c200700064010f001142d0214055040c11140706c0c5040da8105d0441000600040809002925040c8a800401420281c50078141006450341c1c844c2000d03107d10000c4c1520075800041030204160744042c0c042404006850f0141a2030040300301c4061035000034020307070344400592031542126a = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 277287023 1250 277285773 277285843
    0x1412040816031701090911040b01200a0210050309060703050c1308010b0f0402030f070318080403030c0213060803040e0916030302150907030c0e190509030c06010f0602 74
    0xc42144000203814040e481c2c0280b20118a200c0b401400c405000000345960440c062400741070f0340030343c1c0383d03010120440900004025126000d03041040e407010441034a0111080d00c481209080041c0c00401d0300c5005000801c11400c40303010412404000300f0648000106019401106c9464003160a881e20840d5084c10b008a03043c4950038911900001074044c0c0540c003d10b1500000c0d5800403259014104020890104861070301082d0468400140b50a00c2907200218426498803000020080c584030744985400540085010404c03e030701d12015803a000070207141249503011705106250400304080c0e01c034015071045400d1080781101050101805000d914a03031170a11001650719503490800075610001e00703200345a101d59035004916036003404100b0700300b50303504403c00c4a00c85151a00d10703080198000c1c4500c1c00700703403694076500100c0405c0c09943d0054074100f00035900c030f4000424550818206a0083d100701b10000c2003002141c0c3c0201d10000c0c0f5040301c2040c00c007a000c0c01440f0201607 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 277288273 1250 277287023 277287037
    0x5060a0e1c2306060d050c1903150501061116060c0305040b0f040e0c070305030103030f031404030807030e060405060c0f040b0a020d090b0a20070f1203030c14120408 73
    0x400442d00b001c02d42148194800c0320503800407011110305032240c0003817240217109100041c1c00c5801c640955502400d104000c0c03500a14440b400c0d028460b503e4135203501810b40600260409911003004220031503103c5106041d59546c14040c100d20500032070104a0680c82d880340100b486040c080200a16014405903001804460a26642d86d8504c1401610710303800f0740180051400084c001c1810b50203140e0075100c045502d500c65928590864a003541c0040c0000c0204003019120086061141c050b03034001c900491180d00c44040d079040085024081e20143c1c1c22002d419886031003008081440040c0c401e0f004525506120750340c10198554145034800c603000480c2140000494841e42d960015049800c0b00752640d80d03250094030303210606a28030a003c00fa01c00120030200c4450f04400c000348000301d074800c280c21980d00c2990742c8822806e6505c0d42e8080400c018a200d50403051580600403010300aa40e46005030000740d10b20b94100d0a4002c10070030300150041240040c00b0088004212505 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 277289523 1250 277288273 277288283
    0xf080402120a080d02250f0602280305010821090d1106210f07020c0f010201020c01060306150e09060403050a02071d1b040f0b07020411040b07050705060a0e1c 70
    0x24580132400f24001950100070a41e00005c0c96106d501040311481c03e0002c43c1d44d85c081b001840d0040c60341c135450007030741000c0c846c9848000b001d4540c058a000d0040c0d5070f1780600d0304c0d03203000c5615854001e01e94101514200e40b07000c448001e003292220702038030074101c0d51410000c641d83d03c0600c0c440d082006611281703540840e00907000007040c1d4064482d0b480307000f5024000300b90002c00c55892412034440c60500ba0b80400241e8403503640c41400f460707c100d11101540040c4001820640303540c9075242550115401640d000d0b541f26402003c81c250502c260f000b0342800f1071201c609041080311a87d64007030060001d010420003040c0440302d02d04c24028078008007802c0180136424840c2e04500d003008030301621421030350081d0050340101c9800c5a0141d40445880358454010341c0e10300002c0c00300c150701201089a101d6036800c2204c00d84040705014001908071031500948864851800d6460301c12541c000e00e110709801d01444441c16070240714a8000481031799003000120f810008240039400c41480180 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 277290773 1250 277289523 277289527
    0x80c040b030405062409060d0f0606060e01030b04060305030a1202090612270705010507170a08041703010e0c070807020a1503060501110322090507030b040c0f080402120a08 76
    0x3408000500b03580a0808880003070090800340325941d42d03030b05d05560144d40220708a0001030040c94192098081c950141105440b0101b050351a0070488915030442c0b07000c14500716201505581c188200681c0e01015181004242d003035480b004e13502c0c05241c280d04108003172412114081d045640640e141e1a5001e0682034560b100180d00e030020010441f81000b0f021002401440721240b00c041c15541000040042d090b0382c1d05060044a41e90f00c4810203845440c051031b24140f00c04101d600401c5070003642d40d90560b4a06003842c2144e00c1b680d0811600d001c0b0312007070006201a512028078550000b0480b40d019507206138528002c40c09005442c40a540f007400039400155103140c0002d0412038440c2039a08001054855005450101107000d0b00c0c101640140085801c00c00321440c83c14185240c106800d00c0349607136810034426244201c0350400002d454043da14050300f4036000391700301d071643d90404d0305070042d100700003d01c000c0d00240041e2040c000503648601682c000d00489075026041b80e401a = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 277292023 1250 277290773 277290781
    0x605070c08120114090f16020f032d0c120a120e0a1104020c0c040f0204050a06090801060e19270b090c041b081f090e060601080115080c040b03 63
    0x210303003038024883c403001036145081d0b140a5240902c45c8034031907802040c1c10115500d904c0446075506140000300025407203020042584000100050110884240d04d144018402d0000001880321051031004d108103051010050903100484c1044082c640c1291031511203040307000c00c80714940c5c030605102003145010240001302202280580d6500d001ea5501d100007050442400200d1281c07440c601441d800a1b42c407203155180640055004038078074000542050744450000d020340000343e02140200d5a90042001110001e0054000810b0084024145480c4c422114a0540d440c4000d05106580c0ca0084146c400c6880c001d400c0c0c104102000c5040122541c40d00d003080d100c0540c2c42c00d040d48141e811619180ca41402012852117500149180d503c3e00c5030070544084c1d6003e450314000c01300607400c143c00c014100718460000c04182c800031500038416440c0d03604141c1d02401b0903042000307075070043c0540c001ea0481200420301600d4460000d50f00c9286030800d0380107640008240070703000000c1c4 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 277293273 1250 277292023 277292047
    0xb1305040308060102060c0c03040302040902040912111603020f130e0f03280912051903031407030501030c050d2a080613030c0206090f130e0115120605070c08 70
    0x600c43c0800381c00f00c0390181c88580106440340a2106994541c0e4010802840181055040081d03d1071014002140b5054183e4500101c3c0c4c11030011407001404d410a03881c0d51507010400d8490321050500603003405030031900859441c001e1041c8041c0148001c00c1c00b5950f0b842141d0081c00c22401480507541071a000c0701102d0703140c0e8040c0c90b1100c1042001030280d04500380306241c241d004542911000703042da00e041140d490136448440180c5450141c54a55000d21914540c0404074034403d5800144110b01c850080c0d20100f40902100101840c203001400040c0310f99148100740c41d4120f9030034041180a250052443d5060114807000c0c042900c03940c804402c440b07080609541290007643d94994a0071201c02c104202084041c0c0080c2200010f0f1003d820400c00420b4198000b03484120754403008008241c80520340e20b8400d20b140e681e4040c01e0750915081c8581e10070211100c110024551501d00c01c00184081020088c00e442c0c1c0c0c0e10007003801d143c054000d11440c140d00c240d0f2544c5840d81c415103 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 277294523 1250 277293273 277293287
    0x15030303151903051b06040b0d090317070201060e0a0209010f03020d0e070b0403020109081902043c38041d0307030215040818131505040c0302031303030b13050403 72
    0x503440c0491208551700d01c620700030056906442c14080c5550402451100f8007001d80204142076090007440000c80e501002400220b51140da900c2d000850413520308423040b4081c5000410604801d41b05101140f1260703400784a01d10102e080340f40160311280b1220341500200802680019180b10381c07080054003000e5071002d0400c4a000340c07201c10015603101025515041c0391508441c0c0044020000801071505610800454140c0400c00d0b034081c400103c05541d40e071400701c10002c0340500341000c80d0040c410303002c0c0d983c20012045250080c81c00e01102c0d11001c0c2450040980c13100e0788546900c080f81c680d80d02422030515010020b207164140703158030b182c8a50005c074040d401030107046000120414010340d4035005a0340300354241d1518020505414148500040301648030120806c60507440ea054011b54804505807590728240301d19140c1084220340f0b03250462402d050040c010000d91710194004690340c2c9403d41004101c10b0291400610405444400242941d00d1303c401e2100b45680404 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 277295773 1250 277294523 277294543
    0x3070f020a0902041814060108010b0a1202030a0906200d1e0c050a0f03061d09010609050108010c0e10091502010605041103040308091501060f1b030302030402091503030315190305 79
    0x542048204054204403038246d1045402501144004004200c10f0700395030010b12000f6100d260000c14400044504011303640103a40c1c0d080c055468005038404c0c0242841403840c29104012142d1115124108444407805030031130b2040b0035665110101d241d00e8503242075a41c0b072411400204a440b0710f004014049803c60f4040d00300003010380e1503e420290292103084151910340584113141c42403000311100e082002080c0307071090754036180d000441500d2401003c2c060803010001148044000900030481110524000d1052072200c0d0700e4004103421001c08402c0c0d50500341761030485664400300b68094110f540c040d07904149015000c1040b0010303480618019032107175440c12500d0315044100b0381e8901d00705842d144008503000c01040124040c203041400b2003182e04000350094008000c0e10750356070300c3c40c5c403d4001c80e03000420441146030151107558840c60050b0013078802c1c445107000c41c1c0c0d44d0000421045e150340c8210410501c2c0d80da1542d54000d607414010a891410f1303103a192480d02c611080d1 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 277297023 1250 277295773 277295819
    0x30d02040608100303020c0607030c02030607080108010c02060f07032d060312050c0606011101090c08031902060103171305061c111c0507090803040b0307180803070f020a090204 78
    0xb8000c181c05404202c010402c80c0d8141c1e0080940c480b98000300041980f0021040b0140121000ca150058405000342489002c0d140c40e10741d05989403420146c01c1d0b076001c1012404640040d810000d0107032008a0760380d000003413442c0004641442100c0420540800403410150b2403503072902d054401c401350841c00a40e0f03c1960751000c800803249007650746004401107000d040d04a00c000071400c2d4800d803115035240c84400e001050040c000d4985103032a00440c2c0000e1090b400020300c2014052000c1c8252101800d288010a0b6541c9141c55038624020141130001d4071b0384001031800c143c03954440e85100500070082096541c0d454440000070980c0d804030159034114100313004200e02d0300c125020366680c0504030700c84445540d1500d00a00042c04010104003d1100e00341c00070906690410182025040c6a07011594a08141e400070302603042a01d6003001c051480e0100380310226021041c0c6010542c0907070380e6948400c1c07507c000703039a0740b1944e0061100c0c03a1002c60006501e46079045580300307200442c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 277298273 1250 277297023 277297037
    0x603061104030b0708040c050d05010f2d0c090e0106030b04050106080c0904021e031006090b07081803010b031002090405101212030f02031305061e07030c050903030d020406 76
    0x12103030161140501d2201070f2661122100092025000e242c10640c031500c40c2c9824074040341c44c0c1700040d05100c512201510313142e5407102c40d642805894070590005141c49c580400da0800b0300b41a0844800e1490162900e15440d480380d80d5003103010b08092400350a524900c0f4841f982c50702c000070018050810858491401c00c400040e040d40113904190044400d4960b4500c0c103c01a0140406940f0400010f016209403c01100603408c6003400755000d410710348600003042d1f15240004102000b543c10200382c801b0f080111600140c0380100b126a2641604401d94bd2002107000182c0101003001c807040c0c041c001c4060252054a0650003028650801c850800840d2101242012407003594003c1382c082481405100b000b05400003402524501c040c940403079084510022a030591b00181c4410b50b00014501c42e13a000c02c541401129404031210b036841d16030224403041e00c1407041e0b0180004081c141c1d80d860b0b58115512490454200c070780058100c0b43d03240d0400b4081c40081d07110348207035030000d480 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 277299523 1250 277298273 277298291
    0x70801051e0a1103130c080a0317010906060806130902030f031c0b0609060f0d0908090909060609040308090c030f0309010f05040e0c090f10120b0103140f0424060306 73
    0x5074803421221844150741c0c00c0c01d6a807a03158201700d04000071420744001c00072440003e1141070400520903014440c0d500d610004041c02081c0340c07200d0040c0c0002d00198240305c0d05000c0309a00c0000254040c0d022282080400c030312041d000001e160ba5080650140507083d00c10044a00000081540f00351203050b0054003040d140c3d840d022555445a110750005081188000c82d00d13124000c0c082140d41d9040040c80e099012015000b00c41c640c0000b200c1d010b030040f8404581f4a84440f41d00e9000e841500500503600d02400010940c40005000a0034810441c0205d10b00c902d0400501381c2c1c241025048aa55020405089680341c11040d0a203000a03a0100b4100c80d4034416801e580450703124260002c19030720340c5004d42031207420040301c0c0e0360030880400b14040d442d03a50710340380420401c0946945002c110b0a001038026a210750202e0b60505080c600c9040d05480249800c5a00a0b8840151084e075111460681180c0c00040e00c2d20001d140707880404420321850303038043340880307200c0e050802c01d41c10 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 277300773 1250 277299523 277299541
    0x60f04060b0706052e03060b0105071121120403060515030601031104020d060603020c0706050c070b0d11030115020d17130f0b0a06030b0a0902060301050111070801051e 74
    0x25590281412008042c03046100141c007980200341c03c1800c140044014612010302418508154020b04110300c20b10b00e400c000b0b01440b4401d110b4051000e01c0c285150041545481c209002c1c140c11280c0079261518501400b4503400c040f48070b2440441050f107100d400c0e600e413040314681240c08190781c034910f0311000c80d000d80705c103603e0845080805005000c6580c41d546031141e52450074114160081d40800290329540302a1044001420594900503110340104840d03070300c0d0000b00c0d0060014032400b04803080356000009514421181d0070550203954002514003c80907100e07869285a92020200002c10540c406000050450382241e003102e05084210508072901e600b90810f80e14107100c110040341040c1090421801c0441c05082c6024100d04c50b5600c100c40c5103821500c10300c81690300c090600c200070310000c0c0c41f0380104180c0000d0011480b04c0d0000b074640d100600c5241e0602c200103601c00c40381c02c0b0030310613600208440c40c001c021600e0125925014036403110352844850b20a6000106e0101d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 277302023 1250 277300773 277300781
    0x203071214070518130b0a0606031a0f0d03020a0c031a07020d051b0a050f011a1e2202190f02060403020d050901030e030f040f080d02061b070b070206060f04 69
    0x70760007040b14111070313582d4031110424080a0212460217401055400210300000000d500910041000090303503841c0401c01421607003034850081c48041c0b007014081550391400034901017006c04031500c0310b4010b42d51606900c1c154110b4401041c038040301100105105030381c1c00c010340c1910325550040403641c460400304c3c2c45000440000c008034105209580340000c4d0041c00f10500e81d1406c003203d614000300d49a6070301e0210507402d1269035a4483e80c901c1703015240500003d010807001e881000b500d90304612031080078400c8880f21402261040c0a41c0c820800c11300c00000520948601191f03a440c00d8540801c44a070710302c48007004982d4080701240342030b100055a500c1250140e010f41001107811004a8107540174000c994100341e00e5000c1707000403000510090070520070007000107503500e182c120720001c0c05c8459800f41c0b140e40c0000c1000c00f00f80e034003c101d155228401802e081c1c034030f000382d0115400390b02407807001900810351034080200c2a90005400b078020101203410210403039074002040152 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 277303273 1250 277302023 277302029
    0x10f06031707150203180105100906080708060f250c020a0e0105060304110609060a0e030f0616050c0703120f090806010803250f0c060f0306140607030903020307121407 74
    0x21285006110f9080c1640c0d000d150048001c00c28840407840b07121215007503d805a80c0070000b00000e400c1080b6188403842104002e10755a0003501c402403034043c905441d02c10090074521000c4400000520704c4040c00b8446407012400c40d0091011000203100500c06100ca00ac100e006a05d5044003168070280c0703030403041c100c6500800c181c2c519500c66861045c1201d4100a4035000f20040c450b40340745648400c05403498898503a516008064024105440c084084540e82100d4001c4028003c00140107140348036030b01c0301c40c10040d59850b410000c6c1403802d0440e51015044101280c20001c3c0140d1004030302c0368105a81e0340f03005007a5280d5141a0b1601000e2240071081d03842048000d064602e076010a100c038050184524005000703d031104031518010040480e201540c0d01c000348080f03500209a00b01032480740c80e003000000c0c103140d0340e036545941d0700c0d1129100c1d11003c205841058401c0880501841e03016054035032031650744102402e0f005400008a4050107140d0b00051140c01c000351010417 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 277304523 1250 277303273 277303283
    0xc12071508130f0317090c030c1005120c04180b040506030f0d03091415010501020f030901020d0c0203101505030f0109020a1a0d0501060206070e040b101808010f06031707 75
    0x2080c10301c1c3c0c1da1440c00e0300c40001c120240725808002030041d41e9024919445085400050720614402d80b080604007003103107000c0f92160b0b461409650081e6404016100e2184a0032400c4000b5290450084a41e0140d0b40c000324100142e03d00410040109030442d088040c0c041c0c42c10f00c100d850301c0d41010744070781c80306a20f4411644080484041c951103600203244030341c003c408061684031180580c9080c0400d000071104800c25490040080703580c1001354445000c2d03007030061401c3c05c1c040070000f5290005100b0301d404002c03e000e20306095660920000700844181201000074009140305a02184820710a5520902581d281d07001801010301440d0042d61b0700400c45c500413400d2042c003040890f40d000c0c03900420f00041c00119400d001c0c0d8840d20f4060071075a0010a8a89170104001700f0544c15400001e024a04210203085ea40d151440101c912022904050101e0070540644c91804082c5a114001640c00e11340c845040402c668421004e9234001c2d800500342c04451410b10685204526000302 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 277305773 1250 277304523 277304551
    0x306060d061104050a0e040b061f08060616060605090108121e09091509100b1b280b011703030c0708041d09010c0e0d060207050c12071508 61
    0x34800d0344200b0b01c81d80ba600c00315041644a0000c9071954415030440d1291080c140e040c081802900740005038001001c485410703040500b050505100c9003d5580704081c400c0c07030000303c1c10954951007507030f00c291901d058841d403480c01410700c400949aa403203018000d00c4907500200f4800b002243d6aa040c8044040c0d46107849282c501c1c62086183c0f110040d00c0c0f651061014098695490003038a0241001d15120045107024208200c49010013174509100c11800380c50400403110980107032101c2c94828030100c0300c0ca8419080d05800d018074141c1d042c940040a034100e48101c541c0b0000c19002074051006c88130f45130b032101c01129800040e814114816441030002410b117010040007480154410880542800ea843d442e03010000c80c0341000b110311008000420401e84400d115000c101d11030b61a003a08000c2c8940c000c00d060101180000c3d0000c2c2e00000c080c41401410002e41e02100b102800551001c2c0c0010803039900c4401c10b008410341103c0060724000402c1c401c5102034010000c00c11500 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 277307023 1250 277305773 277305799
    0xd08070302120a02033c0903070203060405062e1412010203101e03030e0d0f0503030c0c010c1d0409080f12060109120c050105361309080d05040c03140a060b030606 72
    0x70000c80801452070700b148c4810800040140c4086c4902030045100c5c0340204050300b44084c011542008100d0304170b80980c1c0c0c0321414001a030051820b0b504480540c1d26640d040d8420780c0100704100810900103026600000900c92030728400966a42103d10034090141c001480341d00c4040690318a10001d4002040700d02c0d101c4040c5020980304002c0b40c440e16035024404241d907038050443c0c1040f140c60302c0785072020030080710803003082c01081034264640c9070083c011140714000b0103088031340c10324807400340e40d50f40500010002c409048401030060035800c6c64548611580c680072109007103e209000441000300010b03e10040b0000c408400d0307000c400821011b04100044a403034018210042141e0122500580600b62030b0304001c8005d410601c4054803082c144060001030740302c0c2072400901c036281486030004603d80c80c01340c4c2c080c080c1c0700c00017040d00d4445007400c03014885560000790007401412107040c80f015001840070581e51040c1c809200c2580ca9900301901e0f000202c1300c0940101d00c0c882c80c1 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 277308273 1250 277307023 277307131
    0xc03050903070204052206050601091707060e010323040c0e01150305060d020d0308011e080c04090201020f070f030204140f06010e041d0109150207050d08070302120a0203 75
    0x8180c0c010039406c125020640c4403008055242d91018003624100e5840091090550340304845201074100c1e42a03490f4904000081c5666038402403091004008a41c0e8002d0000da1003500300c540c50044402c00c1c80320a02641c59202601007080e41c0864070b80c066210009480411098114122500290b50380000410300d50103402401d03004059a602968092050300140d030b40c40584503445000b650340e84141d41c1001008001220308445030421030003c9e031000c1000c41800031720b1000190f81520701103066200c40c030050307243c4180c1e11001c004500a08001040030b103107248804d400c40b4002c0328140001c00303046044261600c0f050740c0c2050429400400103100394040e1001e180400c9000e40009820081103403401c038100d0b4801c2c0110490794441c5215400d02c00c64045000c0108041d240440c6884070320303035a042d51189001d40316824015100e00082c001d501903030544030180d807a6200c90303980346000149074000354030843c1d100c07603900c210100311031102000b17603408501481000c01103400c503030700b01c598 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 277309523 1250 277308273 277308281
    0x20708190204020d06030b0a0e070f031e05030a080a140402010c060b0a0302060307020a03110c091605192d0912020a1701151703040605031915090c03050903070204 72
    0x140d800580820a00043e44e04c50300c18000114015020018241072480c1d400c000c1c0e07002c100840c415640b00c010144840c2000c140d84800701c90b4401c1d000c014510140445054111450002400714000400e5008040d0781116485118845000042000040050020140003000e84d0081c1c00a0071501c2c0410000741c0340d5100c10078040b0014400e240c52a0b4a50001d0a03940c0100c81c2c1d40016005810301310101a04040c1c101808400000900000800c0b24003088101100400786205002d250316042086030180b0304407104010b007000f07091140c2100f0304010300200c941c81d04858a035420031400881d200c02148141000841690b42c0c41011440d106e5940704085500f40180d038440702c25100050440c21720610109007480440c00420b504011103070302c8131681c2e403941c01030745811240050042085c0e0f02200301c40070340390641040354698407080001c80c1c55050401140045c507250410040d108109042158119038200c141800300110035441141a035a041c1d1f00c4500a51003400032000514150b00 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 277310773 1250 277309523 277309573
    0x14090a0606080f090a0512181c020603130c060e0a0605181002010f020d0b040e0f03030f10031e06050105040207111c081c0b1e010c1e080306030d020708 67
    0x401c80b5034400041e100c46d07007052030140c1b000c400070340002188000c00610082840e0403030310866540c2c0800c550301006501000101c0c00c024810f60001000580d0a2202b0a2304003407603070085034602034035172120005032051500303401c0144a82c0d21110005034403840740040f40c3d40b464400940c40c00061142044c00078041040040806554a8203241c5500300d80700c1c8003500300303810503c001140010820080c0030407150540c001307616980010020400e50300d0008112a0411500003402c00107a0341c07124070071012083da8100505032044005a810300746808200c0900a5014032000c0000366620f81c00c0004900c50b800d00249000142c407c55441031800714109150400790491081001a00381d403403103016400420050168100c4400ca0512010184640ca440b50780c1130306c841d118141d0980140c0181400034506604200711410700d00100503c054072020801c0411214501c8011186007500d55904120b8460340288500c4d42c5011080c0c0c40003561074102c44010b4050507058100d0003401c40c00707040d030807 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 277312023 1250 277310773 277310791
    0x702030d0f06090e0106030305041a130806090601150c0204020c011d07060305010801090327080d032310060f0219060b0306180303150f0a14090a0606080f 68
    0x1002100d800c046078010312103001c041500014035503042001e60780494220190b1010a170b03141c220b0600000790800201c505a0301501e84c240002c520034581000075210340c00310f100c01c0c18807100c40051001c03c00030300c180c043e184010a6542076a21803c0c0c441078601000209400100d200c0464409400c06900034814000500000b00f60120400c1940c0d40101231034600024990200000708030721941440b84501404101c0c0082c403107040252001050a02841c02c2d0050402107014159000000c03000c840d0000d18184050314041019220090010603840a020701d9000701c80d20b004514644131203840d07214442c00200141410b06080c0b013160400014107a02e42544140b44102c00143d0511400090140c401c04010542c0e440784428181013a4001d000e0810f2900304101400c0c42d08008400c3c0c0ba800600042c0003c0d0751070610000400018440041e40e81220807070101090a000380e07100614840c0043d074070f0350b415840d44005041120114400c1000141c0740101007040c0110007010303950002480 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 277313273 1250 277312023 277312027
    0xe06042906130510021e0106080a03030b0121020d0606020a0f060b121c09090b0f10021906020702031e070302101106180c03240c07080a0206071706010c0308070203 72
    0x1c4000c500104455610301001d03031b024100300c10040860000c001c40c441604802444024684400300341d441e13804540040525896001004042c2d00c00c000c0003500350300c18403441c1c200c3c9080003021402948414801640380f0704041e0003181441c00041e4501c6140d40c05000144940e82c0c07510f41e03c0081a8500c0240d038003903810070900c0d0307152004101032552040250082603c8411081c0080c2524050364016142c0c14100b03000c05205543d40c60030355815650544404021000d510400c0741040c80c0100305091040503c904842404215400b42420620940448458291161148100030903a0002065580c89410207100501302001c2e40100301a117800d0460341c400440c00340c0f90402004640e60f03129002c00500c1080e190400300113100c400441070380a000078400d6152880244406070400b801440c4a8401150310b001034801142c0c41d154000e9161034658449031402504c1d80d0042d40c3c5100061003031480308403640f0001500b50b001c0d4105855100107200c0c0742e41c044d2040324000304071354154081 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 277314523 1250 277313273 277313279
    0x408030d020708040e0903090418020d0210120c1d010905060f0c0118060506040c0e0a0b090a030204020a110d1b020d061e090c171203041502040e0604290613 69
    0x16141d640c1d0084140c04061500c1e00d41082c227010031101d4614068584140a407030310f0b4003584840031060721075901950031040303070320000c001551131110324401821400d10700300f91450030a40c04610803550352aa500d40d16418091600119800c03551401200c0c0c0c804010001d826002080e0802480380c6ca40800010550181c40d1003e071700d24140c000c100351030319a150002c10800e40360510031040b03503811a04001480c404880040340820a00d4040c100c400080001c4104581d0382c0da1451800955000f4015550349884210051038203655054503000c0c3d2081d120680c501501130070030703003400655650040c0054a219000c03c00051a81c6106854255031101c040382c80d00d0a00541480ca9048810081a852414078001034840e8042c0d00000d480c01d905680c4941d1101c01240842641d40a49070140d1a92101c0c01c2c500100d034540065512003c2c0b0011700011516008a1060321442d0115001c02105100e184c0c0d10241e40507800e0658060302064185125600d4035030003402c10350740307640e483c5000f42e42c0b = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 277315773 1250 277314523 277314539
    0x8031b070503060a1d1c050901090503060703060f0b0c0a030804060f05040c06020d0c0c270e010c0e040b10080a06170604050c0a0e06100519031d01020408030d02070804 74
    0x4060340c040455035103a003451125401003041121124203010000c0c070f0b06d20991113600d6000b15101440b801040030004e0600a180c3c0719406240c00b0309001005c0d20864280f804020f0010300462146205950040200040c40003100d0145d42c60000058003401481866680454416800034003c440361070f9202c40c2c6450707241891090f940304510034410015003a090031806450010720710121020403054441c498002040107142d032040301d51340c40298583c0302030340e403090f407030500782d502003080783c51030b0a072103542da003005412085079441141c4942c200c9140c40303c107210949031a41c10b12a0004d040c2103100316644e01c90800682e1109100c50009111900c0c3c13081c039030300c40d10b01c000c20040300d600080c01d100620000f030020400d030003c119a0307506254a40111003080b80300003818188034030251501c003143c00d40544111160320829030080f00714903900c400054020810703801701402001101200c510310b808144212000e9911610045003041408402d080296201c1141180c2601007884009002d103 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 277317023 1250 277315773 277315783
    0x150e04030309030e100e090705040b130312090806070f02190b10050a05090c07020d060c170106031514030106090c05250b0a0506120d090504140108031b070503 70
    0x180c42940c02082d10030041c18024a15180213121912500b011990001c0c0c10360480517010500c04141c42c82c100c00e944610080da0076000c2d650184c1825080001c05200d105010382c007030001d0744d100e000c2101652028003000c0780c4214450169102617440480407031100c0b03004030b824038a042410320480d841940b1844c65a40f0401c8021021100254400280025101d4000144000c0e05082e0342401407540303820005416101c014102030342025001883c41d003551140318040f8805504a501441401500b0324020300007034213410280d480c44050070010420a00c2801801945141c91815514603410708203920300c0021728144460f41903580e41800a00c086031800f60b1944480c0a0f01e40e241c6a6092500e03008071004040c2025405501080312500083c2842035180d41201e511100020a590303800089200601b001172103143d9880340305000c1001503442103140c810b503041078a050000c0d413018042410109800c0c00b0ba401141c2041c8800b800380103121940b004007091420480f100c3c1981c5001090801e = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 277318273 1250 277317023 277317031
    0x7080621070b042904120606050a030f060b0f0604062601080105010e1005030604060b0d020a030b0a0b01092402100e07150f0903020913020909250b030406150e 70
    0x100d03401140402800302010b13841d070030220420300b5006007840100d80c2c0904610032400b416000180d1425088144016544000081c020280501164540701d06001d4100c0e051507100300c581508110b850001400d00b4120722102030300207800c00e0304103410010155030f01d00701c05444001001005840104e806c1d49900f01c00d009219040000559505000b10320018000041c0b14405058548208200d0b036200003070103681c030607046500020f42d200448000b4800d101c10301d401075804821507038003000340600c42205034010042040200014805800103555601d020300c01c0001015203c4480d142c07071000d040c1c02070a95403561068401c43d9100b98241030448081444660a039440510305100603030b90900075041e200d003181001840d9110a034402020340c03a0b2070000078000c4900e840822090140c01e00e20100041d4010503020891503c40a191ba03a407400290000003c01e4401d85c2c203101d070054515080548480102e42c503d19569510380c24080c1403a0b1118069408000c20f00280f1a1103009045000b = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 277319523 1250 277318273 277318289
    0x1510050f0612180f031c0516090e060a080f06060103050a1503020f0103090f0605040b0a023a090f020a050f010f0c0f021806120c1c0203100603080c12030708062107 72
    0x548800c1181b0a070458900801900e43c034a1000301c002e40c0e09400c4000ca40c04c032031b0244500d01803540c2c0c05000c0f44c1222455840004288240c00450300000300104100e07115000071f9030f04100ea079480000f8081a650343e00420b14509080c640c2c28000340c10840c0925000f140181800f10303d01826554105504100503429941d55540e80b06020802581d0b90b04550085070b0003134154103000c2810070030f01c0a54580481c64805001c03c00031002d4210302c038480035400780e03401c40080085841900b000080760325403440480c0310341c1c0c4401d4040349034076000b602a622400c060b91540c20800b25000e05450300e5521072004d4501002c0007a03603400507034921004821074410455080c8190406006021034003905402055444d00103a46c400941d031034a0310000720851030400e0104500c0b41c00d0001c0b0b8103100c583d1020715610307420200c2c08414442c0700e5008190054048080390300e050300c2000c0c0d2400f607000603220000003440078004a1868130700014403440d80c820624100c4400c110150742c0750700d8800d06a04c1404 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 277320773 1250 277319523 277319557
    0x20d02090c130509190911150903010f06080303220609031205090f190c0f0b0417030a08060402090609100f0e01030608060f07021510050f0612180f03 66
    0x10494941c0301060b401000c00782e5408a6504105d00d007030101c940703120402481c0a6490745000c06014501c00c44040190014260100200c206c051400341c0360f0040c00c1d0580030350f00b030984403182206130303214881c12075403d40003850035504d5880064124111050803903416020045242010510505c04d5903100303842605d55003a001404000300e42910f400034500b00c003581182c548070114803000700341059020b2103c0f61003640b0a07981d1a060003170401c1d41e00028894441c110010815500180007841551011100405040c0a40302001d5072845000c0f4a9400100701c00040740460500382c001d4010008010903c60410480401003940c603101d203001600044c88402102020321b410078810036102c2400c1ca070601c00281411000c41c0d94803c086c010b120341041c25000903a00714401d10001c0100100d403203200143d800c14900b034152003613003801103c7c4280b00564594070b680c80c00b0400c69601c0c007841d48425501d0344c0da040c840c0f200600c00e90482c0c10a8082c0c907030380104d6820240000d140219111103181d03 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 277322023 1250 277320773 277320787
    0x40b032a1801030507081306020a020f070e01140a03121407140601030308060a0b03010312020a05162310030b0402040b0d0603050c040c080f042306180601050109030f020d02090c 78
    0x1001e13a04050407080038445102c090221130807415009042c120f810480c09650340711244001c83c80d001c82007414445a0041210124a00c2010210b05040f42c45440100301c4040301142003201a0805100040c0a01c040e10a4040c01d07900443c003541d0403a0710054481c0c100300302501d40e5030428108100300c031000c0c2c002c0001401015000325001e6000349007503c580c01d056041c507076101107610040c000a0415040882c000d0207c901c200590400c03198001d0549140c8006218241b2100030300e801a0802c500003082c1201e0302c1040c0e1a0010808007004100f100c03e5540c565064006201c80d608035600103801b04004110210b00c80020010010511000207050703155081c00c2e410314540d010024401c174280368034005082c1c0c2c0000d055400c0460024618500d80360b80c42d00b03032505801959451007081c1401c0102c1c0300d1610102c2c2031403240414501504418000c4901161914424042c441c0071030300480080c03000c039292843c800c1c0090710182c144d080850013a00066210710084808540ba100002100703 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 277323273 1250 277322023 277322027
    0xf0307020f030405100309060e0a2315072718110909040201120b0301061511060405030a0c08090405091c2d02030d050f061203040b032a1801 62
    0x140c54207409031001d98107040c01c01c8002017607522103c42d09400c06846030700711030600c00190710500980c5031542c100c1c1c0e540011403400a0301c04251410054180d0000c140e6a1200b41020808464645410a0f025255921008203079981003103c412140c0c1600d2b0f81c0f40300e03001305000003c44409804404031745050101e10f203520100b40c5929403004003204906000f1600c880d00c0c2c6070034013078000e9424200a00c042c10341410100080031050401a819801d10f200054100c510b4901c0041d190001c0e40d612003d00b100799940c035998082990300038542e6104000f04040385125082c207540081c071540006240240b00b000040503101c0986440105402001340880c000d4102c006a401c4802c83d030030001c0f129003114541c4200140318440401c6040c010302c1a00e05400d10070301c100c80d01078020301d20801c018100810743d40c3c94080b04660301070140c14060825640c0c0a400001d0310125001100312602e1540c441521031006814681c40c210011094404008481481c5014082084010281044c40c110389400 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 277324523 1250 277323273 277323283
    0x91203050115170c0304020d0c0e1005040207020109030602090a03300206010e06060d0603020303031005030615031903181d150102190222050906010e06090708060d06020f030702 78
    0x9075400b406009a100080c0504403142940d10411040032130381c0720f85d95800882d641d12150300000340903114030340340442c00101d01082a80130340c0348040507905140e190b2080c403040380f050800c040d01040011030100700181480d00208040000a0240c0c0b0840d82d40f03a41e0f140061340c03410002401718000e025004511420400303404010700c1c40f840240702c0c1c0e5241081c82c444640001d85034a0183d000020700403030303c540381c0e04004011980502101d550b4074041c1c80005500348607000e66071003801800c002c11503921614072400041d084c0100a001840c190110898074460110400c4003030181184032000c0540004242c000140080c0c2192105241c121008a55903e001402c22000c40e64403d00c541860f64000784c07002011040401c0391071009481e0002078141810281580009041e9584002001c1c10b0350b00864041c0d0700d901d0840302d82e030340c9911103403040707090480f086600715003c2c40000340d03030a01c6503403da0340020001d40880c84185851300c484090381e012441d2098240800010302040381d81c1000 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 277325773 1250 277324523 277324559
    0x6090b0f0301050f07080c0f0c06090c0303040b090d150525080c07143c01020a170c0c0105041208130302030409020f09130e15060f040f0912030501 65
    0x700104e28150041c00c108420240030b40f07007000901c200151500e0720002c01c40304008102d0301c14544400c40e081c021580c615040312078030340318001e9403650b03480d5003000010b80c2e01342d500708564541800348070405d0020301c21451b40c003600c9812079003241d502e5006d4584102400351a00c0600d40a40c00710300d004034011582c8210940c8200000c0d00100285c40000d50151030034658042841c4050161000c0e07403518005002c1c0c1d0103d4003c000c0200b103466040000727035903034550030012440092911861070043c00c078001c94164030045200211003001d109036845805a000806000c10790805944000d03250840e14100c5046401c005080700f0102c00f1604001425800403551000001c01a0345590094482c0214032031080483c1c2c001c1350288a0543c10019600a00b00207041076014002041148000d4103064101f03d080d4003401541040d8003000200076449038601503c02c4403400400e005100c018111403454003501550340f054400010400b038031844250f50107030340125035541040079800038850001 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 277327023 1250 277325773 277325779
    0x1816030b04110c010c180509011205012a03060608010b0904150807030606171908091c0f030806102c040f0605011e0207030f08041214070621050a0f06090b0f 69
    0x70401c000a60348e0502c02030564080c0744005400300710070b1801c0ca0242c90610ba8039174044c1c50020003038030405613070b0350138370792004080d5020700115949140a64078404280a07841e04068208207030449414140c001202440301d180d040307103c80e5542d00d0f031076041071916041204d419881e20820085d450451780d19090741e80082d0040d00a0b40e00414114034107004d41b45000b89803110201c0e005400b50b07030b800103d101c100f41c1a040d6504640b12840d0811284048080c1180860303506400706100342800d040d1440803440710740b01d40100b600c80d0480e0a104078168200c5020042c044410004140c685016890f65a40340c42804141c80d420a0000b501e07110041041c2d07010b10481d41d8581c1c007110350014120040301c0d00301e10f220981060f14145000648659002032641a03224048a0201b0815038070a40741250044260744a035516400c04440701c04150320004c9001c14505142407005505034003071074212394040000150700c204175008000f0740300300d58000d85c00f403541ea501400071030810000c80001c0a50407 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 277328273 1250 277327023 277327067
    0x30403150c05030604110f0f1b0a0b040b2a0903010b030607050d0515040c0f020c030d08181e0709110309032d07111816030b04110c010c 60
    0x3038000c1c61400000c110071700c15501d611030040741409850440d01c0000e94406d849903a02d00105070b0344078941c04180e072440702100840d41c807400c040780070540110781944421150483c0d01c0f00d0710740c0c0d0741402d40a0000801501840c80c00304040c00c00c80480b40c0800e2000d40c4e21034a41c20190101400c4454800b44103009800070420130050a034420100e58040071160380c0051943c0324180c0940040c072822002c0c58000c0e2422905841382d682004500340311081c29422608103000708014182c0b983c0141444d0f201249100d404168400364020200c6070840d004022546035a544141c036003c80700d5203481850641c0c00802052008901b80d009170321020b440c04142c14074500305000243d07503c0c802c15010741079140c0d6100d820401d240f01d0850074110000824140e0b41c4a0b01c15081c94006c40140d002e03241d20461000b041241250601c84c0c04c030340300e00d0000881300d4964040b15015400b40c01d8040742c6d2640b180c1d6840c0083e0208203d5009001401008400010205207603600604021500d8824100c45402 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 277329523 1250 277328273 277328291
    0x20d09060f050d0b060f03040b010f12030503090f0a030306080114090709111c1406030c090601180e0a020315060c060601120e030a1707171305160803040315 69
    0x1c164103440d003200c1d140581c3c0c1c503042c44000e070340200204505250b02241c00146100c1e00030580020710701890103803507100b00f01d90742c40541107102e018030700c81d019802000c09082804280242e014643c05440002529449041290860304003564100100e010a83c0d41000b8450f0706024030581d03140050a50f11036a860038a460f8603596038200780301e000e2a20b519990421103004502065542c84000080d900844030a4071103004007030900700c2142c0314544007a00000b1a186000102550070f00d00c080c2c00000b01b51070f4940110369101250201e883d9125012200088132441894076030f02c550714002700142c5070704100505001d10380040310f041c3e1141c1d005001c2c25101500200d00a600080b0034203003201ea4504c1c1c42115400f408074517485c2041400041000039006402600c2c0700b0010481d210120703136030b07a03840400352800c11342e15214103da40003c0b00019a040d01e281040c043c414021001c40d40d0344d0f50000e00145c3c2d0350a554100c0e40b0070707410100d410410042641c48c5441c2c030700901e04091040b005 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 277330773 1250 277329523 277329527
    0x1090b150103090f0602071115040303022406090a0b03030a020304080c1503071b0c0306021306140d05090c0306010303090602070603141518070e0a17030a08100e01030c030201020d0906 81
    0x1100700c405450194000780360808c000d510036400900c1c02001d441301006241e6102c040e41c1c150400d11056002d0b01907101001c5140707415581a401c25481c00d442920746440380000e1058146c4010074006a40760780d0281c280b0141e904001800240d00c4a60040d80c0e620709005260307040000400002d80034180717148810114800764802d0741c1d070104044ca0700d804035202103a94107042284241004d002503078000408014410190004c001600154828440721565000f00311040400c091880b08020320522010204d103800b90032194104c1004c1084510f220070020009043c0442030784202c0100e59040e40410445405002c20700c018162420b080000241e081c60f0348128010090140c010071000c2c02c2c48000300d58400000901b02e0401e207080d60f8407894003110240440c903040d10064403594400d200082c1c402010860b61050101c0240034609001c01c070301c415a0b0390170700503000c1032544010060100e17801c1d14000074903000314024650558950701c3c500001e4103220400329a0b0040107000c0c00d090190340d07 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 277332023 1250 277330773 277330793
    0xe2508071d061c0c0308180901061d01050706060905010e0903030705070f0312050403030b1c021503070527120105091f0e010e030712050a0e0409020d020301090b15010309 75
    0x1c041c0c58100344201440302030f40b410306580c100141250011000030091108220141220510b49811011001c00c081c04100c40e0300001d10030b503000a0311003804e40140d900155054000da10b0103041142c1412010340d615401d076401d640200341e005540da80100a4485010744030340d00b02c11340c00061440d604240c00010180d10846401500403003c9002c03002c2018492940480d4010070000200402e0074940744c01000750101c6101184030b40198162000500000210021007550080007030074041041812600d080d00020716401c00d02c0000c3c824030b0b000210010141c0103403140000d988050160b01e0301081017042d0601001130380c1d44e00d0a400c0000c50180012081003480342010030300461040000e10070003500756404c01480f994200500c48424080c008003400c03016101e6440c4124405032101e045405010b0030115000240201e02810000e04182d804070b2001e03400a0105000c84040b600400d007582d0b120382045880c0311047c02080903002e44058002066142440c040c054001c2c551292038040c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 277333273 1250 277332023 277332031
    0x2040b06031003020906012015070203040617060402090d030c05060c071a090f03070506100b0c0d0f0903120c03030f0c0c020909011d15070207060507060e2508071d 72
    0x7170501d090102d007890707025420000700c1c1c051484074107842008600703140f0f440348504011195081d41d000d0201d00c145c0d0000c41a10280c400d141d6a0110b01001c8005401c1e034624060b040503003295003002010798030380319034080308241402525204e03070f4040346142240c075180c0020f001c0c24010f03905100700350024040200d030441c0d0f802104011001d640703d2130140760401c00c0703c9290f10710701d100003e40308040100c045102c0c1e1198690760a103403200d81d80c41c6040e8042d44a01a07400706250032211451042c5406101280c0122001b881d103c484140c0f41e590f00001540235190141c08108108074841c10503500d8055155002400201885401d0107001c0c080d04c2e40c801400c00030300c5040c8000005001c02c009500009681140504030280c0804104003151605c05101070b404114001c0c0c000281a40e000040e640211901c59842914201c22070b10385400515000d400c80072140280540d0320309080740d81d80d0365800900c8000754155a1898000481e1400c1c8407584807583c2414070039103c480845241c1c1c801030380 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 277334523 1250 277333273 277333279
    0x60114090a0f050109090606080c1c050a0b071215080c01030911030a0305030106021203090a02090a020712180e190905190303150503150601050a05040e040f02040b0603100302 77
    0x41515100341e0701020708040303415111030501c1c1c00000a03a00009821158965018038810003c0d070b07031201c4900d40c48420003400d0b180c000c030004140030300c40c407041c40780310201d00d0107182914080c040710340c3c6010081e0401d039103500000d41c541c0d00441d40c4a00500ca1008007503e07200b101e0886d02c0c548001503445d0200b000340c0740d05266580d144d210601c0705140407000350070002810341d00c00754220b02c0c01030410b40080c054000103100e001c3c46114405800f034101c81c0900c180303500a241d00f04643d420060348650040c45218241d800303100440005080300550210220203848106078000013140003214445507a11503a1501c02100c1030000d4551804201038503203c142c0300110300344607a41051071402c2d058000c00c564103074010900d1750605031300d64002da0303014074101000c010080d621810960755518150310380c0c0341c204000340030507200e6004400400b0181c4140c100f05003030a6072040d0701e20400004071000c0d582024012001070441c50288924442103808503103031801c50421056604043d0320074040240 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 277335773 1250 277334523 277334539
    0x601111015031b060e090c030115030e0f010b09070f140a14210c03060117070210231e011202130504060b040b09061c0c030203030304051e060114 64
    0x8200020a9a0800b464225030680504036542070220018040d6106401c0020b04800340a0114a032100b03a03e4024009004811704690074500507d1140c80259540001d06990325050f8001d84002c1c170a60064030700e9580000b410010310818042c00b440010300c0b1008005100d40c070a03d2117030b00682e007090100c3c0200807050f12800e05003826108290b81c10803003c121440400c0d11800c007038070f00602075550724802005041944403c84810140c2c0416181c0c140410320040302c56101031005241c0d203074442082d1040714a08071000d0380440846a0a60317101c00740740700041c10740000c41985070340d05410400b246c0f650080001c900240059100041c012304a00c0c011030160802950f03101d80b0001c44002c0d00d00000c0020b41000e2400398018111200154001c42c24181c6101c000c1c5000c985291045001130b0402190740d64100c89900c0307090344c0d43c100301d4188024200c0800580c80401c09075120714410001040e00b50b07003043d40285261000110820141e00ca08014016030758840150620f4060a0750001 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 277337023 1250 277335773 277335791
    0x4050606030c180607020411190c020112020a0e0a080309031608073c18060303080604110408030703050703020616090504020c190c060314042303040306020d09030806011110 76
    0x25020b4440d01174087e50140c1401d0340380c4a0928180c1c02800000c10f00349030030905ca00c041e28142c508800340030b0027901285071640380e070040c1070f50760b0001c01c0550500e16182510050b05400030f10300e187c59400101507a07101260070714040c06c1c208403000040507a003540e504064540000d90741c0d140100e001e15450074220311655401c140344410302121805020104503940401030314800c2c1007a42a2040842030700080c008c203c8808030b64852003044c1c80e01a03454410a0b5030340000e020241003040903c98031403804100008841c241030016000035842aa265503a44219050003803071300c1005005d008103810001c01500045400005034021640c05950140c1c81c0d54108584070309100e6001c25030b0111440c41d60240080020340064a0152a05510100031225000065030488038049400400440a2812542c1c0c17040c8100907903501c100c001c01c110382c0ba0a03101da40b028142d806c40441050507a0320f9481510816400c54009540154281ba20041e0180b03501281036450f402440140b0050b69906248 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 277338129 1106 277337023 277337029
    0x121e021002030c070503030f0402010e091006030b040902030d0c0605241306030f0303060e0a0504081902010e0712060506010905011d040204170c04050606030c18 71
    0x4140c1100e20154540003580090042109141c092101e1000900704000840c072030f20781ca4a140990f42840d1001500c000103543c0300c1440313003141d44100001095001912012981145800301c0c0354840d00e800b1034014901c03110060340500032504c65a52540d0002110300340740c0c0c8542401c010999503242d0070700740e075910714410344004070640a00360f6003840c10201d010304010000030000348190340e07950b035140c117a28800021404641ca07a80100219203070724015607403091401d0018440c0d482c02d075a07002000d00c03132a0ba01c0302c2503a94052420400500c02d500c2440b012800e002150361071911004480e51000b040d15044400505042c001410341d446501807608507075040c3c40d569141e41a901400c600c0000c041c00c0c840e0080d900340000204106040300b85851050940094070025110f2420f100c26540020102401042c0c20402c0c8003e00c5419411220b00c00700c0018011103d004c00800 = true := by decide +kernel

theorem cover : BRFrame.Cov 277158273 277338129 := by
  have h0 := BRFrame.cov_init 277158273
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277158273 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277158273 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277158273 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277158273 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277158273 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277158273 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277158273 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277158273 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277158273 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277158273 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277158273 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277158273 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277158273 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277158273 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277158273 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277158273 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277158273 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277158273 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277158273 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277158273 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277158273 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277158273 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277158273 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277158273 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277158273 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277158273 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277158273 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277158273 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277158273 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277158273 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277158273 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277158273 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277158273 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277158273 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277158273 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277158273 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277158273 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277158273 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277158273 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277158273 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277158273 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277158273 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277158273 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277158273 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277158273 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277158273 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277158273 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277158273 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277158273 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277158273 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277158273 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277158273 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277158273 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277158273 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277158273 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277158273 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277158273 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277158273 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277158273 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277158273 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277158273 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277158273 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277158273 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277158273 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277158273 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277158273 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277158273 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277158273 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277158273 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277158273 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277158273 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277158273 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277158273 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277158273 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277158273 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277158273 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277158273 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277158273 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277158273 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277158273 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277158273 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277158273 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277158273 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277158273 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277158273 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277158273 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277158273 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277158273 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277158273 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277158273 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277158273 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277158273 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277158273 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277158273 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277158273 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277158273 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277158273 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277158273 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277158273 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277158273 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277158273 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277158273 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277158273 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277158273 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277158273 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277158273 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277158273 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277158273 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277158273 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277158273 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277158273 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277158273 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277158273 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277158273 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277158273 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277158273 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277158273 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277158273 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277158273 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277158273 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277158273 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277158273 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277158273 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277158273 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277158273 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277158273 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277158273 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277158273 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277158273 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277158273 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277158273 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277158273 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277158273 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277158273 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277158273 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277158273 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277158273 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277158273 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277158273 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277158273 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277158273 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277158273 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277158273 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277158273 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 277158273 ≤ n) (h2 : n < 277338129) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
