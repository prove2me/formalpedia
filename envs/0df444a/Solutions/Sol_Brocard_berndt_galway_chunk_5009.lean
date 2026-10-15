-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5009
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:26:46.966399+00:00
-- url     : https://prove2.me/submissions/21d7d31e-1915-457d-8012-c0deab1bc8f3

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 900719424 ≤ n < 900899280 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 900720674 1250 900719424 900719431
    0x2030f0a090e193c0204150804030806060301420e01020c06070210050c03070b390a0c05190b07120e06010911090a0e0115030e030412020a0b03010e 65
    0x550b803901c3c4130000b000e09049498000c02e08280e07440a4003040407490f0211010180c0601250036400303000c00300e19030b0380c0129030391181c0c0000c0e92010494606801c00402603000900800d004500808c010311204109032420300140008074041200b0103282d0840d6009041c06609940c1e0100c0030307900300020310780e03c040344001d80d11003682280e0164a032030041201c90311508030000d61051a5001213641d1501410190a40b40e80c0001079900301202c2c0e8968244585044641c146083e04031044a9110680c0f000e4180010140c0041d404030405a554005807a12540c0c403164244045000345c9801c00008008482107980f10806011380036040346842040b00e03406a424001041c06c00c03400850221044c801d20a4008000b0300400842e40b800c4d20800052890794040d0354401400c00c0040050346504105200070804150748507078962404070b0088030082c3c1407001408050800041203140d207000400d8505540340040740802030419440086c201004170340c440541d0040110000440950142c0e00510 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 900721924 1250 900720674 900720721
    0x30a03240e011d01081005090a080418110a0e121f0c020106060c0506160e18040b0a0e0a020f1206010b04030201020d08070210090804210507140102030f0a090e 70
    0x10703810044083c1002e84000d02840f4903a80c04020a241e007560705421841d00040307450241c0b80c1c20119600c88191607801500040c41d02000000c4451141d02d03103100b080001040c001010382070031415240280440302a410709480b030891702d800c8480d1040144009021b21020208203003102c1d0f1005404c4014002c2d00c00c081d8059440c01400040141c06611902d281c00c1d40030010b0b101540d901340b4190382007000840c088080098490b50144142c5a6404440b01c030359903040f40f9046803815160003068030100420180000b82491103008422000103200c0034910350495890034400c1c3c0f200d010907a012400d00b0301802500c25a000024244400b070000c000741c84c001e0f4207698140c04101029500b200043d81c45400680c4603610408000c46960f222040040c8140111490140e80744c031459400d0301c82a0040121480303000084c2d0400c80104007003001803c442d1001140f050010300081c0d102d018400c00010625000610783e0701c524814a0781c0070203001010403888003810104000d00846254814026 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 900723174 1250 900721924 900721949
    0xb0a060506040b1c0204050402070503031f050d230106031a060a060e1011070b04060806031504030809031603090503010c02010506030c060d11070809090a06050102030a03240e01 78
    0x25107041540c00c41d416120052056403074464041e4041e00054030030804403103840e07800d0001180e965a140000d2052038050710043d5228186151b408030404c4d011000c10304618510102001107444000c6018450754200e042c1c9040c80d040380440c3d01108404c83e88036001075290000c040304002681d140c0c2c00c0b00c0ca40303030301c1800000da49180502a000b03d060155101061140313120341050302d86031000e01c9040000f840e102c00352075202102ca0386400322507082034505810101d42408050740c440c104950181041380140004074107548040d07003010001c0c2001c0c0130010040000b0701d50070410401c50f20400700703030340120110001d035080c000c000b40c4444c014940720f5424091501801031050292030302989000380a03085180c400010410030340e00040c107841c420368031400c100030341680c0d64000c4e012072805001ca040c0d48001d2402040881480100a4900e081c0341100600c403690340042594500541030a00184001175405c2200034813001c40403200140034800c601082405000903141c1c106d668122890 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 900724424 1250 900723174 900723179
    0x70f080a0909020906030f06030f010501081e1c0c0228060e04020a1d01200109021008100618230a050102012007060b100201060501120b01080a150b070b0a06 69
    0x6506134031804007400d600107030510100d00d90302d0780d200400c0c0d0003a80081c200c40b103021042c0c80250030355000346c0c4500a550040281c0e1f00395150702508149070144100040c01e60a20503800c1c1b00c0c8829103004e92201080200d451482c110b40b00c10101c003409808071100c62108490008842d10440341a004210005003410083e070034509050090341c01d6002d0390740351180c0240d00490030800101c0b4405ca41070410003401c05514200f4424070161501039045800800d106040340180b0010241d000714a0042221106c104407103100e02a5401e402e85901c0d01c0c0ca031008112421450540d0720721a0042c0e14460302d032451155107510039001da5244108141d480d000300c25660700040e0700b21079104c01201040800042c54411321501c0100410120f40b00c1d400004071924248041000e40954074004800350b91341da04207100030341e001041200c1c000d008036000e010142520700001e01014001d8001c00c0110340b15543d440e403814800410102038540f05015649440c820b0906c855408002c2e5040b818a40c40e00c03902 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 900725674 1250 900724424 900724439
    0x17150a09052409061201240518010305100504080403020603010b070c1512020708040f150306092711040f140c040e04020d0326090c1e01030207030302070f080a09 71
    0x10290b0030900100700c07115541d07558003801035859601c0c02401155503100345000400c000c05440c0b44660640c0305011045034141803c0c07096019400210b003940340d6410004000007440040c45015101d00311a0120b40b90703c90b460100700c1c41c09140c000a40c402000700000c038140003203070003420b40903000c0c002d00b0503415600c00e06421982d1003041d11000040f8400303110005a0070310f80003003c0041c89012045d241c603030b0f41c00b813607a0760710714581042c62614852901803211075030600036200038025201041001407521010030001000c103510910842032700d610303c80140b0410400301c0b030656101420031f22410580502c420010401d80f900807007444001070108000030703195005e41d0f00b503411b8030094410a854503001c101e000303d40003c040b03042000041002241103c5400401d0460100244000c80c9040600e041403e0080f5240c0172805640c040c0c201c040c101c640c10f451417158039000c0c20010790f00c041d039040c00c4001e0300c20214007a00c03c1c00e40000304010030008000801c00580c0ca640c0740d222031351b200e038803 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 900726924 1250 900725674 900725731
    0x804061d0f060405010302090109090612020108180a030f12060f0f0608150d020d080c0a030905100f0305070e03190203060c0a050426010504050f010506010f17150a0905 74
    0x9086400c10b00501003441254003c2d4028003140324141090340101e82d5402c030342c03000c1c1e401ea50090426425041c850104550308080c800e508420310182290107941d404040340e948440d0b45402408201041c9401000036014000c03002010703d480308140465034a50041e600044018400c01d43c0d800040701c0002659442112140d01540d12102d001d000d00b09000c0c01c01000c4445c0e000142ea0040c1500721400001d6100300c010003244804a01804956001c2d0401038070785041e40c4c1c402c90042c2442850203e01c0b80d40000368204c450f40c00e090010305611100d40c00c82c0c0d0854105441a0944510b40503900d251009a2a0b948002e10860444600744d80d100d84d120040d0207008540350102c6d000740001d104000c000427160381031400e0070061720b840c070308442201e07800d6130341c169425030300e6411440b070f0440c0450082c01810b511220030b003400d5a40c0d1480000040500d0503441c468104c03148554003154034441c2c000d210084841004100c1c0020036201d0717030349900605007540c42400d21201e00500a0b4141d00004 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 900728174 1250 900726924 900726949
    0xa030507090e0f1b090c0304121d030a0506040c09200d090210030207051e0d030b0f06130f12020d02040504050a06180510050c0a1b0804061d 62
    0x901910105160480075000b419a42c05214018012100d402c20912010000c480c010901402e21a4a020303042052114005001c1c1480c40c10090410811000c20305441c01010041800c0c0b50030703445c07803014014800303c0b02644010150301d4090708a030b14007440400155a40150b024003000c0c05400e54402e010002ca5140b0322103031b00ac101c1c4001a00248400420191400900f58070004c00c3c9100c00e6030000300124041341d240d8000ca40d0100d40501405020040b00b103288103005400d00c6032455202d641584c0c2c00c0d0110b4104105611444401c0c1c0c9521850290300e280d14018024640b11004048800304048442c0200c590200c1c0d04140060b2400e10607071041180e0341c01602404403161a5001e204c081c00d4001d0080d10741307114404015000451601c00c01d201101e09080c5407050740340520f01281441034901c00814454100000e00c0b00c14800207040711088500750800c0c0c030005600f840c15003006000c1d40000382c2804004580000c41c250000d170000384d0b459014841030300240308502041001c0f000b10 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 900729424 1250 900728174 900728183
    0x40b0a0509010e09030f030a0e010b040c090b090301020c01140f070c020108040602030c091329060f131e0504050705131e03140d180b1206130212150a03 67
    0x140c01001840400b00362180c104d40c842c01600d00c1c1243c1119194a154410f4400c118903650766059181550340c02e10502c82c11510854080c400088480030041000f515405503415040c0b0000d039072aaa030b54254119171040c0c01950080c001d482400f0308000e107081044a03000d892000c8000050000c6108903018071529905858510690b200c5e40c494200a4000412207071802c04200701c5040f060350b61056803000201000004100040c00b040d240582400600c0d4501042d0080c00850204c0c6e9503030750665a010500d1300010f0b84510f1840304490081c03150350700501400c8131494401d6840304418680740295103041e6410700c200e894003d0212031a02c00d82140d600c8464100005000440408d5084554003104004c05244942c90740c955800f210f02c01c04902010741c3c02800c03d164150740081800340607241c1440401d1156203443c038002071912512030344040c40030303903080042c049540d542d00402d43c40304100c004644400c4071210300f5003203000c25920700c0c2007144900c5160116181c0a40c441041d00d512 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 900730674 1250 900729424 900729439
    0x10803040b0d0603050a050609070b0a02030f070c050d03050414010e01050d0b01092105010b0108160e0301020d021903061509050f030316030203040f050a0f030201050a09150e040b0a05 81
    0x80c041c0303540c00c64001000c051081c545482c000400701e1010041b02001d207020f00080c00180c18941030781c03850804036034485400c048050140d4040d09401000340c4440702d99800745195501c219140c40000b14500750400b035402620002c0603424550700c10302504c01d8a8500313500d50341c503150280042d41c0187e00000c1e45400110100141140b111319900142050038041c1055541651641c00040b12000e11201d01018003211050200500400b40141070040c002801c0c03035940c0b41050f03101c0c001d00c840302c40800800c0c04200010520561000d6044642305c2107902d0046440c0c0c8680014403c040d84c1c0003105c840080c2c200000860028020300c4032424402081d11421104c81c031308001e2009e209581c04005905002c10b0200b4185400d10f0101e075401240710740d020f1070f99141002914400351480d40c000a01481243e08280517103ca4055113105503a02420501d07181d80d65071008a61600c243d41110110601140345114000d41110f807d0804440469060001d00000824440c11460921031694001c58 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 900731924 1250 900730674 900730679
    0x14120702040902040e01020409151e170705031603060b032806020f030a02040302190303020a1401200a121503020f1507110a360204090603051506030601080304 70
    0x405034040b881c614406400852010558010305007260000e6002c0c2c1c0483e5203030b416003030b1140140004540540341241001400d0f845034403c0002e10a081d0081864461007000c0c0f1240c500c008001140003800028115000d900f03011902804141407444102d4840d8208500d1200c91725010620184e04c014084a5074030320744990780480348012100c6410f03200268204840341050000c40021841244409005650781e841c40c0305012041d00c4100d4005a140d603000c4044c40000e50104903044240c0d0004c0300c03490802e101221050051441c3d2140c075140404010b603400ca0150a5400b6017030075020750f01c4040a0328540b186000954616500070300c416400407c0605c01454086000d0300351945c090110040526000c0c2d0500310b41d4072460341a02d80c0a003191043d1140d251108110b8084d00c01250036412114500941803000622094041040801403180116072041c03581a41c4c010101c0c0da0060105a50300e040c2551129007450301c4202c04109640025020308000601c58100d8601e2001103240c140f = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 900733174 1250 900731924 900731929
    0x6010e010504050901090204210b0a051b19020609010e101503080c06101205061302130606081006030903080c0304031209121812020d02040f020406050714120702 71
    0x48001001418040d0600c00412592290350616029280312540103a0b1241414100c0c00181c0030010f00300c0300c0160003408240064500541660001c14080740862540c60b503ca81c14054410400d881c0f118802c0445c0000540320005407036420071035280c0954541d500d4520489080e111001a40043d991054131017030f18156580c0e001a00050070340e00141c07242d9403607566455003607200c0a501102607000105100c41511158192401099030225440d0840069618a616801c00030040d195602d1a00092025512075220140361440b81c80c0e802c0198070303110f40e809011514141c80402d100080400c01107081e6000c2c1c07250031075040e050b0b10b40800c6990342d04520072460740010012420800e000309000c0071007040303000b188d03ea1441600d14085000b140800200482060f94045039035011800f02046082d207032035000c0c0c00c42501940c4400510b83d09002081c080c140c1031540c050f4542c800140003035120b5005002d02000341c801e0700c003090341c540c16001c1741c0d0340c07003151414a05221908000000062 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 900734424 1250 900733174 900733187
    0x626070314100b16081614010e010b01090308070203120a0f0e100839030402100e060414031c08090f0604031b060905060406020a1b0b010603090203100903170c120601 73
    0x11846540a00d00d4000c1e07100300d0500c40d041401e821510028850300721010200b089c003410000368a101c00812121041400007420a0464400582207941c00070b41c05003503441c148042e0424200c01d82050390780315810f4000403c0001948050f40c0045c0c1c1301c45d03d0000601d001c00c0744d10005042a0388070b0725075455001c0c10728501d29100e103002201e4007000740d0140121031403400031141d074400409000d81364a854014040c02e009190070000c20080017030398418103999003200352020755500e0b07002c0c0b07a006044000820f160014000c208091804219a000269580f141800341b01e00700e810199025004820b480c41d0b902c071002d903001004960007002181c0d10710011241c04c40c003940590400720341400a40c560b20300303080c005e860607581503400007070320160903070001110094a0a01911043c0d50101e036240c401901c0010b004500801d51101c2c810000d40d981081490032040c0680803c1211007010f280151420460a07541403e0703801100010701609641000c0c1c1d0030080c81061011741542c1c4071001150700d03 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 900735674 1250 900734424 900734467
    0x22e0305040812091504030309030e0108130809010306030602030c0306102d121e0b012c01090e0f0105040b060c1e011104060207030614100626070314100b 68
    0x31881141900c2d017a031800b1050a90045001c3d13103000802e588642001400703040b503d40c00905120700310f4140311040c40e5143d255144e46030004840c90311000c5c0100120050700450344060052800030060084040001000794010314085480b0710512003060380a407030040c9800140402090031306107030042d240c44000c0c448210305240c6082c1c00d20a800c00001c80450703410b408043d101017030142c402c1d85140b40f1485141801c4030242009020114040c4c0c09924a254619840404c402e1140c0e8810f40e69006a211102810301550505000c1c84e128900e0440140c00744600742c860f5040c4402010181412030480d4010121840034000000070788a14242c40c00110940369030541da1040d180700700000a034080d00141030240e024100492560a141c000e0f10a038412000451010030306100d80c1214031030501040704c5090400107403510783e100c408082d0106c0101c52909040030382c0200901143c3c198803074440007a100c590050980c548080031140301d010342c0031b00321881604200c3c004172107103405000c204 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 900736924 1250 900735674 900735691
    0x182704110103020904090b0601030c09121e0606082a06121312202407050c01050c07150c0f0e060d0c09030b0f0c09010c050a022e0305040812 62
    0xe0911a80b0101e0112180720005071104541c1f03d00340440756a260240c80070080142c544001c00314186042500701c2942e420300246007003100c03180040d0f031024015103401f05540120082041d60b90341d00f42d00d61182611503214044c00c95083c51044080030311041000070f10400341c050750404485501e0b0400d08400070300780d0111700d09807925500010f0758500d443e000b0751219941d4104011002c001c03c00120a541034070100c1d40c0c0100c04a403141d019506010071540c0b181100f11107145c0c9070000c090300e091282402c0750000b0b500707000c20042c80707505010003400118802d0001340e203034804069448044546540e44400020403200805090364440c0c410ba0f8980078005101034a888200fa580104650162681c10080f5421132010414000380c0100c9980c001080e99a8007454648499150705903c202c01d81a4107010740651450b060020801c0760810705a80508181010b489510384034000594050b454a1546086103407908183e20034000c45000315030000405082821303d004044009500600d44030 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 900738174 1250 900736924 900736927
    0x1f060201061d070e120106140f060904051b0a02150a0b031f0e1006090b060a1e03020705030d15060c050703140c06041805010510020604150209030318270411010302 72
    0x413003558408550500e50100b07000001201450040c00e440000f040511540c45441121034000554550004450101c5002c80d00042d0a903a1001c2c100708a1a1084ca4001040c0021032122661a000103610104030305411544905643e0b400011003078a18103a40c00e03403d90000d2840f010341c0b00042e400100107400c490000304011402e41d483d0340ca400d800c5640214400d8690350300700300b0006075105801c1d4aa1090320700c04e1904111880151080300c07240e281c184034510301202d40841c1071013681074980d641c0e0300c01c046d00e0360f464041d0841e50260000007401d03d40c44548e1103001443d01d00410851003003d500c10058a2140d146460320304070040f0f1400070454600554007000000e640d02e01c0100080c04060345207440c0040020031036012902d058102d9030090f4403041680d58900e0b00010350742c2e803156215603004115002c54511001900862146a405100c042442501040134410481a0300b0040d606580c020a451100007a0500388603d500c0000310454049400701e6007113211002103103410705015 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 900739424 1250 900738174 900738197
    0x120d0b092502011b020309100903020d2006040e100806070212030c0403120c061802010522080106141e09060118030506040822060f120b091f060201061d07 68
    0x14490030440c4d141d00005810000c1e09002c2450000042d48285031185080c0d0312480c11079000ca64000401c1c00044d10030b0342500011002c01c500d13241080c002c1f42000d013940361510b690705114543d060b400e0354031211903150000049529440001d0b0f043c40380c8560f03070080420082c1130011003125071000e130043e04200402c110120104600000c440103000d495650860415118245070741181e0740039446010041140340803801603a80a0190390f0300c5889250708911000404900350046030059009040d00e5080400008400036107881aa440030350540c1c8144070242c982c031568405a5511307000030383c4000074001007540707035108501d45100300c42c104681c00715090301e94072003500d030010480d0112582d141c0003807900340301c0301144040c0b5402c1c0c1c959004800e000307003006405400715124a2111041010101c800060500c6075085420106405481039400d0705158812491b12058105c07984003480d040400003031661f01c1403003128200e802e010fa80010f1065240a0b00e01048800391114003005604c4081 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 900740674 1250 900739424 900739451
    0xd1d0f0c032d0a12020f031903110705010c020c190e0408070c030507080c0f0612011e2c011a0a081e070e0127090c02030408120d0b09250201 62
    0x210240c1d41d00480c41d0804d140d00f1003500a140480c00ea90481c1d05400074041d034212040c1c281d03111024000c61f801d010501050819482c4460300a03110050111740c201210fa88440fa00402c1000f4484420788148100c1c448079840049465070034403484680f034101000207408590141d014200032807117080c019403059900d445240c070b0000f450b00500042d41004116000380c1c50002d41c008071940301603a0050804860304084416a00c052050061188400c500c481d0300d1150944400003500f0604240c1c40c0c0e4410b42001d0304208090104d61591240c031840c004111b040350402c00c6040303d041108090315124400d0303c01c03500054040c0500d9550700070040030050840303010005911852099580c00c1d0035031800d1000418801c890441414194420000100038449907144d101c103981c030034a0049203a81a015040b4174500c075075400700d44903008042403038400b651441c0c010204510740c400c0600062844200700001c0d8141501ca04d29130940c40403540d0300040d01c6102e0790348840d425000000b034a00407a0032 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 900741924 1250 900740674 900740683
    0x21003140106021f052502011b02011a0609130f06050a12020108013206090a0e0f09060606190215011508010b03130213020d1d0f0c032d 60
    0x40740140c1c0242c9241c0042c81030320310070131007109500a0288141d042c1b1342490481e0843d034122040038403010001d030204542c003d401802001e044c1d000501103600102800900814009111260309210100410907502d002c0050702d44511000301002c07140059180c00700000c0910a120b2480709440350390000e41659042c01000c01010000b40c0342148005601c001080900c058001c0241d071a070700d02418001d10168541c20180c101d84200c0107207800204400180e003409007c3c680c1d0351101d05808040381c080740c0565090700511076851405580e44820400c00c0e141ea404450740d5030000c40c28001000e00c21100e00345481e2101d0103005484166414032608000c90000360045044c0108091442c10442d50020780c5a00500d400701c001819800d2095125299400e1800003038802c048860b1103500d801d00f07680c111407601041b0b020401c092034000402d80f078048a188600c01e50b034040e010b41190b4229001c110010150002005002503406441003811045c4008440420380001d1482e40ba10f85c3d0f00c00c10 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 900743174 1250 900741924 900741929
    0x11e050f06090108220818010c03080c07140d020f07060305010302010c1514151c050709240315143102040905030903070b0a0c03080601030e0109210315030210031401 73
    0x50716a521070109283c03100300d03007c1000b0181006404250080825800841c4c0342d0080ea02040c020780d00d89072400e00715841d00e8078402041c2c050141c1d43c042021950001030b102511618501550303c410b55804081d42100c1e824803010b4003159050302c068000411446034141110720b0150000f40c01080012141141ca8088410701c465221851412032545012100a4943c1c00d5032a000028803042d66201a01c0388110b102e00c100c0d0702d0b00d40c03140c951200068516000c41e46040703d511482241e81381841d400341120a40148406481c0000f12071040a0746a0300520035090a1a000071802da082841c141c1070250141041103e4403422841c0300582c0c0d039000c3c0707840c4103004000941c0ca4164a1040605040c29980000b00210381085404500d5410646040c001034050811001d82d9031800c0051f000303020a0201d03c280c80d4038143c4100104880d0400d4280c06281d180c902d026200602c5400b90b044941c0d42501d80c00f43c2455850400043c41c6c080d0301980c0d0201e880c03602148850480400701150030080c0c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 900744424 1250 900743174 900743183
    0xd031209050d090b18060a0e0d0f0201090902090904140f01091103010608010507020604120215010b0a17091203040f0b0903030f0703020708090126011e050f0609010822 74
    0x2140300042c0c06a00c407200401400500003254a81014114501e4904800420701d6003d02c40100d1004909409144104409900a009204204030b9460710740c1401860100483c045a202c07400821042c1c01842510520301020b8401601500d50f9216a54900f255135541d500e184035401c100005840300f0300039040c0061103400040310803040c0004040c2903c5458110450b1030307141c81c0401a01541c0021119009908416034501d8400c035444120f003003502928080007078031440c0d00001052080080100b400e140195038215501c144a42900d044100540d1401103691016a45030b907240c106200450b003091040c0c040c821610502d6803841089407003100c480541d60004010001c881c4103c680b601c0c0d1111051a0440c03400e0b00e2a56000001e028070000e040c10401920901450310209011002000494a2039001d0540c1c1d20042403841202440c51079160340302c812000a16401e14011002e01040003d1080f0b00704a80c00004480c0c0400040894030744020079101e43c1685403107803d40d801a0f070b005 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 900745674 1250 900744424 900744433
    0x9030c0f05010603080d0c1103030f07050c071a030703142e080109050d1d0d060b1c050f072403050c040308040608160e030714061c14010b0a05090d03120905 69
    0x10710001404000008c007120b48990800c0003004a403a124403421a4060840d0501507114902070282610708030441d000580b40e02c0008c0188442150a0006184600460341c1c041c011000d080e805840042000d841036000485091000c4c0c03404002045030705408950030016401c2560ba070300324242034a05040381507513a07400500c910040700d41d01a4101803601c01040e030354041980c9000c0401d090109520f1701400c113039035800350030541d591040001d40e0301c80141c00d528840c50000c0d0408a488025100711540144a0100006840303024541145841400c40103c2c0400070b510030b009501500c0700070f10300941d141c010800440042c1d16800079102034150360743c0b0004946004046032811182d03545512007407022000f82c09400d42e5001840809a907011824889682d40b40401f2079030394010719400303044103000380d401004140e45c150301c4000310f02070003820320426076600c403a400c0c158071521040c1000900c080003900c00c2d0b42040d41e1403034901c510038580b605050940c081d548003111542c070b034200c079541c01 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 900746924 1250 900745674 900745691
    0x13030e062101120b01080f1b0a030203010f0f1d030d09020a081005160c051e070506041404061403060406150314011a060405181902030f090d0309030c0f05010603080d 73
    0x3113940c00c00e4050640341e001400d0664481c5030aa964840745101980601100d1140c41d10544600014000a41c0d01030000c1c001000c80195134005446102c1c0840c000910b00800b150540884250804240c10840c0241d89004903035018034014240448099810a0350b40c40009210303101006112064100941c00094a003401072092659141c614298800c11143e1202840807500215205500e03410009034a020482c1e02a107042c00c1070050303800258010404540060101040d41c017481085508940411040e6207a44c942d1725000c1ca54102e80d501030b40440c00140000e0a9039108400c000c60613003032071340029540d80c0c030b8050103112030460400594460a0207034501000344621808400308035042d83c10705003800081041004425107140e10030b00b4260124610682401483c842c82d00d1211003907540c0c3ca440480914ac02c84103441e0110a4810741040c60100c621074804c402e0426419a14408885050340b5800d105d500240003c6e21203542c0c41c1d00000010b00c200b030040c09070b00c02c40300d004030704010b = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 900748174 1250 900746924 900746933
    0x4020c03070503280201050c09010507050c06040602010b04180f02090901090623060a050112200406030b0901120c05090718170c0108090c06130e04060207060513030e06210112 77
    0x44c41020484196070416051000040c410000c0d200c00c41c0c0c013132078425200c806a040c00c6280c00100c508c1103400c07400008002c1112541034010260310310050360140b01030ba50000e200da081c0200301d42d02070303c0c000c02001075500610380b1184050b0040c0b4540700200e00c0704d45503100c1600f1100408271142420314002880d50310424500c2c02554400c030210781e1200480d00d07200011303058030a008204034442d40e0f02c20b400403c041e10285145c01d0b00c2c80404100d61500d407102c0c400780003052101081c52040c2800c400001e4000c0c070100d800a49654442c0e9128856854001442108440541400d0074400c2e1a13803c80301c083d1140700000010304840350204250000307403640a0801710b2102500381040084c00401103c114000b640b40e810601c161501c681c0c88100190f1003003124040d421900b02d00001c030301440207100d01600503202d03c5015010030010380d1142211101c0071902010018040350140342070400b14500074000d0248108011021710144007500c50260b5006c5003600580c12080500c5980001d02 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 900749424 1250 900748174 900748237
    0x50c0c06070503371707050c0f060a090b0c04080309010302130e1e0604092a030203100209090a18150b030f03180609031209010309120804031707090504020c03070503 73
    0x81d0b1135418a5482006030f001c1c42c0d00b840200600030307002c0c858002a0104041e404000c0d460b000707030444c0107898443c1444100745002c3d281d84a001c0d10b06c0c1c42d48c14046140d05015100303c6088480c10740c025840c14402000540203900001480e00f12241c410500088402100300c40702c0c8540c02c544a4201b0f944120020188035000c090040c0303000e146440c811130005103503880c4100e03403a0360015100381d130a6080036a41c541910789400080d01406180c6403400c0801c1107070058001c0050495418a0b0f071b654070404081210500c180d20840c101490754064003240e52100b00600100e0340c5d2402088044030080424603040f000282100145c2c80090034500300d424141c442451120116034035880c0a40300000a95141d0303c40941e20f501c4000007070100410b80c000e9000c1c202c036503031116185400081c01c110141c000b9804403001e60201300341114072145040080b03591842072a51b521a40c2c00c00742448103101c0290014083c64286110810140c4c0204d00100080d10142d0040d0107201224400ba510003901e5 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 900750674 1250 900749424 900749527
    0x4020a0e030f0d1d0a0b12010e0708070504030308060102071e03150203010812161514070309120c02030a05010501260a0804050405060d0609080415050c0c06070503 72
    0x50f41c0000348000c086030343c840c4208000050110000c80328242540000d10400c809920065004200181600c40075015100d0703241204d40001c42050143d0300c0240070fa4000d4005c55210001139020807080c40001d002d1000d0741d411280c184100d508842d181c030302521070801442d070749601400b000d034010820001c818000b000385892070881582075502d05442e0f40e607100f03880c1c2100381900c2030114008400f501820345500450fa0440085a8011294420800107002c985400307045d2070074043c00607200d10700a00501403002e900c418201400007240c4c0e0700b03c2c0c48007240c3da01241c2c140030310110800032031001d000e018040d002d588030300004040b9402c08440500408404c40c2450317000705a0800104819000380da0031900240c90200b407983d40e50001500c80d042008000b0004e5140c940300300c00340b0030000054000c1d034448035101c203440000d2983c00c1d12640181d03101f040c41d41d40880c00c1303035403a0306021b4050859148544200e1741054045070038603400190080b11120214503031001e06182100042d080b00b403 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 900751924 1250 900750674 900750703
    0x190f05070f18090c03030309051006120c0501020105041101140405180a15030b130f050d080103060509011a0f01031b050c15011211030c10031406010f210b04020a0e03 73
    0x4002c1c1c144e03403405900e02c9280f001074241907448004c40140f01c000d21050b82c0e242c50010f0100300850305c8103400c0401311907001307080c2c802c08181350b0302244a500500c41c5070b00654100959003d000c4080d40112110390501e05212070b542d1341071100003001d071100c0ea50054440d0286d010048586010603803c400c03103041d8941003035101e40300d51003000451903007407616410442005040d05540c406050104910000500081003842150000300c0c820303500c40040c605076840f03090180070355110888114281d400c42140d11581720b51108070b0360850703c0c04e01c03126032100c1010704000c1903a5030402c1000900f074030300b002a00e01046000031800880002800303c51904442d040340404294140042403080004100300100300c2141c2c066140d00b10340e4108009801650000c100320311124407200c000300a00341c880805d020001101c00450380e00c0d8000c5542010f91025940c0c4d1a49a003140c403801138107051010450050342c0d0355410744e001ca54881c0d00080854418a854801c0082d2601062628180740c0b40000300 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 900753174 1250 900751924 900751931
    0x50d03030504050f121e1608030a0b0402090612310311070f060309060b030105100e0105100219080903060f0402180c0f0937090e190f05070f18 63
    0x2d143c0300e000425509600449817495203a02d01400c941d541d1b62142e4184040d007a8038100c00c1000304120700d0000c605c42d00748010107004181c1c07110240826030080d0b1032401e622041c01c0c0030701652000446010741e070000340c030302c91800c0b51010041d00c2039002d42204030303400c0d540300e00520000030316410011201c44030304000010f01c80146030030f402d503000341c4950044000b01601c809031201440230030b8000d484c1e0f445004000300181d003840e400030024001c50b0f20030501d080c40d800000107100d18184440500881680c0c02070401d01d00c60134010301c648441e0400440710300005120610b02030310200b10742c40c411016403070404110b0805004014058200018003006845400c007001081480304040d94009000240305580b2203061800180344010007056500c0211026452907000b196607012640401c1118402040400d1b103402e014000d496982e101d04103564800010360700001411900c4890003800707101810707004d40c0d89698650801240f03070301800f4241c2209405001c00e070480c011902030640c0654082 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 900754424 1250 900753174 900753193
    0x5040623090705040e1e070501021b060703230304050309280509070c0812060a06050a0203040b031015020114090c01020703080c0106120317220605060604050d03030504050f 76
    0x1c1d42c599140c010b6038003d40c0c941c403202000b20401c010b818850003481018001c0c000600d82c5086da40c0d80640308040c010310481e00340500c10450342c0c2c54007100e0400500351502e89503042d1819640201c841c0342070070314482001031031445c1a42150181d03000e244910080c42c2d590b0750030701c104a00807195911513560000020741c0310b0303041c1c00b10788004002c480c1c081e22200b203542d50b000010346001e80c2d040d402031309400300040e170f1001c0d44910407180392044c1e03400c44001c80043d45900c800c4505001e41d4201001682c0304110620591030807402540e40504034032050345885440b8000c1c481c403c2954252200035039140e103070818060399624949684820600001e041c200d5005000030351710701c5107100c090000040003a42c0070503000d0a4011101500741121444103000032480c0043c00d0461901c043c0d04c003501c1840104031a01640407104041814086001c0041d00858541c2d000828010744850350142003008006001d0f15910000138942d40280c900080d640b0782818154105007010301038101d2038000c030710300303 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 900755674 1250 900754424 900754441
    0xf050103180f03033207021c210f020d050117030a03020d0b0405010b120f130809130518120a050f0d0b1f0f030501060504090b030a0605040623 63
    0x411201e503400c918814021229814180c1c0100304d105241d0792505040e2150484007406100618800c008002d55500f15649014040381c80304c10321464880d80c4282c1000780942c0c103100d2401d01000f00c0c4490f0442d00c401c040242c0300412a100c4941c0b0084007600881c4441500d01580725990041c8500014000202c500d1111280c0f01e100b0203079503c0502da804100040505e419500030800000c02500c104101e503111512400980c0000d240c40c242d01c100743c000541c818411844e1a07000f403c0800d5048601c0e100e60780c5035015a08000c060b01e800a000c00b450f1058020940500c43c01405104448a1050316110b8440e06001094007180071180b010800500b51a50200495800104007140b841c0c80b51007051019019142400d1240d50003040600c0d1403024400740301d0384036040042d5444a001c034a15100064054070800d00c01c840c0800d0f0180020030000c0030a400c95510810300405840c07004525945003405c480c001c1d14146c440320f5907a80220360382c61b061001c4007042d0740c02034220740c43c0c0c0c946030b90f2 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 900756924 1250 900755674 900755711
    0x30a0b0f0f06041203050405060d05180a17030c0d05480921010f050618071215080a03170c0d0b12030705010905060114091b0f130f050103 61
    0x3c0c4d4078040c5003c82c410b40c141752080b02a1005440c004002a43e0f42d010041074502418050f03403247c20002c44442e42c10490f100004080030980c0d80718503042c0c050707a100c041040c055003008094180303100d4100a84100d40e411449558491144d90081c010403000c9066007500c0c114a021080e135070a08844c04034100804e50014004890b889000750030307078900d0b5400204840c0d02c2415a003030001f49280c011403000100641002c0e45240f50a0020005542d980042104c00c0e151403030201c8030300c0d94040c003080780a480703007800c50300e00c0140d0718000c101e600c0360a84140744141076500904185d000700d0880010160300010038005c001c2460920800c506200700001200c0c810b85400031303180f50b91080b400c01691905113045d5110034503030b4203498440005081441c06040d80f6041140c4034010340b000070903400e5104600550b1000082d080c0110750342d400400321070481554038900c00d800030a011840c103080c1500006c10213106c41a10008182d0300d0480d64203160320302c03500070b1414913042448000040c13140c0d42 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 900758174 1250 900756924 900756929
    0x1308071703041e030512030601030b0603040308191d060f0c0c0709020a0912080309060105091302012a031d0607082b0509010c020609010e06070f14030a0b0f0f0604 72
    0x52000510411800d440c0d40019101e9100900d00d02402044c1900700b601b542c0a584611030a032014440c9035001c20800c152844204d600a0100b00c101d0081403201e007046d400f0f410101d032800c50001d21204101202640740007110340074805540b000c1c0822800030340c03510745030750801d500d20801801c00d0780d588080d036110817aa0146141881e404140d441f0303060703c07410a050080c85641c00c000310050050400d0300882d0300446680050b4810100005001d04095090310303ca24482d110009a1180395401100c102400e10051401080600c42000c1d0044a4007031a0040074403a84035112511142d2582d000c3c42c90314130305c4c21445844240844804582550220b80f28041c030000347050b4120041550701000307003900c00200060a40380c9400c00050301c405620910f80010b8640031245d0507640c0309030660a94012000490243e0402404916018018440c52a2401290034103200d49280010314580700c3e0421550b10500a4440085000345e0900d084003d21030030064883d481040c1503400410070038411792 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 900759424 1250 900758174 900758189
    0x20a110703020d03051303150b010e01020c0306130503070c06020c03060a050f0103031101020d0617010e010207080702040b01090b031302010e090405210705030f0d2307140702030102130807170304 86
    0x86c200c20348000c184206009150f0000c841e036181c030f084521800003401785c1d011803404510301d44035400340c66000180c0715480201c001c004190558400706661311216200d2411030309480b080c0100e20001e4800340b81c00c0d010340b00660040c90750703146d08000c05181c49800740c920700c8103918003401c0c8500d01e0943c041381e60549030541440c44400c440040c080e80240b0900c4110140380745000f0300491881803000c030340c40750242101c0090001070300c0004100d00700d1140300700c01824030804025060050500703410410900304c05042400c1125510024080315610440d428902c59898181840031580c1000203005c40f0881642c01103160b2400f81d076410b03a1480c81c5098109a5807240b040c403038164004008490302c1b180d000007520303240e1240a01c03a0050b5080b80c107010000f0303824941980e255a010340c000e55421010301005801da916501c005440d203200d0b0034102101c8810411910002d42c17401d0004185140e8610781391054a49040c1e800c2d418000310750007140c061412302002c502ea2100c004191400d86011 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 900760674 1250 900759424 900759427
    0x3060108040c0e1f08030c03030619051c1e030f12061203020a0b06090919050703080412030915020304031e2405010602010204150c111201020a110703020d0305 70
    0x1281842001da01c0c2e02c2d8840d03400000b0500400907064640b0074000710ba0310000c101c18184e107854810280d00c03405200a48a5982d00038400036100e8a014041801c0703940c40c0341da07541900fa8542d400701e0030b200a40c1c40200202c082c0342d0f03100410001451200c0e21034182e0300103c20014401c0d0783d001402c50315500c0301c1e0010050080c0256044444903070044000344881d0307007000d84144c0c1c140b4000e501d81509a00680e400d00c003101c0021098101000f41501c1031a614024144412600014460720b6102e960143c8184c41208004800590b8a000402c007038000051070461000c00e0745001000f0818a810140c0818040242c500301c0c180c0000a40c0c0a0f25400900100d001c100318003540da80c000389180140082410318001c40c01c2d5100007515030b202c0c55030410180103982c2c0351034060b404c2c3e129a01c54079041548010700c41d079481e4480c140380254030703116820002800008100062800c0c1e501d402c02c8502ea5800105034181580080e1007052041c0c0c04d10160650919503000900d094400ca503024061010 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 900761924 1250 900760674 900760681
    0x21204060f2106080a1104060605070b070e10050903010b0f092d1510020708031902100608030315040b090703021c060e06090f2e09020705060601081b03060108 70
    0x8201000071410001d0b10304100650740c54082c01c1c0d032440c0244017940e405004541c00096400c144c080c450a940c41d544500c1e240c004565550582184000d001d8000c100c8900019803603665072500b0b0340c11180321545e459494070400800c240c21640d102c83c400f40f180c00072120340909034945402540e80b0139240e200d110142c141d000c241d80034056191140c800412008030401c0081488442440c4000300c080d07481c59001c600800060340d8400441c081c4452a5000f401321100d0280e40305e0036484024031910548403070041304c103214015100710350032400c3d45402c08010007105150798505441450070480d0103019020200300400c4902d080a401a42016000030751008664080c030415100c02750041e6040100316170381d0300b003110040829581e00c2d1040d402c1c0c02c04190041c0c010441d081c0200b452030403000f449644c0041c050321200e03109407512545621035400040000340341c8040e2144501410241440c0e24001d0001000f40340300402c03201b0802107210361001424559030a030b81e440502804c001c0c15030348 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 900763174 1250 900761924 900761957
    0x90c0c06053304020706050c0711121911060703030603200a0308090a2102010f050f0316020c03030d0e0f030a0c1101030f0207052109011d042703021204060f 69
    0x10500e100071b040e00e4144400d0080d40c002060050540501501090810445410070481e000c061414125503551104895002192286a0300703c10039104480c00030100001f603000c58601d810501050f004a90f6401040041c000000c64005e0254110480001003d1503900081e03850001030001030800c010204196a50382c513038210304006000c42d880f0356a42c032000d000720b222000c1b0036048124002a1180c200b08002405071064a44d00041e01803ca4290b80e60408804444501c0ca4103c100f103108004c1110342d9900e0502c02020150261040400c1050a64103c6031400302440e080011a038810000c80d10400d60122441034050b900561844070300d90460012800380a060110b414090301c0018410704010b4005002e201d000810861500162000303071800000c2c0c02182000d5010038204070880c8a0f200b0140f02c82003400000400c00a070400456449881d5642c101ca40300206c03d10000c00c880500d40c0400c801d582c1084034151291919090540052948010010f60350900024510440809 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 900764424 1250 900763174 900763177
    0x20327030a1404270f02030606040b0d0f0e0114090a0201140d0b130606020d0908071203140a0c0b0c030c09060f07050f010c0306120f02060a09090c0c0605330402 71
    0x1000f1034240460741c01d00e03a507440c600220a01d502c50030388031700d000700c80700c081540d80c001d982c030402c00142803c1c10213140072000f100c0c690008450740320865449440c4404d1195610881407d11440d8000061840304654040c81c00c14001d81040950340c410460900142e074848540344a9271441035202e5240c4122031044806040c0844040750301124002c21411041c081e68820000c564280d82110382103456140305440c400307805d0003095a240c0181400b4841d80e100d602600100034401e14190310408500300408880b0f1b000000d03050700180c8603056801c1840386541c6002c0c2c00c141000324a031710314148007007400391314401c0c4c003102806031902280c070780c00d082003c009443c003440d00581500d03c40302ca6121007900800c0350081e540d010903e003000c04a042501402c05000203940b2004c101c0804450fa02000015000320454000700300c002c290121b40441c1c0d600540031204815220f07560402042d02d00641500c3c0004c0505100d0140204c030205140c004400ca491040141c0144204c50002200490060b = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 900765674 1250 900764424 900764429
    0x5060421020d0c0303030c03110910030e07030f062c0304090c1101050711061803070f0206130605120c09011d0109080d0905210601060509030102070b0406020327030a1404 75
    0x40ea000d002c00000c5c107415401003034401c9002e540070451071989286804280c060400d0342504900001c0e0b01e140340c2c034020307800885021301d01030846d1142d80d40c0769200c038040e008154084510300e84901050001203910200502c64034003102d0340c4020482c11900990f502d007c0c0d80b00b21401952140ca441803840d00445070340740990400d0000380024500601d0141950842d008086814801c00c400030f2100c0101c0e00c151a2062114005035251528545a40e20b121741e2142d0280d03070114040045076880c0010003081e80c02170100d0703202d02d521034070001e00c030080100e401042000c0c0403808221080050b80d101004120010074481e00c1014a28003000480b22038980780c00c03070310b07071403090810320b6a0040e007148501085810860304c9071406c0400c800380ba40b1000e01802d03240c215501180042c00840c0c05035000c0c04c03140c0c5d4090001400d02c840c070b8075042041c3d00c05981c1a25055800418402807102035a0880c1d0b0360b24041d080c48844003803252800750707284155102c2c00200001241000c10604c99441100d00 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 900766924 1250 900765674 900765683
    0xf03130c0e0c1e0306130b040b030312071407110103021e03070309260a0c030e060a0f110f101505150c16080309010c03021501140a05060421020d 64
    0x202440e011600c0d03001c0d54407255144044180001c3c8094000040d40d00b201d01c00ea10103004581319000001c054000f8290303c040103984252240d1400400d91400c0000d40701801c0c071807040200c2c900f0f101c0030142005113006c42204a026003000074901148681d02c1300140b91600380703001a81c2d107034400d0003040016200e230211155504000140810790b98540c10201030326001307100d441c42101091031202c0c2446000540018104010702c80384030442e00030400108181c0c02401c18101070140b002c001600313607100d0000100881d03003070398003c2503030b6502081c20a80c510721240100101c0e211081001e41e0f0310600080b421100d46c840d056500500003407990070004020203030100302a0410302031000302c5500909401a0148140350712540144004001c1c0d00413150326001651078104c4000c01103503142e400074003d0f41548a2291040700081924860500030300c04c040604c882d43c80714404120740640150311140c840d40060006020800440341c3d6000382c544039000c40d9007018031501c0401c40ca070302c0302c5c1005030 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 900768174 1250 900766924 900766949
    0x1d07020a0c0902180d0c050943030c170a09080408100c02070617180f010605011101020708040b1b0f0a0203060a06360608010f0506060f03130c 63
    0x20b4101016000f81114a0546030902443d06030301003800441c12101101422020030700b00f0420040c1458010a078019000070746070502d41311a10105600034607440c7c02c0ca24240350b01e411104410100f0544208080042c1c582404072000004008200d040800c01103400c40301c031440410800c8000b03600925075198007914040d00d8550b1100c0c102d448900f000d40c0035200c1c1e400d0840c088041d600c040340e07000c266201d5469003c0e8441e40d4090072070700c04c88024074160b524602c2e44032903543d01100b08003500c0e50b50480000840d0359410480010944d0151455452180e030042c412030001032003100075102542d501da040390342c8445402580c600c802c0941d204407101030044c41c80c18648060b001c03c910303d4190080c0c040720559103a010a840880f000d611500070914000740d4a01d00300c802003040314070802d144035068046120b201e1800c20844840b54070401550790b40d5404c0e401500864000c00754441c1e0201d640c0c0c0e0a1880e40760825042e4400100405001508610b100b0201314100740f0900203000e50b0103421 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 900769424 1250 900768174 900768179
    0x712060209090c1611031905010b0a080105150103090c0b07051b060310120c03141f02120105060f0f0403140c0406080d0e01020106120b070906091d07020a0c 69
    0x80000d50010030703118000e58000000a9064072108100c800341c2e04248020f030501111900c60200e125464203480d94036000f031610f140c60740c140000143c104030f07000340000200c59000404014000c2e00c03a5108100700c2e4141030820520480c002510f89400c2000c1c00c000ca0b80c8840d918101e07807103411a400040c984240480d1440a0140008815951500c0440022600c000d00303400c0000c40d0104a070103041625201806001c2d5074440c0d01c07401d04584c45207110001e101c0e10382da01c40c00f071080403484000582c0c2c0081260744400020307080c40c2e000071142110031482c03e41c4901140c5800c000500420340650f400144501c580e194140464419586004100b0307155622860410345180d680c0102e00441e10031124990540d00c0d0501c40c810480701003500030000312640b201c0c2944c0c032001c07400c0c056056550366000014407036420118440304a21030700c003074800340c94100e10140844031250407441c10001c3c0c400c41131101c1051f1684140a422402100c26126a03403000100d203003240c1070078010000c1d01d048600 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 900770674 1250 900769424 900769433
    0xe0f0c180a0f260307110d080d0e010c021b030c010f0215070201020306010e1207031e050615010305071107060c0c12050c040605040c0507080c01091209080633030712 73
    0x4504040c02c00c40c802400c3c0c03500031108203940f40101400078003280a00180400c240c90141d81209020788202c2803181401c100c070003c039040707980140c0c140d035040c0d4492400f10007440e81400111510f0b80900000100580740c02e010176a1000c2583c2540d040c090303410900718041e8002c10094003102d000005900d5a440d007000000e02070740003034849034082207801d48030422a14002005800300c0d0240c6006048140c510340304d0b03036605100304101001501c88180100042103040c8036251084195414201207055020f0004040354001400c0a0400484c41040300c022500401c54000b1100a85071102c000701b007a04141c18000019070280c4031325108610680c0030001e01003507201ca031050803201001490f40d18414841910b080c0c80b003a000191040201d04002140340020f4060102400000200e4000a90300c4846801170f040e000e2020408001041000c00e04c1080b11542c81a803818038511440144202d0003940c0c101c00c442045a2150040340c9032607a101040204001d01008001c10a0340b03146040 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 900771924 1250 900770674 900770699
    0x20d0225050c0d0308160509040e01020301030b060f06041703120f061503100302060c100507050c071d0c07030309080d020a0e030109111e0a0f0e0f0c180a0f 69
    0x3400c44180c0542c442c5076007946820550241d0f01505605c0718540c070795032056003504041444104000344101842002c0d0b103a01c42c3d12031000755103074036000142e0769411800c03d4141044000c1c4007034482c42c80302c0352603011a1a9441a50700b140c040c14a550101e038100c801590440c001c400044400c04012810818250f051000c602e018610540b00e030041d000e80800100c145200031541c611032102010020001030a00074020140305803020141e42c500d500020328081580c1054540400080740824484440d04041c490a0300078000b1840140900c1041c1c00c220300300c010020b013254044100883c1020038140039410040150ba4085c071810b566224610140009410103003144002600394903140410703080521130b0403041900310007040d1070f104180341005101403d40c0b4516a1100d6002042d0101c2d0b211030003114050200501d5050a00303081103602040f40b080108140b403e00045414007402c00301040c1282c0003956030500050868445401090398146c1c1c1d9032000c80c01d41c0d903a86d800180c1040302c00 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 900773174 1250 900771924 900771997
    0x40803030a0218030127080f040e07020706021501050103020304020d0f1b0f0315020f0d0e070306180c050f010912200105120a41060105040e010306020d02 68
    0x68603c204095800141400c0301c9806100b4a9881c152400100744d66000c00d5480c02205c0c800d907440e910740802030b00206100c1d041075000342c04070307003a500601c400c0340e8061000301c0180141d40f00900081072011148910301d8418801c03d41490341c002702042c10340d00d59440140c0326a4002c1000c80c1c10603442d1903c81c808803407010740c0c1c01e1984510140811030034003110144080b03a411400f0542001c0e000f0310000b009511078000203c4140c0100f10001444803140503200c0c03800c45a01c040c10b00d0700e2841c1080d07400e032000541d030008110010303152213001422124000082c2c070000d4514031911074030000162086600c58110620341c003050000c05041015280c05c24202c1141d03815501c0d460141000103403007501806e01c94801d000c20305800503411081d180d20003081c03502d028100140529075101a1b076150b04000d180840c855441c071540c400c01c44501a01e19400010a29003289481e242c10360750102101b060000808481e00024404d945100580646040312100d6448039070703880301d2641701030000ba80c18 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 900774424 1250 900773174 900773197
    0x7080715050c04032003010b0a030c09150506070f0203010b221506020d0804020102120c1e2808130b120f310507090b011b020109060c08040803030a02 66
    0x1001c02040006841c01c0b207602010f05d42c04041c00004170301c1310b07003a90b00009805660b21f05000700a0794680d06a04003c5000707100300203540341403e5081c019074044650a8a4881d403102c1c0c20801512031100301e40704160007514480e5901458800a4007602c034840041d50b220403541c00500c0780c0380c1c144003200103000c084501001407240c20042d15030f039482c0070b200741d030b000d81c22250750555000d00070125250310610510686801814100c003084654100d803d209450341d001c10359403080b01d28013440781000441024001c00c41c0e01d444408000008061501c0100840030311107150003000209010703240304002c42c40d150b184040d110081070750242c001d08442c501c602078078804a941e5004802003540511603114000644a0044111050b00200101d12800036541c7c90809004110f0503c5814060f014400c4041024040e91000500c6401c100c0d04032800c04000e44070000060380c110007004212002c07401c100501c076619003001c0209002e56403010602e40000000c0051031030080d4000c00e440101e6 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 900775674 1250 900774424 900774431
    0x20409060909021011010615050901120b1309080d05092a0904060b240408070602060c030114031218040f1509020f160507050f03161a07080715 63
    0x12015079a0a407909107001940105003540d113407100301d20440c02548010a03c10010038030540c1d44035410341c82042c40030030a00181c004551440d0540c0d00c14a0411652850320080c0a45982000003461060030403143c142481d5540e916042081070000c2510b00c512404102000305280c6060303070a84170260002c106280c521a0000c5c807042440d449443e68217490041c01600321551150f03241001009641003903603015030290103251384d51080100300c011284615204e1612546004040382c50640076401204c2550406000c2040707200b00101501d04441e4102000c01d108090200441e08010300310104252004002405104041d0900803410825070183c904001a140c001075800460701c0841000d00b00346c0c03403850200090903040d0054100420038102e120310301142c020313820068070902c03a03088940c3d421030300041116103883d80c095500c1110a4015080203810302800108101c0140220381c0c032100e200a000c002c8040150559403001d0388800c00560b01c00c9981040300000c181c000d21060020705 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 900776924 1250 900775674 900775679
    0x507030b1b04030f1106180907020706052d0d06030302061305100e010b0409140c090708040f0c0f03050c090610230706060f0303030f0501050d0308091005090102040906 74
    0x50042400c14071801c0a140607040c80d0441e81c030411840c407000c8050f20500c9120344609800d0352480001c0c00b15011030024100c00e14100070a00100f044014440700c10b40d04a040101b15441d00002121840000421200c582928410010801c00c2002c000490040000b042d481c0804540303600660949010380c084440b56039400590f50007000d22030400408940100a401500c56003507001141811f10903000841d4514080d00420121103001c1c10907240180028420302020006114120074010282e840322418504004090302c2e2403030280c001000c903907162074020b05200345483ca2402810360000c1002c0110fa50b4103185584d240c00e60081c91080c0021400b1500c41d241c401c1d6202c54034925612480c011151a180014024500c1100104411400c00001e800900c032442841c000e4200d18014808090450400074100c840382c102002c0418030b00070051045607110004001104e600d803525686039564840114180100d550940000506000a0128010041d0003070020386606510821140d603 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 900778174 1250 900776924 900776941
    0x20f010b0307180f060503061302090604060303050f0307020703060504120e030c01140a0c050336090a0906021c0618051e13080c010c0e030d0f050d0b09040507030b 72
    0x100b003032080108009004209420426072a08018401810b166002075040c0d07845001c603003050070450314044a0b42038980c4800451801c560415000b80c402e40d810000700d411540c001c1d00d24462110402d81c681d1010001031b5030b241c0300f0050b020180d5844201071045040c83c0ca01505e01c11122060b0f440400e41094102566090000d10500840300c160342c0d041c0305ca00d2240940b101c580c0181005030821a0300c06060021600402c0280001c4882c034410903559080c403a020744640a041d05041890a0340c2803440003141d956500d1150001c1000d1800241034441d454030400a100b200480c8400e4140003070016800a101e62054040b10801e0038000c0012443c03c40b103108540c411036042c0410300c0c0794540e45005d48804140164409000b01c3c1000c2105020b07100d42c4030719080944c61400f969180c0b50882440341d80000c40b083d040d0700541c0144901c0c1721400e805059000f010607440100540491608485101504050360001c806402d800c0241800c0c2815610b4084502003a11880b01881c08910800b = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 900779424 1250 900778174 900778183
    0x102030f18072c0a231b04080706020f0a081903140a050f0105014e06080c010905180c1314090f040f0b070c0611031e130209180706020f010b03 63
    0x440a00c404240c5059088882905c924000f44c4034454102c00203503d00406070210707006001401e00700300180700051416200a203444d1800c042d003907803030700316568000c00108024190740c4101c07204040e00b911009101d504400801900d040040401c170f2403424400041100e41c030241c0070321851010202e25070380f20030056404103144107000c3d155012900c02d8404c4d031072000041e00740803500b0b504410240341800c8904110402c0031000100300c2650750104003c0c0901c100844001840d00b0b00f04220300f1440c00c0c0000e080740d410781c1e03012400b01d50f040000828500092007100c0e11100d41c500c04181498540c4a151030752000b0000311805032401b1008112038035400c01500f8441c581c014581c100184295075070290302d403c0a0914014130440ea4000c80c0090790700c0c09144094039680c2103c64503442c00c400c045103ca2040100259444550401c1c08920403901405158807a0151516805600c495030143d8400c00c500c00b2503081c1c0d000d003000100d4000d0b4041030040700311184070001d008500b890700401d500c9 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 900780674 1250 900779424 900779441
    0xa09031704080a231b010e15010e060312030114030106180926070f1406042001080f06060f0d0f090c090204120b090a02030f1c020102030f18072c0a 65
    0x30560140700e040c440c4d1751014102401c1d10815070020903100c103540e140c00d1030103500d144150030b03800702140140020900c0c0c103032255102c401140105030034410b00d00890010b100600400c4210803070724071040300940303094111500a240b0701090841007580303030441c5001449032480c1168142e0780b50313801c038500b030f031640309100d00c91035107085c105240640c00d80e1507400c908074059003120024111624100080000d0000314807270303406414062921991100c034000702e003000c048002d041c8502d040601c83c500c1510350209501400a58020340d0352208181c03050018020041e00324059402c1004600d803d442030340050241621500012a880d52a804410268000da0240d51800c044d00035409000c0b0755112262074000c406042074402034011031700447d040c0702c1c0440550b0741540c48450465100300385800c110307056110340c2c4000c500314100030a58001c041400f0341b08031900310300c1d5a00e080c00d0540502416000380481000c00c0d621301c0130108030b440b01c424410301c865840942c15001850600150040028 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 900781924 1250 900780674 900780737
    0x314010b12070c06180c091401050907050d1505120a0f020f060c061e0601111b21010509190201050702040e0f0109150501090905060a09031704080a 65
    0x308601104410a4204010701281c01c000b903d10180c0d02040d9240320703e203d0049002c0144030740920604118188004c664081c09045103041b00703e003103850030b048145040d140100d44000d482d80f038030300c0c00711146d0050750598010a0b01c0c0c84035103408542901c0740398080f2001030b5545d6000c0000300110548600110501900d03405010381a24010301d00350b40b041d000300b58000c1c00d590801450f40d1a4500d40303941100c2c031561608420000d00301c003000024040da840358092070088003196810159035290800c06078060000d80c075054400c0101d0340d48038494045003401c071001c4107200c9202c000040c080e0005558403d041e005610001c07410303002040700e54420a03010703150b4a1a1450660038072006116010203503200c2d00400e80040d1009100307005103501603000340c10180010644002141c03c40300180e01c00e0300b8052400b10b403000021400301d64954023030849031002448210504058500f84040d074900084942c40600b08400c000c0480094800c001c490781d200741c0c00045a9083d64030700c0020121418 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 900783174 1250 900781924 900781927
    0x2060403020a17041508071808070608090111130e1b0901080603011b02012403051903020c0301050c0c21041518090204050315060114370314010b 64
    0x403c003281600300080c45820741d070034a400c0e07494450020880e00d0b00e800c800021a02c409218080e40c0c8017031102070100c60414451745540c5400c00f510b0703980e00c2a01c200400d21440c140000c080344030a41c0103007a05203034036007580d9551400d0f94240f100040d071030240030007020a1002180068180c100c5407040190b0076415149091004001510700043c0200307015413541d00c840b1244100980000451750144450b000440c404020500c2140841424801e40800034122002000443c0f0300049a040c588800c2861410301c3c5083d085c2213060030288800c258043d0300700824441c9002c1558010020b14051205507000385040c03000c3c172181684984d042c4400040203100c1481859007041c034400c450005410040074440d1200b80c43e42c0001c10b59400520001c1d8046403c00560500b4425107591391202d81400d0014500900068031140d1007514003a441c850100740c0b03c4085282c00c0d40c1552031441c646080034a800640302c411410310902c40302400081c180302c4040c951175103001115042e100c09142c103e = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 900784424 1250 900783174 900783193
    0x70213151208090301110d060923133302070201020c12010f0f0e0f030a1d15031303090f050109051003150909020108011d0a2a05040302100206040302 66
    0x2001c00441d02401500d0507801044443c000b0b030f80901c40d2005560300c2510b0303e5103d03c100b003440b8086170b042d03030b000303503003045c2882c0982100c00042d1640b0311034a904c48058002d240ca03081515085c019260100130301c40c0c14403031040760042c5008040410109030300160351600038580c04210f4242c0c010b1440090242e446004440040d1030001141142c410050000240825204000c0c03410340d403000301100400c2e81d941c0248004800c0a002d00480001a00021032070f000a40e140101001e190713403604100700f42400c088605035903402d141c0c1d10310652440403054403400c1c4940780c020f100f950101d081f0b02141c05160005602c0301c03642006011102c050f16400d246515100900c40520104110b9808050769000708803204403841b9114000351040e81400507815201c1c1c40003500d03040f0182c1094100700d5401d065510200c01c250201c51780078a026801040e80819200c03180711949001c008001c0302c003400b04500200b658048042c2040720700880b025100c1d002e032000c00f40d881d20410707a0040c0c010b80000100 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 900785674 1250 900784424 900784439
    0xc160e3103030e1e0609060f0c0a050702060f13050a0f0e0c0c010903020304180614010e0a092d14241c201c0201030609050a0207021315 60
    0x1403045140070381004184844004403050404030601c941c0700e4921000303450350745149020030510342c2c00a20180240303010305202c1103445420388000c1680302200000030b80c25003400d2082082d0707480150701502d0951546251070a0703190a810035001c2c0d4040340c415043c0050b882c500300d800c41c41100c50f170b107001802ca18180340c00c0200e412401089920505020801d00c400c0000903c280d401d030901a071b010b1601d490410028240442c816a40100760900740306092000c0c4c0151110001c4840d824240011881282e8001c50000c0741c841d801540c4142c580381d17809100314030044064403000001060301c0c440c11100e155800880303d1400403400301c00c80280005e80c00700006034010000d00070301d464104664650500050646002124016210034455001e20401c0480354641c6001d001000d001c00c0b030500c540c401324041042d107003148162044c113458508107590007680400d01070a810b4030140900d00d0940c032400c0c069800410200c1c000e07091103106a840f01a00d100740c401103101145042d1744036150140 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 900786924 1250 900785674 900785761
    0x1060605041a041a0301081c09050f0111010c09090b010507050304050405100306020408011d150402061e04030507140910050915040e0a050c0109080604060f020c160e 73
    0x1d00700000c842c00c000c003148640f000f41c0388060b41c18001600c50743d250b0400c400d6a04101001000c50518081c00304201011500101c491085c0c1c1d0003a251119005142001240c051800c500c00340b40e107510303100984212590015414040e01e040c07140900402d1400001103500d8407410b68090501d42040c442800070b89070580016070480c1c51500301c00980340e11f070789a01080707900076440625141c0d50b0303880c00000c0c00c0449403403a0350101460043c1c0b1560280e0728404043c1c0c80f0051000f4805c202c001200c0b40c0c9103c0c1f1411600700034402106540c0c03603688070300d043c070b682d1a2680699000d898036880012400d01d0061420f610528000c41c2e503084141ca006c040c070000e8100644242e00400c1c02c2c0642801036180d82c82600090f66012000b49007050303450418138209203100880904000710031009000102c5c00240309900564000800515001c0007102100207002e440c104042d240a81c641401d100904845a2001c0e03800a1144201c641c44044010803441e62803142280340e0b03148061a4001c6440605 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 900788174 1250 900786924 900786959
    0x53011404090206030f040209010f0503030a0c1b0f08060108061006031109060a0e0907080915150901060807090e01120b0603070e09010204060905030c0906090919110108090106060504 80
    0x14404110107100741e00040d0103800440c4c2400003552628108010351605842581c01081c40014250710141400c010039264850340e0440740601a01c00b64400411110304203009100c401d1500080200d0b03120790100c145046541302d4440a4402e5200116610b440400e11900075044209000f5030305103402001d40140c0b2681c2c0403c002c007001401f0440541d00d5000052071149101d640d400c0c21801864200400c1c61b40c060075040800c810b070001c000702c54030000ba200140088201160486a94601d40c6058660b40149075580104105000241c00ca0308543c009000c0c441d252690100581c88a41c401c943d032209104e4455041c04000400b80456008802190800d60103020384030308075114401111081025149040d49030b60005040008a9205400c40f01900b03007140680004505000001d225040c003811080c800c00b040c1000c900d41e074400f00700508e0b10328022041082160848d05180e0303002d801d9003880c580440c1c0203200054009606125510a80d019902c4560030b050400c06c0c0d410701c80d00d010 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 900789424 1250 900788174 900788179
    0x14010806161707050a23160c0914060a1a030408180a03080a0306050d17031003050115030b0705031e070212180a051905040b01530114 59
    0x100000d555080c81039000501c075050a44a1340da60354031803000141400641e07400f00b4012440041c480101d40014001c952035a0708410318030010210504014491240f940e1241c401103103041c001084d0030b8201c00344030b0301c680d00c11030303d81c14030cc0d41d208640d030141c182c0080e09410102c1c04100180024440a0282004112a4411100030b02444000c40c0c450784881c6c20a88661601007031480c112036260054001801040c2d036010020b16076696103010742802d4100c04c00200b40040002282800010610001140c01ca002800121034103100c0d8400b0b044140401d8030034521000002d001c480c000c1044074040d0340d036603080541c190054034501c44c0d00340010b440401140903640c004101c05040a000c0c11040d080001d105102500740420420b90304c4441c3c0c80a4040d07404620f000c042d1507101203a51003103130000d8038045550901100100c920b0031200d4111088241003007400080d840c0c41c0c03c01c0302e44a0b00c241c000d00c60300c084200c41015607c8100410340314150303400c0300140143c50000001c4034401601 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 900790674 1250 900789424 900789437
    0x3070e040905060402041505130c2106080606010f0203030f22030834050306030c040203090a050d030b030a063b0c04090305031f08010c03020d1401080616 68
    0x89500150036140e0a03041a50940c1c059404d000c15441c4c43d2054108088141035668905031030440455800c502506d0030511696840046070f00c054010710385000707007100d06c40715007a010480558020003800d590094640c0c92058800241e03d40d4021141c01100c0f0405800079401c44d65161903c41418800400c0041c0310f020b80c2048030751000410882c0c440c4244692504481d924010022640908030100303401844201210245042400700c40700c80c00c10300703641c80c185036250f8039000800d180c0030030031407002d8000d440041001114a404a44040320512400c181e842002441d541181038407007003080d13554141c202c4d4a41c1e400080f5198070043c107003051103112490011404950356402d6010750403001240541c5806106039510a000d501c5100710102c1d4200301220385a14010180c0c00001c1c02c5800703400302d8564940403400802c1c00c41004010700c40003488011a140d01c02006508a22405601281440e81850351960417962540c140c6450724002d101039079070705007160f080d50551032150052056 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 900791924 1250 900790674 900790697
    0x10e0c1605070b0d0e150415020910030603060e010b0901151403090312010b0408060403050c0309220f051608040f0803040308070e031b0613050d0b0406050f090703080307 75
    0x741404800c0090010040883e1502088141c00c4180d909400c011030075500410300342d000950401d146241c01c6134000b4a10306140c154541140e00a108242115901c40b46448640e0342c81581500034500341d0f44643c83c18490a2080d0aa40303007a101814142d95101007408014003613010601440102100c0a10700705015840c1029802a240d0003914140400c1e000040d20705501d01d60b0303c00130382c01021040340c41d515007894501210388401c0040c20040c10000300080302010240d040095900d1428000c0440340c41c003070091504040e220304a02c4c5d168650781411080009450980f003500e00ca07c05040d02c0000003803480744225140e00b001041101c03043c2511480300b0110700b981c400b451050340301c6d07110741060303041048000d0103014102100314842d506c1051846541d0f085d4070381d01101c40d40255041520380205c500c08916072810340c1c2000f82c01c50f1070188e0100a001070210814000c500858040045454000242d22440401c80384226030f0780c0b000d10200001441c180c01158000100e01e008450300c034 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 900793174 1250 900791924 900791933
    0xf070f110411281718010501060201020922060f03050325021f09050d0b160504051f0905040e0c03010b010504060e011103130e1e010e0c16 61
    0x2840400203584000c0e0115120485041c24401c4035920b03503418000b030303041141c08034806a54100c100821044061103101d00050320340107460000031010501c012046a00d05070300c1c8a40d10f6031031401004a150f00301400099818018401ca03904008003030603100f15107100161048200f42d02542c05110603a072100c0004030016100d08560180d44a0400746942d41a040c2449a049003075031240c89802100b03c0b40000180d481c92554003800316040c8a41540710148641a64804095440141c1102185401c00304001202001911070620051040c01030541c003c0110786902450107900d800c1200e03000042c04404485940c03907030031280e9251031035007641ca0700046810780340c14604a2006a11080d406005071400380900c101808080ca42103040506e0001d0080981c03500039031040c10b00ca1030280080d40184140b08070382040541e11a00b01d0110795030401c61a00c0502141e100301801c04014401034404034021040e4100c81080c3c101138130540301d1003030040003a4170447d01c03181c01484540c0d03841d0015 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 900794424 1250 900793174 900793193
    0x507050406030804030308160905040e0a0206031006021501121e060f020319051014010215090a02120607050913090c1509080708151914070f0e01140f07 67
    0x542c03094036002d40350740c131794503010744070100251111030040010f600b09002d0b02d500c9007401045500840340400c9aa00740303040d440c2002b04800c0c1c044e400440000800c860369003201d60803022a44a0f508440f00760348105484021048280510140c1c20040850f04c0b0102c1c0c80c03184400010000c050308002045d15a690780e4003105d152451900816401004202c0d00350099060105401440c15051203c1d01d04130501e024214900d0103034540c040c1208100360016403080044803072210789003981d41e4807418410742c141d9403003811300d034200d2003420304688402d81030902143e460702400c644c0c1c5a25040c82c900c4000c010114201c04041000c0c0b59940c1c90300302c045000005010300520551070840131000645070024266105038020a101c3e41c410712013080741c806c000440011400d072644404243d61241c2d40c0240c180116180c0710300280e170070b100c1c5e05c490340e44142003464020b0146464000d22402d103c032054410220079200280460380619151221001038030003000200618801d0340e180400c0c55841c40e00c01d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 900795674 1250 900794424 900794429
    0x1203040e0f0106050a0c030f0201140c04151d04050c0f1b010c0c0503030a0203060d020904030201320720070f030c120206040b0904090f11030c091603090507050406 72
    0x5400c00300307024981444008207400361000d13141141c540750302200060b01e05612000010b040110801031003841c0c600c01e520000b900c80141721a060076007090380000c02d60b5080303030103000c0384004060018500304c0d0068032440e40c0c6c2c40c00004000103040c0031804002c01010018840085100b08000e03040c0090f0800004148815801d084802c40c3c905200455084806850003101070111004030039001c40c800006499020040c0e0300003580c0c950325900464050700461200940150035003061104041d0190000c4190001d8440e034411101c1c480802003800180c82d01c2000044000d620100e49942e100e40c1e03075003000303603241d0215100504521a602c1d107482600d038480a1420017030b0400b03004002d040343d1084002d020700354502c1d47d441225000164644114800c0780003010b400604000c00e82c4030341d0000320b610344d00b140c0340a13403142141c28501c50b04600d042c0b01c24070034040c0d81c550242e2481d00e0000700f03000300c075840201c15014100b0101a4014801d070341040c0e07103e210b0034100140c41d50b61400f90001 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 900796924 1250 900795674 900795689
    0x50d060c030f140403080114150d020d020f0304051002030f0403051806041d01080a050601050d0c0f0e042906150412030e010906050a050d1e05150a060503010305030304020d02120304 80
    0x18500e045c0c01d00501d142d03410780080f00c2c56a06441020115510000c81d590328010b079101c0584e480c000c54050310000c0c8500300304140c03828008964281c680340e00c0c0f009148150b004000f07507019240907160100c1240300c00c4035a124030340402c2c0082400b0900c9a009002060420144030381c50710200030001b1b01c2900240e02139250300c0811000d100c0104005e03403659005161100007416114480e55800352a01014050702c0c0c0200c260141400078400b000c1e00c400014405140e8500351580c407041140e40d40d41e821a415a1340701d0001582513580040c0d007a00c00c440c21002d402c0d4105c0c43e2030b8039082040c0c0e040c2c070351007000c602003040c800841d40c0d45403888010041446900d41e00b103040c0400d4000342c2a04050341c001c0c01400410f115079030043e50403804640315404c0c02240000d45005094000e0b10305c2441c442c0d03964500b4984002c02007001c03686c3c40c400d02142c1c0c049420300f0085964200c2100e0790f1200340001845030700306102141c0107003070104e0702c0b071405440141030110b4080a54001ca1647c0c01c10740c040d21 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 900798174 1250 900796924 900796961
    0xf0f0d15180b06090103051b07060f06150e040216061401030203062d0a020d0e070501120c09170a020d1104050a06060f1404150504030203070f050d060c030f 69
    0x1c1420030314030303400345803000c028000c0c40280390302d40015950303010b4400321a05140d140d10000b00104c940c044030861559481c14840d441c1c100c2d50404c1401004006490900c4130719040d40420102c80ba42680045103a0340d0781c8010440c240714041c00060b40001d141041e82d002c40c4c0030080c00180c81402040d1442442140102e007a40c90360041615100d80544540241a800308000c815082270b40090944030780c480300c6008071a03c1c1c2a041000034130038480b01d14003141c07900c040117901880104649040324400d0b6509031000d090004108102c0b10410700c000017084803240e0420045003016007450750085040140c5140300f61a03004114101e0002c50200d421484119400c101e500e032910640740c200c2c07141c0d2000c00003142401006448404002804014040844200445110010229000741c18440c0314500c00003203c000142036078016000807882401502004a0f02110301c00d024003c40700700078801059040c05071102401400c0d6100ca01c0101a180c00a4080c6c145480c01000c800b076401582c6030 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 900799424 1250 900798174 900798179
    0x30f1104080c03100513060b0105070804080606090a0c020d14190203030f1605160f120c050106080c030309060c0124080105070206010b0f1b10050103050601080a080f0f0d15 76
    0x1605140055003602c0c1045d140005024242e0041308a41070069409000010000321000058604e030090b52401041220005404030f40c000380403542500406084e5140c0245071210742c440025900205600e00c0140c0c0400c2c800503815118003814400e01091030030383c0d45001c00d4041c040441c20680e815000243c0d1001003031180c01c00040c201241d00669161050602c2504a48020094401c41740314408181e004a0110180b1402c5a00b0000b080d0b8442c0312854502d20050004c1c101303c04640041d40c2551030441c000554804c007185516042000034091403900111804018650b048404180c056650328001c0b0002211080003420000060101c0101c01034504140942554002040b200031500100c004020161101050340c081012002d18540c58007084400d14082003044030b0b010690b0300c180100502c030002750b6400f8a060303c0c001c60981d219a80c95031141d96030768540740d1300201100e10401400c105107440c4000382a0030001d602c0340502c0d019082941800b618a0740041c980580402c0740304 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 900800674 1250 900799424 900799429
    0x1707030503100b0c070504021b0604240b180702030c06131709010c031b06090614070903030804080d1b12050a1e05061804060507200d030f1104080c 65
    0x82c00142441c0d2150742c94482d6503108603440e602640700d420f01503034001c00e0f20011703100f460310356800142d144012100781d0310f450309101c43c50740405044026410304015403240700100c0b074000c02d44d060700003608800c1c01007058107a091580b1030040c8181d0450005001c16807500c18140300150207941d05024405115a00d0306045400101031100407003c88001c0003440b0450b41c11070351340190f0580500341007240940c0000c240941045894004001601d011800010060349500840180041d10301000365640c82a6060f2007450543c0409004280c050300080c0004100c40c00070b0240e124101d4001c02e018402110705c013258000146c54078042028003d0f041311a490a01c1070650000d20850144144602d0032903402c0191001c242d1054040d840d0000204075440b8402c081201d2440c41880120360302c0d00e810b040004000589101001442099064000041c08803083e01a520400301a00040008000c168005d1200400c0d2a50054844ca4550180708644000d40b00400103140580800c0184104 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 900801924 1250 900800674 900800701
    0xa030e0705010503071215120c03060509030306180603100e03030a050702030301050d0602071a070903050c09070f200d050d060e16110c1509040b010c030e0d1707030503 74
    0x841c80c1005024400c0000d01a407005103000c099803084800074001c100101c0d8800c10302c01a4010b0255109041110000c10100c0744520341200d00840081102d07840350003807180c4030310050329000e41c0090302c0129841008070100c061900810001c04907400001c3c200092019550201400d4605400c08030821102c00c2c203c0c003030380381c1c844c80c14030285140d0341c1400005100842d5680000d01590760224548041024600001d00b070550084c403006c65a02e40050001d1a01a07a0b00046500d0700901c01440719a0400c4060780d0b010341c04580350a4a10241d4010440b005141211102441d000d00030780040c50001c10302416100104503515544d46007400d90322081900c0850780301140c20703030300071b01080030800d840b1080f554102400d245c9410244030410b206440c20040c002815481000c10614007001c0141100501c030a01c020f440c20311010613480019a0b5801c0c03101405008140c041da4198044d1820b4481000254441d942c00814180c00110718045500070b448200e0100d0030000a202c00c0c45150300 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 900803174 1250 900801924 900801929
    0x3051009050c090609130f06020408160602010207030f050702040b090c030604140910020a020f0303100303120b2101020f030901050a0506060c0a06150909060b0a05040e0703110d080a030e07 83
    0xf2007010302410318102017401c0c800c000342048002c0002d14119003c0000c001310031940f098014030103645481d00c400d401511110041004801400c500c0400242c19006000b9640c4150b0141c4514205000e40002a90150b102001c2240d1160344c400f0050707419039400f00024090400800a2504d0303240c08414002107400d400c80207500013440c40100800c0c40000600c1010201d001d542c05a01c03075007071460036442e1022a8034140310a007c04010000110404000442100d00030341d5210425200010700000f241c51600394180c110100014124008a81e01120300e501e80c1d0003c001071070a12654a00c013200d800980e8015000e0f5199001d02010000c14020f45c1c0c0c00800454440d440c2040203005c055980400200007030002d0703102c0f0720b241d4203590701c003070341400500326800140503d16035850140014000e211400b840350071400c1c0e01092a0900b0310130940c0d0a00c3c040c00071701215055440d188268003080300b80c0740c0d0101142e00c40b80000342c0ca82c0090b280d03016213500d010501100f066040d03403c10101d81c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 900804424 1250 900803174 900803179
    0x15050409110f060711152710030b0d03030b0102101109090a0c08131b0b07060c1107030312150b041a07081b0c03030307050a11011104150903051009050c 67
    0x51109a001c580d00005c0c0d5108080100c03800640901000034440c054058095100b41d080840d03944100424403250320706400c0345080ba003c0b81394082449040c1c003101c0101031225000004990702000203402a0320100a244c414012514078640d103900100980d4a03c8c640820032140c0400c100d0b005041c03038407281d0b400002101c002d000d40461442c00400e8000d00401d08080c0b607280740041c2042c801c4000801e51041624402c00c0c0c0d031030f521070f51544055403141404075035003840c0590000d140c81c481da02180c081c001740f0020305246031440d00c0851720849201003c46200750703030300d08000c0c0c2224203654000c002c00c24244442d4070f4528000c19030a25000318666000e030403504000c80000130340990222005c001b20368050b500364140701c214062500304000381282d018400081400f500300d030400050b018502d215078070341c411701e43c1c6d107601a4241c0b00d400c0240d45a0381418001480306582240d91212018050b00e0301c40e001c6550b0340ca0391454000307031404204055940740304890900005008070301c80d9460a = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 900805674 1250 900804424 900804427
    0x70812040914062b051507020c011d010f090803031512010605010912050f0a0303050108010612050d030c050d0f050708134e020601061e0315050409110f06 68
    0x30f04086400302c0705211a290305114000c44801d8a44c0440d03480e9007059810100f01e44010408142903501010203582d82d8000d8071850a0f02c0d031a0390f215500e01c0c08403038080702c1c90461620201e0300542d46c441803c9034071002e2000b200f002150641c010406140714003100d54220031054422024001111a59006070f04646d043c01c20911099802100d400d0889010000c81e4a4900c2d25050590a00118203021169070281400380b030140342d4035070085030580b940d80300200001d6a0320000084200421030b0f004059070400024042c0c002d0199001030b44580f45070814919002d62203650000726078814101d042e02c1c50f40c0b0b0042c00781080e4049601540700b040c1c030020020000d0700d500c98508a420081d13a5a82c1b120001d901042c4142074004166403c6220360543c5805c018a0000d4000c0c28012001c50030061082400015940c1e200e0071840050300c003041300010b224000281d00300c018107843c1a03801920081c25100180325103c40c40386404083c0a078003402080c80341081000b02004a038050303203100703150 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 900806924 1250 900805674 900805681
    0x140c07030915091208090d0c03150c020c0402130308161109090a0f080412050703120e0a030f0c0b03010b0307031b090504150308030415050601081314070812040914 72
    0x2085020f000a440c512589809211214035243c030030f610800201540064030380384c80c9000c001c1e81001c0181601d21030f0b070485c000304005106110823610f580040c0f4005900040d20140281025401400c28103010650202801c0e241d4850070410341c02080c192884800126029051009915601c40c0034481154038282509200f1700c3d241d039450050201421803000f1005c0c407010019108129001043c00e00f48031000680e40d0305184d40c4900c1c140c442511114030524202126601c148040c10b00b150004000700c0b407141c00d40c0c8038140310180114003240e03802031101c0045100bc1000c4041c50080000b00407696276480d051000034107988a040c407903606030f207900d000102c059400035403403c240c1da01658005890301201601801580071540081d110000020900c0144000000340903483d000c40001409a80c940742e00445a403c412154246114910110f00c000105011071080e21494280c04481c0300301d4581e1100d40c01d02040d0380c0c0c00b0b801c0e01c0001404000b51921400760507000b105030366001d0603e25 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 900808174 1250 900806924 900806927
    0x50106140d0213080610080606030a02010c1b0b030a0902120706020607270312180f0e04080c070e1e0c040b090d0503030916080c0d0206030a140c07030915 68
    0x2a074501c4007291500030800204051059403c1d030000d01c0000121031003410a00c0101561a0540c01580510301603000040d66074100080d80c001c2c010790680d039012a601c069210500c100003041c0f050a00c5000c4c0c2c420005450040402079402046403c50000e402c88a520400184540b0102640200c0d009184100000c070380100f1603651202d21820102404d11003203031803440e034581610070f4141540a0000200902c4904031908000070700580700d441034580d0202d079511040b0701074030540c481040c6030402400a4000c40e40303047d4005114400a60501c88807000ca581041c840340c06c800c050805c0d0b54204404d2850080e115034440c80501c800d00d0b09418042070152140c0700ea0301030448901d400159070041511001c1030404015000410788e81c403810f019101c562100021046107942034070440c4042507403580861108030209004040d036a50700762075821310406030401042055420b907280119204000c400e40d0052260031100c5150350b40721168600505000903540101d015525100100030149 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 900809424 1250 900808174 900808177
    0x14033307031b0302090406121202010c08011a09060f18040518190302190b0f180c2b050102030a05100302030d05030417120403030b030c011704060f110d05010614 71
    0x2c1c1d05140c0035a0364a10000810050201680820441d1024241588c14006000d05c01c18004030b02d40e000380808074a40100300c61100d8280198441d000c014620802c0c00b2490704000c1201800262509003044809400301441350000c00c000401c1c84a94400343d131951501e4803ca5910203039100014069444e240c680b190303507402c9818640d80d95a9120031a200749030080201ea04c1800ca406004e003800801481c01040d000029594220040c00c5100843c1004116a80a5482c0505840185462612641000070f0428202e01d0103400c051800c0804103800b220001a030003550194001607600d0405020340700031220000e00000034655182001e000595001c281c0003d0990945046501c1c0c0d16681014804a024180364a80600c0700145403003180d0228036604d40316074041e4504001d0384114109154894a821000300c1c00500e0001e91000d045410502994002c1d001d03030000500b60401d1500e10048505840c0c103800300e08008503d44029038194004c050140c28507162001d4036503e00c035100f4949 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 900810674 1250 900809424 900809471
    0xc0406140310081f0c091802180a0b1317060c1e030106111c020309100e03060405070f0f050f0409060f060b0a03241403330703 56
    0x80110000c049034892140b2180c480c080c00c030f40f6068980707000c812200c0f011038140c1881c12042407405e10b05d5820400740560131210480b0500d140c03204142d0305040120000f0b41c022004d40e90707111403a840740708491b1204aa06409071100c00d00d1560359145c86070310060000c040340d0205214005d44907a01160a401280058002d2078040340c1d2525040a10f00e46521b0240b11154466141c502100000f00282d101c40740c0c540b051404000e5802001040d40c2c503030112001c207088a0003681c0304000241560030075011801700725000313240c4040b815402e40f00103801d01c041034070161340fa80e0002e0024025541848601001000340e04002c4010070705e408040b805505c0300740c4c0c0b058440d030381d51081c810a1100d03942041c4a00840301d501000346d5a00c99050030031a80200b424200002d1034000e03800500c841a4181104900c0390040346c080b0365140c85541d00143c003060418903054014000c00ca03440102d091004103200c9488451b00c50b0014100000c1542c003400207201204060614111030443d0340a82000f100 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 900811924 1250 900810674 900810707
    0xc0409110d02240a0e0303030405061810060e011e030b0403050334110f0c0907020f062508060d0f0615081f0908030f04030915170c0406 60
    0x142800c82c00024440810a02c0280410070354120751030051030b88000400c020200c075102c00d45450701003800c1c035980307006c2250001c1c441e5200c10041111a0424400014040502030844190781400444503042d60503603801024010840001072001180c09407811a44d650035a0750a0300440c40c40c0c8800100070009071002d03044c00b2000011908044851614000c041d211040d610140390510b11804c04c028021107400c4002241c48400724030005000c00e030020f01140e004014805007140000b000403400c0050001c100350711480c400d4420805040c05003c0c8100c0105644104000c01c030202d12a070300054103050310420110340100a81030381c410070304180d202e4000c843d4103070046281c645000100000b201a00552101400002e4560380c002054114406010070000307001c8140c401c40c10a403a43d101c0c008240c0c0ca030600c0000c06512020024903401406403130081081c5903102d448800ca030312610031040001d402440c0403400c40301000d101c2a0070850b903407451481c1528000d001080860300e8400200e = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 900813174 1250 900811924 900811939
    0x22511033019020a05010614060a1d040c0906080a02030f0a090c0b0c0d11010203040521070204090c0503010c090506091e0901060315060c0b042a0608090c040911 71
    0x185a00e01d00c041c0d9501c5440001c0001c15520014406903842200d07038402c407203940c01c091010841c2004101810410a8040c0100b07044c404054000d0302d0b01d030102117410000d001d2844a00d001d0795a18001d42801b801503407500419207041ca6401030500400400d1a00694010130a02c00e070080b0919080351321020203440007900305c04901e485c1a224000303510003810101b0109910381d604401080d484200b401c2070f01c070703d15240d00040419083c0e0004640107001c680000342141c49420390402c5040d449113443c4041464010590700007022240300c1c440603600113140000600441c1001d20500d52010201e04112002500c2d14000032540c0c440c42c180c182c055a03031040075884e004140512480c002c0801810308440d903849040050060020100d04500c91420341c1e000070740b0500400580304000d4100c0c08800255031a6120f611800c61000d4604141c501900003c1c458240514051b0b0050320700d56503203240078182032058501d400401c8003a10700c62481c042c0410001440320901c0c0141b100103481700d0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 900814424 1250 900813174 900813253
    0x290a0c0b040311120309010c090305121e12160305060a032303030f1005010918020f0705010903020604020f0301060b070b0c09120319030603150f02251103 68
    0x440300381c000307030001505600c10015a1840d01100a0217180701d52a0390000b003001c9410800200d5448540d0712001e011070300143d188900310380a0b58003e00747c1e00c80010381c007514003066010240855100c60b021080b031407020024081020301601c40754100010b189001d00650410f1000103c501c0190310000b02079480402080000b41c41600d20b54820342c000c0c1044d00c0c0c80e4074010780a4400008112a24542403141d4800031906600a105d130758160b0b406144210034070b11203641c0d102d0095221444110304c0120030311156000131003d000322115280b00364060411814140305004055200c200b03441e1007641498000d200764494803058071025500702c407002c8280e8440c010104a14842c5250740ba0700002130807d14000d29000000038114030f90003040c0000d011824202c12011514103000040810703515014190441c06aa0810310124001d01030051070221824412010700b00142c82c06c0704038115030154030b8107002a2508120600001360007074564518051211801c1c1040c41342c006000c681140b608 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 900815674 1250 900814424 900814427
    0x4050906090405300d050f06030706120c051608090f030708030a030504080c011803081005060906070501060b0d090b010f1202130908210901150501140702040501290a0c0b0403 77
    0xb001c031110313490440940c0e00c0440e031201902929040b2010643e44c40b8000c04503801c2c0c100010b40340c040790415990b208841a642101c4806020f41841c5042041014072000c444411080c904d41401c1d88074090380c0d50744102000501690480e40ca0060748207400c280000c1041100c04000c54000c1280c07864001401e41c1c4500d0480350600481d0088001581b0f040702200c064400c0c0c0c40100c0c00b0500179211072101e90b0710521040030007003481c0200c68014105000031181418100042c1c55000e00c244008100c90303854405594158002d080084032241e148c001a5090290507540030f40544521041e4409660904014030320014442600038004c0c00d0004481c81e02d00700310f61003000f10607400882c941e5a002c0b00b10110340c000592041c0b4407100407050010a002c0d641c14440c0c001c402139040d0b030401d00305251500640c2e545015080320a4011410422100160ba0741c1c8200c1d07002c0c05010719201c41041020050602d17091601d001070820310802c011403104150004800d41501d54031401801d49540c1d1840e0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 900816924 1250 900815674 900815743
    0x16120311030a090602060906071b0213050a020d110408061308040e1e06101e030e06010801090b06030a0b010b0a03062c0c040b040311041107060204050906090405 71
    0x600c20081d00000c034180c0d0900f0341c4110440d003110f0080d405c880e61600d40d039070090f4403080d0645030400403c030803801510140144095074580340c0c1c0010200d080700d10140c20f07450b040d80d400300d4150042550014010111110b180700703000c00c000c40e0700001c90400e0f060a0341180d033f0740b00c05404d2000101c9401c81c0d82041050001c211005480c94000e0781100b8185140030000b20080402561045100000055110700f031104c600625a42580d135002ca1f500c2e6005840510040888084410181c881d90440e40c0c80c00200700490003040907600001d401e03105810040d10004015280d1442038000b481c010000c22007040809054504074140199100704d110710640c0100b4440d4004e03580901540c90100005c2c03500301c0454101641100003054a90320101c5500c4684103a001381c00400e4000d100034004600d05c4015142c050130301078400a95808500f210044079044004203e40c0203400103130610035401e101c4c40040e00050140c0d6560194249559803d03150600191382e40d0003980d1404000780c40803010780 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 900818174 1250 900816924 900816947
    0x140f04050a0801050103060f0e1b0102010b0d0309050910050604062706081501020d140d0b030322060305160309060b04150e010b09091b040801022a161203 68
    0xa04070300c1e08079901c500d00c038041c000034070060b1741d180d00d40740281c0700740382080c01500c0e000748400c006040e44101e0794980c01c14100300380b01e000c4c0c110340d44c400c1c21016039241e2140443e516070094440c500928030f01000c20600c2e20006014003005d9440160030080c9442e424180d40584610381803100568078400b100901d4400b0400000707031440a407020020310990020340180c0212040081c0414110061005980d10400c011030000020011400302c1d504080080c01340020364241307a00846c0381d81131103000a00d0341d00282d10644125804401000e5071611210611008040b68101400740d40741102c1a8090390f01803842402c18503031a14444410000694800001d01c00010001c004001940c081158100038038010b004014805000110b00301134a0004c0d00c6550900915510b11542c0700e21504956004540d03881c80030070ba090102040c1d643c2d007800540050b241c4044d0204011001d4489401c595807800d08161042e0082c009c0c514494000351440410b68060524014a46c869490215620703400003 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 900819424 1250 900818174 900818179
    0xc010807030e07060509100801050306060d0206070203060901020a110601030b060d03030b0a0f05040c02030f03010506070f050f01021e0304120302030c0729070908070612020c0102030a090b070f140f0405 89
    0x1400082883c2e41c200c80a44442c00f02507035401d51f082841541036640400c20f00440f503040c1d025100007110740c5440d02c0200c60f464409000141009420360101e0718101081d00d80d00d24594000c60403092150b44210522058095480140000c5d49507442d03040c400341015001c14007809001c2c054100f4140641c0000d450514080d0150350080d41e943e1004d800b5182501a8511543c146045d5402d043d10020130f840301411042003d519591901c010001c03298000e403811039442c0c0040c0344a1010500034411041011540c0f000560344000403036172107140c8035115260300b152030b0052080c0130104000c44903681c100d6600e4180107969071500c00c02c0d03403424021600d00506480d88120344001d040c0c816050141417581c2083c50240623200c07414240c6980c4028001c2107090391201000b007020500c142540401e0a10240340141713003102150009099a1040795002c40303039511507403507204000707660607002d9215585103000000b401c10114001c200c10b0401c032a034200c500340802d10324401e8030400c00315802002c00 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 900820674 1250 900819424 900819433
    0x411040905060f070908032a0a080d020301080106051e0f242d220b0403060207033b03070519210f0605040f1e0209060406080c010807030e 61
    0x202d1000b64400302c40113000550150000110300c00700006446640f05011000110340d0b070750340f214204410300b44844d80d00c1803084011410210703040d0300061004d02000c2c20003587d01d6041c080c050b42940d420303901490285030034504941c0b00c10000000d48010440403261308080035045000140c5102c07902c079284191202e0107440502001c2060020454582001c0e0600308256504413008039241c001900a84a00c10402400c1300e089601c2450920f4040181d41000f91583c840d620320480d900183c00c2141d00c0340e800030b159410b040c2c03c031b07ca250030b41035401c29103040d43c00d0341c900101140c2d514491001c00e403125265040b0003030b41c09001d00006401c0180800140c92141000c1c802043e8251090725200c6400d104030314025295030301255800c54101c202044583d069595000c000c0100a0090341c81200d442168000a40d07000e40720b41500031811392458440c0301d940100282c80c580900301d284141d10741801001020008544a000110309003030011040d503c001d8141e01800b07000d451b8186e0f0307008 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 900821924 1250 900820674 900820681
    0x120609270d09090603050601030b09010e010203011403160521010b040e010b010f080603120a2c0f0616240c030603030905030609120f27040b090c03041104090506 71
    0x40001d00403071004440d540e6404a00da40c2d031058400c40e4014000a0903a03007043d0010300c041600719200c2c58100c81118000140a60001d03c0e50f800c82c0c00a0308140c0c41c291100c2c04e160024a410400c4001035210351060070704003450000000c21503201c00b04964001d40a001a2802414003907214042c0094040c00500c135812041110314000d10040304018049610b40c816a940d29110301c1d04a403282402600500703402e0300e20f1200c650241c20011540003005108403401245107140c40c51401c048801c0a519903c00c40c001c0108810000c04510303050141605100e0450400641800c8c0205070b03401410307c603020f4800418403800303080e0704c41000c941e45003040740c0c0c1012150700d43d100c082103c0c040e503500d4100c01e49803010551154019030340c14400398069146081400711038070050a10200c42d605207403820080d40c80c110b840310061403800c01000034550340100305e82094007804445400403555406246800088008980405400038096940c0642d5031005030700c0d9580300c2c0121641045c02c0798540e18 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 900823174 1250 900821924 900822001
    0x1c0908070f03140d0c02062503030507020f03131202010203070f0b10050618120c041a1c03020304090216060608010c0f0207050d0f0f060c091a120609 66
    0xa03074910048841040040c11a12041d8000c20302440f0303020265903501d07440c21a44c003040a0350300920350401c16001410480c0c01e11000d240017440506200380c0300460710b0320f45548040c3c2004203d4196103129001041018500350482c0750250640b008414002035035140d03800100d1450240100c02054001c0d4024a0320900c44450000c07031203550403215003d00c050302ca00c140013207406440030780309c0c11290340d11007100396244c8140c010110343c109000700c5840402c800002401d4441d60b03414440510b0000f04222054105440390104502820109030301690107607800a40e40d201e0b600c00c00c080300380d0109007040c49028002d5100c400703039040b903c184400c940340c3e801c09009151840d1030a000c5441c1000112003030f0300120ba0001107680c01031800301c21001c207407207406a070078542e04102da000602d10500d400049151158000c80e0025a54294541d42400c0842e440c0d00352031402e50040103c20b010581c0710144070b00d851640540107441620311915440e03203410902c0034a6034182200c0d00300c0c0001070b4062 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 900824424 1250 900823174 900823199
    0x60c0309041d0610270905011e060b07030f0f0507020604090509100504020306011202030f03030a062d1703122805010b04060305100e070c02130b031c090807 69
    0x400b2030001d4588984689203190030500061240017a143c80e450302e03400d00f1205800c041d0709083c42c6940013180034280c1e0350f82e0a084888140803510b407050700314800355841c001c501c0361001800ca01c0240b1450492142c40c060024011308020780700300030030307880d1000700c480c440d1040d10341240c0d0190589442d242c1b140710840c003402e0111500d072698400e582c0d1a015031091b0340205400340347c0180240c2002c0c3d0815051a07044070007090140d0701882502110350340d80c042000110f200c0c9002041c0080c0e86402c0100703110074031400001e11603041c3d10402102025810031401c01040350500d9a00031101c01d0484d070700e242107000307844108418410800402c03600d4401c074211600034003401c0c0101680c0301600c6070300404644081c05079000c08070091005001e094065844280c00c1011035400d60182c07070b510301074240510002c0380c1083c0014140d0044a0031400c000c208514131026511050000102a0011a6844580300d80c0030001c40e210102161180d405902c041c005004c0c40c900303071401c0303c3c0c41c0c0b004410308 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 900825674 1250 900824424 900824471
    0xf07110a0b21060d0f020922110901080a03121a03030a030e190b150f0d0507050913020108042310051009051b180603011518080705060c030904 63
    0x85142040003e4074034600003600324480359010b8901a400c0da401c0e001d1080d103101c0188a24040200d80009082c002c0d840e4640e44035084c0706040d0400b5064020052040c0d04206a2011004c0d5220501d40c2d0002a007156078807a501e0385601c00040d40172044800d2051111041c0c041e0354142c00000398609800b03502d82c001001c04240c0008a40200002095244132401d84601c00f92003100800c01140e00901c0f54030a00c00741050041a02201c60a04c5001444050b44174008603540e0740101010040340c04d0040341c4541c0300d45c0b820208045003000d90006801c60600520081c0f030304000e142d01024404c1100c50b5400e80c0d034a140104ca0005041c0e040000041c80180d9180301d154100c1d840008401d0180d0160b10b11540303107031612000300200700d240210a5009915807050400107003c0044158035288042c5001380612000103000d0210604080c7c119040381880080c4840a01424810141b00258030003c41c3c8007504d41e60703900c807101022941180203451031182e00c030742001d40d55a120091034001100 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 900826924 1250 900825674 900825727
    0x408070b041202071514030603030c15241f02011409010b03060903030405070b0f09031f050f040309150c0606060c050d021506060a020a060f05011a0f07110a0b 70
    0x204d07942c0f158072250f561a0014115070004805030507a07802d140810700035541014011b41103900302141102c4250503c2d044000740404600e2074010014100400e4120402d8080039841826412481402042c11002450f401c80303100304031034228484661003540068001880200180c0e2a402c08940450180408081c01440303071142e0004900c0b000c00c08000c8034084c80e030001c0208441c5180010255083e00501070b11012404140314902580d10103101e040b040801403071243c016540411011001c940000c3d048211080044080000007078000b0740420a071040540413591203a45a0002c40e806841018010a06420311600181081c2c10410443c0e60034480c5041c0d030f041441128007242c1d501e5040c2011410001c0550104403e418000b00820208240340b040d0360030ba40454481d1800e80743d541406069a42e070b6000104180c0303098445010f8141d1903420f0703981c42c09000301d0040002d4000c1031006800720040041c107407015655032550000824100d50021b44135145594404001c01d204446d884 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 900828174 1250 900826924 900826933
    0x1c02090a021e03150904080d050108060117030c1b040207200117151c0813030c06020a020306040b0c120708160801080d0f030b0a080714180f0408070b041202 69
    0x88100b841d28290392040313000000c009030103072480b4200640c2d208003800039284070004024011241300d0a00840c1e0107080382c04010903c035407501d480a0290b07004013182c10714642061106800150021031040c5ca19095202150023144600c80054002d100f480c600030b0500d14200039015000f24a1402c2d0240380000340c807040403101004c4070041000d0300c1102d810a40034055040320096107805030585600c035020701501100d000030f07035540c03c0c0243c3c42100c1215201d01150000c1040000d4012808090842880030b07081c60169607005c00e81d5098081c1004202c124010009a03944881c0b0050703a032000e01e000c0c007920392818004030250408005458196980c10003601e0383e400329000b840142c0c12070b07400400510109107092003c44084100c0a01c0b241056210414945240d54a4450764040c2040b0409424418a803090755807044d282c804440c0d0140c001ca080e0317075420010f0004561351101040b6803440c1c29544924000120f03103e074100040c01e540c1d152050006000307a14205d0040d448030768088a = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 900829424 1250 900828174 900828217
    0x1005060f040506150d0b0a140f0a06021e100903050a090e070c020607020f030607020309041d071806081209040c020106150c060b130c08071d1c02090a02 67
    0x8802d49504031042c58105003c0d980c048034401c0480002c0044a50001000501044074400110700c00c00701e90100c450206083c80490007441d086254006003113084420442d0039143c904007079140d041d824041c0e0640d0030b0741e09001d09810002d014020710910440e0042203500d15600e000b0304150021504900054100040070a106010100340c82c0100002d444804071401c9a9081140b1075200b0b100403a000198014660450346040203142e0042045801450b101d030040070500c0101e400c48050303142c1285c1490f52011089001040c0c0c1e0041d507042d54507603420340125010940c058103140c5e100c50410711500d040c0a2203140c0c168007030002e14004945c10300c16510303c00c2081742038480500461100d038000000c02050359000d0701c038082e80d00384103460100700742c030790103000440205101c20030f068110b480721a120800c0354020141c0b03601101a050084000c10b01e55001c18030003040c1c0807514040e0280c0c4507440006405054404151680144621601d1030301207020380c080e4110303500001c041030840400 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 900830674 1250 900829424 900829429
    0x17090f061006050d020904090f0302010f0b0f0d0b0702070f0b0a0f050702030d03021c1404022b0201230a020718090b0604270506070f090303021b01020304081005060f 73
    0x10300102c4910341c0c1c45078244000c0c5451003000390300c41c10f125a4030a550303010781170004a07549031010300c5c00d0098000044041040800070283da47d400d1300c0901c19016000108a40c1c2d80c1c45410100d42070f00003100d010240d030ba11100383e1402145400c071426140c0c14500010351141004003c102c804141e0703a40c800c2c0c0b619042d0065805000d08000254036402001d48484524880d501401030102a04209200d0300c107441c940341c2c22520940a06029460180200819420810190000090103000100703c841c80d8400c1d0003580e0001c2c20000741003120008028032103004006150082d605024111a0307140707116040659504098461802440700e178a03100b80341c00e03080344107000b1040e80101c001901ca50340c10b070400c4000c0c0004034411016a0311404e20780052503400007040d1802d0720400041c040b5003032040028102e0462445101d04000d0110814800aa4042020f000011001304140110f621510051742076005507040044030748540950034079844e100ea00403074007410041c2c44819104001406 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 900831924 1250 900830674 900830701
    0xb07110618030c04061d040602040f18060f050901062f0607030606030c0c0f05011112041401060510052a03181c03140f07080a080f15010e0117090f06 66
    0x20441d48901048080c500081c2071b0140d02c1d402442104010b14064448050746612455a0000c0c0542059202c07503801840092240708041e10741c0d085885000c914160000f0364111050080c00304110b100c440d44072103060744800a00d0b902104805c650444a09201d81d2a5070705412520400001e09040f4005003040c02031151400c0302c603031950350000c280700716182c03400c64020021044906641e540c1d81400390380381c820043d010264848032518070604003400c104400703d6103c07244080a07403400c90108181d0f07440448040c0d04a0303240c00e1542d04c0c1c0521030300000c0002d003100300e0035039406141d505c00c8071500c4000c802850780401550350000c0500417001449002507824040501020182010001190160712400c0e08142c0102c116803401d0000c00c4230045c0c44e0000002160f2541c0042420050031f5005120b843d07019461001400359480c152925003200c02408006a043c4410505080d9840c7d11070344162040081001b014030311307400c0441340325564a40d42c5120100b41d008081c04910721266811 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 900833174 1250 900831924 900831929
    0x402040c03091221110318032502041b0305220f03140c01060906050a150903060b12030f0909070c0506010b0a0c150b01080703060f0b07110618030c0406 67
    0x1030403803d850714250291540020720032a084043d851000a805604050085501d81d1410160103610ba044c17180c0fa0070102d41c5050300100a42d0000c1c001840804d115207880d1807070400010301280100c0c1940007160003004801d0f03102a02821242a1020381c54060304554041c0000c00015029809102e81d80740d070b850251103000b044200b0301c403400c2c004a842007010a549041c3ca215403880c044040d103095003140d640b03030300070480180c60785803c10140c030701105810300420394500a003c5886158000504c84042800f004080c1644e42c1c0442240e030301c501290018001c00b032800c0343e58a150102c1900c80c2c0d604070b0401148103507203490000f0320543c81551503408044e400300003406141d0a190b0592004e801c444a00d0742007140d00206c0b240030607c900410301d080d2000075030001e801078240d40010040500205840c040c10708000003009610071814240301156211210643c03242c0316440c0c101d080d0b22040c201140d202802161003021a40320f8880719010703800c224122403103041901c0503c02510802d1 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 900834424 1250 900833174 900833183
    0x6051311030402040b0102070e04030903050105071403070f0306121511090d060b1804081201050405060f06071a0c0423010e210715121b0c0323030402040c0309 70
    0x90002c6401414203070442e0181a00500550302040c1d1104281680c4400c216800e40014901d000c040050200030b1040c5070300252280b034400048110316613540310510010f0119070070013180760960000c42c1d109622820240072085860002003c0c54100b820a04100b998540501880e1225054084030080f04440900710040d085207440203040c0c441c41d004044113144242c03c070031a5078220100c00c240c50181e602c110b02c9101c1709070b1034801f107200712510b4003c141c00c1240201d280000b03005181d5510860035481c900c007210322030b071b98503c03038502128210221001410340c0d041410912480b80c18440140042c0c1c0d0794012100c0c210030b541c004813080b428104200b02e0210b01d01c4819a60f403803c00c40c00e110001c21900c400f151030346103407003d52071601549a110070007000d40804514074003584090312900b103061f0f0850600201500c3c00003406030429500d00310b010311008140d03104c00c040c042c00b22998081194900700b608a40341015078495644102c0d402ca1040c0e02d00400450164020f104903511b06411 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 900835674 1250 900834424 900834427
    0xc01121a0121060b030411030c131505120a050d02070b0f0c011b050309071205030d1518020301030b07051911030d150e0601050c030a0e0f03030d06051311 68
    0x100015901c408902c20300c0020100468100510a031640c042c01d80140407100c07015a480c0b92504180000c2c2c10f40b00e10395480b0f500002ca14104030381c0d130801c1804081c40b6003200001d10720301b404100070210420b50310643e0807014260300032440050210f2540050b07801b500075a1385031500c101c0e0898541605c0e01030018008002c0c0710f5440c0401665002c1c0503883d20034000000c52000c02d220741740e0000d503001901800948000200103440c0428004080203200c906c0c030250810b04a03035a00e80e120f0090041402e5816a01d0309800300d29448805050020039601942104240003817640c0380c043c1d4800d020a0710510316036008900441c0c49036040700c2c6500c503500540e80e9400f15001e41110080003140341e60b40c50340b009101da0b4910100c54070070442d12003c09410604001d00e0400e841c04c958400420721414040180164604101e020040310320080e81841c120160342145000502e40d07142d00102250944070104d003601c040703040c551194003540e0080300d120040d0000e080300d2030259819051000c1d2043e60 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 900836924 1250 900835674 900835721
    0x609160b0f042303010b040207081206010c0f08030106080c210606040504150e09010b090a240305061f0510180801151805010e042405090c0112 63
    0x14640280149801c0203500a14196a426902c51802400b00003801c06180540b000d01261030244508004428243c07419820003a0980366402c95001d10b60054284072440800030300c071680301d80c0100d0306003030b8071406140c0303000007034189000943c00c24000c00300401c0c4100042505c40c200c04041c3e1781c400b000200010200c42c00500740581c2c2034000782089410070300909c40800c0740d603a03a000c0c8400824105007500d038224508110540c0d8501e015252107140c0e4903001895243d9125a482140d02c6428104042400010880900d400d015410740c005000c940082010041200120301c1a000312a5030700100c2c110380310f10034400e4140105114540e404083d0700200c2e0741c5c1c64025000901012540d03031b0042581e80d91343c000c45094850642e44100c00c000000028000e0203881c912888c41413204d85010007841d81002503500d001c0c40085c00151180c40c2e50841c0a1407000461048030545038071b0081440941003000b9030036502e8100b101400e0202d07010103110418207050b441640b0400080b10b00c203030801403 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 900838174 1250 900836924 900836939
    0xc03032304030c0611160302010b0f1804171c0c09050603191b2318040b0f03010c1e180501030209010504081203010303031a21101103040203060916 65
    0x100c4048100e0b07140c0d031280c105c0e080c4404407001510900313945195403506410070b480d0082c01c41700b0141946102361520300c20780c80e00340c803000042280d5800c480000312898403039081000980740460185481c46500144001941102008403032a00d41c1e102000d21100025076003e032640241801020b402c00c1c030500004120f03e403490f041041e5042e1054002a5254159480708131a03103c500c5110042800c100d0321020703001d000608044000482d02c080740c1813108061914039032403100d007041c91040da220f08071070f0000e98690903103601c441c0d0020001c001075501c031172000d801489041200c4a100720724000c59080c41d4043d4540c108001044002c8101080c2890300540c02074010070a40350400a05120109115108201807081003802150f00d944039071540c07a004082d1002d2030601d4204150407d8000340b0341d107030398071078540444e0481482c42011004c0c8480e00e00e4449402e00702d802035424002c811814000d80d00085010b5802030f0180e642a03914400000d54640442152404c094040704080080c403 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 900839424 1250 900838174 900838187
    0x1080c0d0b09160906361805060306070f080609071b060f0b0111031603030b04090b180703030f1b080316180f090b06040807060c0303230403 62
    0x4903018200141e03400d00c08010414804044a915158211040c040f4000d25004007001c3d00800581c81d14003841c0b81e072500040f0304224000c1c440c0f013000d010803081d00c01c07000c0b1700c0c00c14101070401f0781341c024802c51258040d4005024280d59a40c00382c000c03100481c030100d03c0f8403010003103000e03284c0720606551240018803030302050007400c840400040301001403081028800c0c595100b800341e0408206980f8429600045501030f078000ca041c0810401001260080441565010941c448222440b16100c0c1015000380455004455019103010b81e080108041400b078603000301000c03208011280010701080c2e90712019404040c000c581d01034100002c0900c502250000581d10f0310725040c03100020f54440d041c0d60010f03201c0220380b05900410f2010203034040c0c03034824068224006017402c81c0c03502003c800f84580e41e02034070034202d4440b40f015801d0b480717034000c07a0000c0c007081003141c484613502c00c001480802903140c00c800207410090124002c40b03e4180a4024200320b00a208050301d499805541d103 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 900840674 1250 900839424 900839437
    0x60810180207060c0c061413060b03010e100f0609060305491b08030a0f020906130519030203070512010e160501020d090b0403060e0a050604061b0c0201080c 69
    0x815002c0104400080450044040044090b01c6041c0c0d040680c0c68528141e0f000c1920740380c00228940200501c20100e01143d408071303904544001b640d00440701c01310f80500bc013641d60300028812034a03010f110f00e26590102809505e04101048803e840b0300c6840242d40040c403018001e0380c0800a012406800141004400024660384012540280b4503211203000004403010320988500800e0714010340014859001000e011051340803418180e903100054003025049085241e943c09400e6000310b605c0e41168807040e00100001d44620308080d1001d40c401c0d81d8050746010308428040040959041c14140f01a01ea0050240c03c06c90704090603c1310301495002003121130b640b5413010718050300c0d0600c039070200c660051130240c00d21400d20b03001a280080c0b03010b60404101c907624081000544034800e0f10306032a8491408900d018900299502d41030340c48901501070301a10302071004201d02030380b210035030082c0c1644010501c1403820060b41c451052204c0640405c80c1e00000074144200040280301 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 900841924 1250 900840674 900840719
    0x3051b0a02250914092d01090503040504110f0d05070e040f0c020105090f0a0f020411030a0b04061703071410060e0906060a180e030f160309060810 65
    0x403510040007881050707181c44000140c1c00d04642d607081c000f18001e405600703213000b160401440c0c541001e20003103685032102c0f0b003070b00d084801d850320301d20041a1021800c244802444024004400d80b403d00588951180c0300e550b00c41c031b01d01b03203081a68070f500380292841014010b919500b0804081d441001800c40240402c08210707801d01c11046a0b9030314410786540e10840400007a814940782d0b0084d084820161036041c1c030b540a201880041c40700000c5805074243d01c09071008000d140d502c04134002c1c01703540824145c403c6011040102e012520791200d003402d82d0844047c422641e50306898041c484e02c0c1d0a05c0080b41d0401c00c502d00104183d054180401c98030785040b10741400520780044104d0303985d42c009004a0b0211411b11080541c00c200b078942110080390900d012502d0000010804140403400c04180ca0b05c9181c4940d1240051007a10030f20380701e1140655465054048840f840030401d042100030403902c080100b030151140400901c220f4400e24454242410080c0c1c410784041c07203446104 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 900843174 1250 900841924 900841933
    0x30f05040b0f03041a19090203191a070f050307050a0215010801021b060601051210030b0f0105031c200106030614240102030d05091501150f03051b0a02 67
    0xa010141e000040044110b0032160540742c0c240383c6008050b00e20080b91080803426004107100000c00440e0590005100581c0001014840c07480800c1c00c007070f00182d038500c019456842c1d5005000110700461a010800c0d070042d0b00a81e21008103581c00c0da59944144001901400003075803082c080e1008103814a01401190b00510005142a24042c002d8000c5603c0d6500401c030034007922144e5250841d01100780b4007410351803030700b80c0008203280a0115114a01085200800d00300f000f44e0860b80055500311204244924010f00c01251a040a20596000780f00740b81c0c03907460f8030302507040d000c010f01c00c0b980c2e030031080301141d0010252900c0c00110301d0f50103550724000000060007611602584003004a1003011314a0002035103a04e000d01110043c10503d211880e01070b0582e4040205c0d880a01070000c00281034075141206440c01072404202e040c086511000450080707a1110b028145942c1a910030800741e1041608030160b44041d0381441c0055080c12113110161100b602600c00c01035144101c8 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 900844424 1250 900843174 900843179
    0x408120f12040317090c0a0f150503130c03032001020304020a030318080102180a0f0807060c080c0f0c040506010311030f090c0d260909061302041d061206060607030f0504 75
    0x103d40c00f090542d0359a20130352110f01c283d98503040009040c00100409a07120b15034902e82480031007409034007100c4504000b030000006482c2ccd0f5200e40207412442d001814400d042d80c0340d18001d0810f00203060740e044141240f000080c4004014000c89100e1030f4040d2054041ca031442d0790968849007000c0312840100c040c1400450303001c00074400382c0b0720402e2200800c50410246400d00156000c140c00582d0403418540d0140706124001841fa01120100c1c40d141542e6640790400d140035024403034400703e0324000c0d002400b094820018045082c04011501000282c40344001901101e00000345581b42400900001e0391842622160b20360207640303242a10358a030b2200c0c0000e2030110a09204176004840701e641ca01c141810451840c1a5005100c2440e01c0c240c440c00009400382030003414684503503032052000c442c4039031940665004000b64a6100805801054a07202400c0101e4030513004621505c006071030503000140050103094042c014074504851510121180214000312105104080100 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 900845674 1250 900844424 900844457
    0xf0d020301020c0f1c02060c030c0904060314100b030c031009060e0a0c08070605030f01030f03090902030a020d0e0c0d14070b03010e04030e010806010f03090312050c0408120f120403 80
    0x200010118800068050130fa01010170380f40d8124106040802c40d0b00071030822100c0e0991108498110807000345080e20b9140400c005005005541c2000781040c1540ca400035070042c0010311802d04424401050140009400a059075804501007030303030389607000c1080140d8514080e48001d05d0300d4050003010a50703254044000d4500f6010310400c403a00c5e45943c03030421200310b00740f1000b80500b0030b5251081c5541041500000013400c103000180c040007039444c21404060242050300000d002d0641e0035504d0703280441c0060001d405c52000d4051071805c0c00c0e13300040d02d0001c2a40c80c030340203000f40204584101a1500034000000c0c60840d440c6200c1d011003c1100b01488000d14024003070210b504100b4036051a0007040b80c00128915814044036200748030300e61b038104e910000070708403074a000115501303e0300b011160104002c400d01001d52030316051101c2a2108801001902c0c041d5084926401d03030b03550154030310b1040305440b0564000500c5000c01d04103628004a070000d0182c5080325162074100346 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 900846924 1250 900845674 900845683
    0xd240609030209090a2103020d0c1d060702030d0305090712050d1704021f1209060e01051e150607080d0b040c021501090e0a0f03020d18050f0d020301020c 68
    0x4200085030104004000314a0101d054561140b1000c000d0181d0020ba0341e600c0d9004d125210f8807610f241d4418400038003a5110750b069442c10509144280311980d8071040192481009001e5007644280d0b03d2200191401e1040c00ca85805902800406a50290304002c0b07005002c00b4109609034000c449e000600b03006641800000103010708080e00d0030704140d038406000c0c0841001110f020070f6030f100c03c01000daa00c601c010500344a0007115001d200a00301c404032600100e00807400d0384545405440c006100700c42d4051209408400020041d648032010000ca105d09640001018145003600103008140c16660f10340881c00041d11150a09000d5964142c03250424036034041c0e04d41e0b844552410300d00c0c0502420714003107d94000741104000c44101418400c3c0305001d00c4071b4a94607440c116406880c1001500c4a407504512130440310b500d649402508d03501c0203181100060301101505100091890042080300c100801982c0c149100c0c5040c44220600c400081c0d900d55400c6c406a0b010341c40611 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 900848174 1250 900846924 900846929
    0x20c10051009060b07020f010509030a0b0f07170403030f27050601092c19081308030f070f032001020405030111090616050c0a0b030f090109080d24 65
    0x11480385081d081400c90306155034400c10040d810b0941c104210313422042100d61140d010340d181510340102c0b20058441d8480d2408061301032250f2102e2009000742c80d01800e000c0c0010307411406a80c2c4a42904465500d0303d85038540c0c1150208010400180c0244d1140c2c81116081c07a0204203508400315070343c5290302c1c101129003005104407004003044424842a03024240c103203400c100c001e0980103400002078070042000002c4074900401d500c0c2c81000c212805548148888040c5003a08600d03101c01640c00101c10f086c036445002c203000c82c1c052404420fa40411120420050030300c10680c40c0d00c01044c0ba0300109605001806001c100715454030f44040f240d541c004000540d40d5840d00701414210792852101c500855000d0105403a16620681200d140b00200001c14420210605282d03041905040501d0f500481c1d915000500c0305120b40554400c209051848101d0340c2c495032114241d03030b650758000b08070090030003c4000c0000c1c0b6501c20b02864440c9801000e0f102d4210801c000503e600382c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 900849424 1250 900848174 900848203
    0x91e080304060834030b13180c06020d0804031413080d120203012108120405010917131a09043b061302010c0503030f010303080604270501020c 63
    0x8410001d8400003045220303011080c2108282030101c00c1000a1310280b058010395042546446501526a489042e815520084508100600b0112103070f201c940441d81001100c00849011000860038004195041d00014989a0381070aa5551398100c503500e05010b424042c03000103021445031844107102038005042141c00800582000310405400f0f0132090040114541c010070040c40302c00143d541c0782a241492000c2d0070302902c558508081c05005075003d0500c40c003e1007081000380001504108151801841001c00ca0a02c5003c0e005440c0f240340e101d00300280e42410108044500c4254035203134094400181420719000d400080c058444003038950500014114004a4034402c2221404201500031000232003c85c0555049491f05801811600c8000c141d0b4002c0003964080d41d8825115a8000142c2e99285001c6000190720f030800c1c0021750008140c00b00080e51030400d0b1160f801802c582e00c484044030700182002c0c06258040d0300c021100c55400303202400500508000c07607031000256 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 900850674 1250 900849424 900849437
    0x40b06010e0622030501050109060506040302040225110f0f100e011e05070b070f0210020c0307150213090b0303041202030f0f030d0c031503391e0501091e08030406 72
    0x8500317145081d184182c00c00701c440d0385006030401265444400716811030b607043d41c0c056121100c8030800c100300e1030b0b04107101c220884619400302c200010a01c2c0c6000c0c05408484c1209054003140901042a10040c013094010399052509121035000d8030901c85c14240515052094a148030487c4450700f1080c030714400820004101002000800006654044642c4c500000d040c03d03c03040095845000c0c0c60ba0000480e40000c0f0288080801c3c42120840d03a002104000c030907041c40b40680080d4040303004180d125466500c04902204580903400218400030019030406003428507146400784501e0b0700301c0e0725208283c0f075201001003d00c410048038145e2005182c03501d20b5020801c040d214070410740c1c82014908108030010406a02c004000c1e241c01c0794083c40d181e564180400280400e0383e68186104038030b07140306040d035110b00d0355410640e001149040f00e0f50642d10035a1116242500490340840da00c1e04090040300e01003412544d840c042ea052080205070782e0740030141036901540219000406 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 900851924 1250 900850674 900850679
    0xa02061803101407080c1611040e16170c1f090806060904080309240a060504051b070206072a121505070c0b0c031e040b06010e0622 58
    0x10103000060541440030014400740c07200420032003540500401403000d01000c00d001c1140c2090715801d48401c80200700000d8940501070400c0e0741600c1850440911031030402044002b03a00000c2a0010180e00c00d141d08101141081600441c3d41c41058000d1061b1050b0000070b041e565900c0302c103000441807070910040154103014000c202100e5178005c01c40c01d42c0120284542c0e5154440c0f0705a01c00e400814590300c0e1344030101614142550a1000c41041c65143c2c0480b6032800600c01280c041c403603203041001030980d00c05c1440255202200d460003a45207112044170741d00c0d10a0020510584010107440c50318500ba0764010017100342295509007294001081d5060f000700c04904400341c620f103424074060134000d0b03903074101404100a00041550b05e0f02e001c5680c0c075000d08072411034039a00c416051540e03e03000703904651582003142e6401c5a10758510310700c0c80c4165004800da010700d812007200348175a80c6101c019a40c09625031180d03600040208100c0030700d1003000c8080d10180d000c0e00c0c07001e48400c0c03 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 900853174 1250 900851924 900851929
    0x90c2d0603010e0a18080d090f080c060901050115020a110103021c020d05180a1101051b030c01051806011406040306091115040f171e0d090b03060607140a020618 71
    0xc000341c0c940d0000a1203800d00c100030403101e0003034603447e014020703010820000a290030fa040001042004002d100c0200303075a42c1c46480800c00c2403103106900000c12a0b41e80c2d4094844041c0c074020b1031500560809600c43d40490201e0048800e85401810090315290060098000701e20056120340c00700c9a020640d03501a40c41c4e40600d03a080440034240b00e50307640001c242e01c3d4456100c490002c000310b41207008410f03580d00030416108103141500f816440d44001d41c488035142d520480401c0460b520f08400903040c840c0b4240035540d040d550500814681e800e044014511480646880341c0c0054103010000004c3c411f4056084203034460011040490742050078020848100500b141d1208418003041c007408001041c00e8084400b809a802c242100448241c4d081c94040900c130120320720688141e040300d000016480440340c0784c640e22501455502d032841401c0740400d403001076122004001c00c50208030140103484010000c2004e84e00481681e0307000580c0d940c440003004640005a541c40000751 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 900854424 1250 900853174 900853181
    0x9071511010f0207030e0d0c09020d090b10031a0a1503060903180b03062202071a07031a010c0204020d06080d0908010b030c101808060f090c2d0603010e0a 68
    0x100b80041c0294242141a54082c10405c0703001c50044c000d0513400c9809080c0b00d40703400100300910070b510302107544064100300c80020700070684040c2c40b080e4101c0b02248070f0f414103144e2941201d422604030708000101600b040300141d4042e2000e2600d6407114140c4080082103409040118401d03880010b52240519014100000d82d403c58240c8990560301005000c074480c1c222a41f206040301c114401da2501000032f4400d10b05d2829114500740f02007a40340800210f819640c42032008030421708c2050355000000c8042c2c40746c2c807012489900e0f00c0c8440030701035405585102c80d210301c0104090308220008114a08503500d40e4050403c075400217004055141e0007014020180c40f0310002404807290000200b555058501d00290048201240c0c810400748504c4401440d41d9141c8a060b8a9603910203055641d0242902e45103828101d02c800b040107107c0024000502c45405401b0a03030001400d01410b645440c0c1c00840217000744814484a42c0717540c2e0100440c06080b02c100003001f5414000404402c4 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 900855674 1250 900854424 900854441
    0x8030c07030f031b110a15060603060b0c0a020d1403130608150a0e2e05010806100206070e04230a0621080c010906140402090912070201080907151101 66
    0x525244c840342103810524050521115001801c1c02e5042ca00084c048030300d8540c031241c004d4880b101c0f0800ca08800d40e656003000d01107811540e0306012003a25950041010b100340c0d0341501c29030b80700d00a00d000505000328101846405000945040f600941c012829540851880c02d0340503094582440b455800100954002d012080740c1c0c1e0311251132002040e6900580c1c054a558402002e0001e0000d000d081001310366031545484211411402102003000494540600750128a001d00060f01c0c42c01c00e207241e0b20131246030307600400c5191691002500c0246c1408162504951502c4480c00f0301c01c45000c2d0350600e02c1090418038440c0c03803d100054220f500c95040100c130308804010040c81c07456038100380c130201904005415500c00d01c1e5804c250041942c1f5100074411400d120001200140d011085485113000381e03003c4810390743c2d400321142c807008e00700b41c4034217202418809580954880c0f109641d12654141c1124800c2d80c031400342d480d002c0c14001d4500005407040361003040c508020b0050010 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 900856924 1250 900855674 900855677
    0x1b0a0f030e15041a1804060608070f030506061c090507120201080a0219080a020c060f01060315061e020a06110a111903030903051909050a1d0a051308030c07030f 71
    0x503d810040301c4191111424403030030a4940c003060154800104071320400380103500810410006956070005403800c081140c078080414010b1110500f100d00a000349407180500070052440c0108000280300d0150800078480740a0359078117000d00000f1f100704540c001030000746210810101d01480014080304004108002c1940140214021484500c034dc4081c10001402c0400c200c0e50303401008030090151840c0113015100d44400e004410b003103100101c1c140c0350760740d0707080c40030f05111140024654820311811000480d007a195020a0402c00940240e551051040c0c0d140d000154464070152141a103074031540003000a40a106030fa00280c6008808244401510301c4107940000024541540b032406000e1588a00308001014803030001c07510400201c2082d280034800f106070080054004d030140502810110344045011455142c81101e0318041d2a2030810350340c0e4000700310014150290120740b01d8800811140c5c0011120000b851184501250242d120034440c00c008281001480d100030 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 900858174 1250 900856924 900856927
    0x21e100605150a08040302190b06010f1701030303021e031021050a020f0a03080c0a02030705040603020d02040e070f0e090c18060d0c0504060902120703111b0a0f030e15 74
    0x55042812010b40320030001504041c02e4907517440c2016403c00c5030b03072010310300c12043c40d4100504005c4100780e05030086c4401c0c3d83d2200c1090030140c0688548850300500203980c1d03038078001040068402c0d00186400f401100041d845541d240c01c4540d0140c00650307402d41c8000c08220284181c92034420384003050a0311300803c41c000061600ca0945640502c10302078090310b102c8540d8440303910341045840080d9441400195120304814101e03481d00c0140004038400c0c0900400040d841ca418000d01c419039400400074841070510b5401c110003400300c0503481c040e90003032a800080c0508a0303a0400c0051001d071030b031403c0c1072a180f03143d9810030740702c00c2685201c1c203c0300b43c4a8500c800000441c603031000042c0e07008000d00714181481c00d004685c66000f55449401c100010a40036080c0e002ba0181c504540e60008143d281eaa100350141c54100c20f0381d030f0b4107580610541040e20421400070541942840555034054515207e003410015900c5c416804908481c0060940e4100365000d04007004010b10f040303 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 900859424 1250 900858174 900858199
    0x628150504030c060807020a12021c02010203191a060316080108060705030f04060906111c020301080c01050a0905040f0518070522150602060f09030703050a0c03021e100605 76
    0x80010442c0f9004403070400c45010300151450b802008101c00d40350b00810b80d118006c2000d80029512120420780c030001c01c64445481d01298014002c3da0b0254121402d4256a00c3c0402410001401c2513201940ca40114640011458540b03070011400b41c0c00c10b0300340300c101360008540546444810f0344541080d5001800f0006015840303020350350030440c3c904191889071100e0402e60003070410308001600e014a01824100034490750801000c5a88520403200a0a50080181c0049010920a801150300201c4074a82158421401440364000c281401c4401941f0782010400b21080c0e40d0401060641d0780b000d0000650f05500e041d0b00f0344200d18014217540307081030003198001d51070340882d207520644a2801903c1482c1c40d0407840c001c01c080390f100203615543e404000d5803200251800709202c02d8080100340c04010100c2128029501516090701c1d1294188003200c408103000b50540450283c1e2001d0600c2000d20700415407004a02030042980681d00945042140c04c1d41d80a688101c040708904c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 900860674 1250 900859424 900859433
    0x213060e0303030f04022205090d03090203061f0902030c04031e02151602030a0506180d08060d060f09110a081605060d060503030c030a0207171005062815050403 71
    0x31240d01010390113628020f134440b840881ca01c900d20484605c1074025059a40300313010301e0b90344011b01c03030444041181c3c440b10b044072099080b50040b09010b501500480000b40d00300582000a14050031240302d50500c40b0b65030584a03040fa0010750703283c0d4400400007002c0040c4510740032503c865242c00d800450f04141c09900240c0c06444040a1304099000407826065940f8450451a0754a80140130b0304e880808500c0d20b02d41300c00303080b19507442c0705011120100043c0c1e800260f5600e036a40343d440c0d00d0440d449000400200241100c07003261060349410a5282128280c041c0d031843c0c5100d09000c0c2c1c110380f0148108045204160480d031000c2d0310014024011701680c0640204540c010749090340d540c80c14040d150080c0042c0d400051b05440b00003142140c0200001c000d10500e07443e6805d441039240c81c2c22000e01e200440c1200303400ea55001d55240982c88039541d02640c2c0100005003811510016030f2000080c1a01015140b52200c4984c042001001044880801802d41030300d0028581420360340d5 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 900861924 1250 900860674 900860677
    0x6060112060608180c1305100f0305071406042102100302090307090902030a02210c041e0c03060e100e060904170c10060e0a1805060612150108010213060e0303 70
    0x13551201c9076000300c440c0c4141400f4408a418004040c2038040030040100c018400780c0003c2c1c03098030b4520b80f104800920a040101c0c41c2d000d0303e92200180500510300303014040f03203551940745603510039010040020543c0c101e03c1e4001600d451811240800666401080400c4e5078880f29001810b004000320503c594002c01c00c04181c0e014014001041d2286001003481c00d22000002500080c0c5401b55404176070300c1b64956090b480c8840121101d00244c1c5060109403007035071103100c81d02420b45a500c04040805d4010a0f0603000c14600040d45950703a07c2035400510064403059280d0282d0f2000b400f802004280056008005440d00659800c0c243da48004114985a070310500d01070124900b0b038220018407041030440c100003401d00400340c46a48030784001c5000e540d40018149042410310080c01010718100d10703907030000064155641c43e04107101c00011501401803107800b40301691001c590500303501c2406000304000050b111000500f035204460a15040306042c0280c0401c81d0b065581c0020 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 900863174 1250 900861924 900861931
    0x421b030603050c19170303061c020609091905070509033c0f0a20100e0411040e040605090d022a010915080411012c0613060206060112060608 62
    0x7980403e04520283d10010040360359000105e000c10390042e06100c141c0000041c0d07010b4881101c0240d4682c030000812802d100786e0000080d0011010310550b001840d0001c4502e6024680000f0031072075158861403441102c03c01c0303514a010450200321a115420304011400700c0f00c030b02c0f40d030410784020380d00b0045980002c58591501030004100301c4c0424048140000c61362095071000f140d842030341510b401081240c02c030704a0b6402d40c0849941600515040a600003201d10640314500501191001c0c0009055100a031074040c0d441008000b0301072495a15080c402d41c01034030002546e04052030291b040c03c1000349407074110751141c901c014089015102e016143e401c0d02900d281e42030b0411005079042c0c1034a5110751103240069a0103200c40360040783c01e91180707101e0010030800340480e80042d84e414680c02070502166103207070028441040200d00c0c40107031030401484103003030034005250f4610b801130700d4000b040142c2000301808804e58006221409801c00842d0611469007003200080c022350006 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 900864424 1250 900863174 900863179
    0x9060e06101413020a020a0b090f160e1906050315160302120a02030703140412020715090e0910050108030a020f0c1c11130204050f0d421b030603050c 66
    0x19414800d039000308002090568008c45018092038070750b2200c2d444079804e0840b08003c4c006c803020154043d050701105410307244030000c518405c1c0c4580580c50301c80c120f9540900d16807940c0300004680356034100140c0011000c00d83d00020b19160081241c041c1c851081500d00c141401130000c118034201305d60035107510102d51040140c0b66600c84200b06c02a14403140d1128803402d1a80c10b200030704c0358076051403c0759401602181d00882d0364a081191014002545200058100000340010a40a602c0c1d940000c11081140c05d50184200014100c2e10280d10069460340f0026401d018a501801555201d04c54400500100042d0350301144070710b150011074408801070b13072241c04200542c903030540004030400740c89180010009801c8400030361007805601c0c815041d00302d00e1400e5141000c0456989540401644203004806000d44412408040c00b0081054000c0307401740381c0058080450400500408007007086416803501100c000e0420028408040c10120f0034000700310006901c42103507009 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 900865674 1250 900864424 900864427
    0x7030201081312051b2107050309030d1e09030c052101051816030f030503091e01060306050a0b09011701181101020d17130609060e0610141302 63
    0x1100c10010740c42c201e00000802c24016000c0c61040c00e603210015108131303000e100302e00c00020156101c0310756403107503070200d921268420321121400450b400d0182c030001d40304900f120b007850b007502c000030700f48401102c203a00042e104006a00304803402ca425505c1003412400c0145d50f890031500c900769480c0346801454014075030381100c113062262400c809090301d0b0840e8003c1105041c0401408402080024440428440e80c66510740e1048401c0d0302c0c3e41221346c05008402404070300c0c3d505580a41004200100320300500100680d0504000f420070f50f801c4c0b80000008a841c190b1070500e04641c4003510050032280340040118850b1500300e4454107503a109940d036040300d18100c003010302501484800c0500702ca074500703014041041290300248094001d03000c0d50b00e50240c031542140d4252120001c154802110f8000c1004003441071040c41d40c0b14011036020803040c1031601c4500030754481101469680d8845000c100fa00314500301800b001d003030013003e9520884102c40010302e403000d4251106103c07560 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 900866924 1250 900865674 900865681
    0x3070605013f06021b07050102150f1005060d0f06060509030c0108270c03061b07060b300105010614070b1801090308040318050114030628080705060703020703020108 73
    0x11003480c0070b00680d07220741c0035541c0c1c0907400c4400380c0d1011030900000c0144500b50300403c00b0b60010400e580f0492807144100d50711b9580d406451a850000ba0111420144482d030102d820b441d100014001c50040712000700786810965212000c5070419071100c010000203000717010300b030382d000b00c0c5000800e074003440c04006c152074800c500000161220343c82d81c41a2100c40e0075800002000c02ca0b40c20818045040d526079940c0c0c42c517000b5a0040700340c1143d540d2101009a400040c040c6d50007500705240140c41a840d00130508041c0d0751142a1110801d1a01018400b108160400740240c90140419180411484c0b000a044809078010114010071400180740007070036640c490640c611500760180003d1281c0811420090b16410044e03074241c0014603a401c2410311240900850000c9030010ba551680214000340c0b540155003010380002d40c016440041611540302c1420249800d118184804511030302c4c000d19146042801e50107a80125400c0c05101c1c04213070082808000c076502801d00c41001d54 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 900868174 1250 900866924 900867029
    0x9031305040b010f0809071517130c031b03050a230a020907050d1b0c021804081c0212040501240810025409160c020307080307060501 59
    0x161260010342c008600211640c0c002c42d0b100d0540c0750881640394911b509c036124440300300411404000e0181c41d51056044c1080011681a4201540700300721503c07900040d1281d450701d0a100800a0540d1030303a480710348444a01c520700d602c918140448400501c0c907114217501140300c0c070000a02020a120b004690460560201e400005221120303980c1c4048421074840050b0080314940400d03401000c3c0c251014020348003106409001d0768200f2007203810144607105c0d60310700400103080303200310076000d000048001000c4038a16000324480d20002c1030382082c0d8075079100307850800b02000040c503081d04000c120a11020680c00b0420176882000760b0303940640311140c403011110040e9011040701d202c0e800c50f0901c010f0750190540c0c5000001e98020005031000e4a48444682c0d24501d40c032141030400b0a0911011074851a550040c5042018540c1031540003e070504501c0e031700099554200107004801c0204e24458140541882003410000710300c98490002d0f10182d42e450803d4115181e010304003941c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 900869424 1250 900868174 900868183
    0xb031b01030b121501050303130e041e0c0504050912070b06010504080d03020405010806150904150801140405010c11060408030a02070c0602030a030e0304060c0611040e09031305040b010f0809 84
    0x40003030801a04050b900c00f405554140f43d58000751104824000071076503240100403504981c10386c184110020b8184454444100c5016004580044120034100c141006420848101a000d6003000610314540300910013a80d00084c0b00014a4108151024098034160181e4000503000038103006540d5a107001620507205942151109101310b1083d0000345034940c0040081e0742c02a03075103c01a803030380400c1c0306113902030241004d0000b00a001091480c01d290380120321441c812070f020001181d03103204260031161441100860743c1000c0e420841448000d0241520400380351620000b40500c42082d0360710741c51702510040090900102140468900d0b4060750713285074010301801c00320340d81da0a0181d520341c00707500c0d4500424140303c4560815074021051b0b034120354403511a112090056a281c2c1d004084625101403200001c0c0070124501c2c208c00280c510810742000155a1450090300300300c403140c125030103184100c1c18400f0b43e12269a0050480030301071500d040c03403c030170b0300c0e4402c8013030030f1 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 900870674 1250 900869424 900869441
    0x1120303270f0c0801180c0b040b0a210c030606021605060412030201020706020a08011419120203010603060204090b120d0f0509031c090f0e060609010507050f07060c12030b031b0103 80
    0x941c20301c551001c00c00d0a44000c4101b043c0b041801b00c0895a03500c0380801e85002e640300f15811408103100744070b40c16003e000c8800d10072070303d4840c80d10200300030701d5600b003147c2081a0b0003001941c0c5010034801103404220703003d11100c030141c078448070b240b4000000e80148101e005050b20400200041c40405000b501540d508541c40203056407251406030008040c40c4003482101660140440a00c4172820121502d482e40c07040714285503240740c02c03d84030041c0e241c8510700898241d0350742c10700000030440c0352020380013130100000e001c540fa450071000c01c600e881c61000344038205c0c2c01c01039201c9025604003c02101070895401d0042e100d4104e640040e00708030000440002c2200880103010b0b03900e5110030010701756821900282c910b1600c41407402056882255084c6d0002420000d0704410340c050000340662500c120215102a240441c085040110590103071000c07030741000c690000c00c00041402502c80155250403c80174050f4000240ea5101a030350780341da040c0c0400740403205d5034441d401c239000 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 900871924 1250 900870674 900870689
    0x40e07030609060506010e300703081308011d150402060d0228020a030804080706110406030b01020c220f0f0227010207060f120b0901120303270f0c 65
    0x440d4001d081403006090121a0640007d440d8089501b89252100d00c070201604401c00420000f100c0068800e1742c441035070341407281c40c4680400040061400e400510003094001d60b200c2c1707440d00e4100c01c0341c20344208074000044101e400050101030540010080198601c051103824240c0b03c50000c0f802c17601c40c0e408102000740c0000b41140d002d6800300e440d60340764961600003410100c10380501300c0c0c94030120341c4003c0010300700e5408640402e00340c10283c15141d025610000769101c849803031828540c4564040c401081d05e178045440c0d55078050161200c58002a11403000e0b08107849400c2c039404040341c014030300595943d490f10307500702620350040910904030942107643d1504669640007140c00100d440c01810a01ca00004181d4804600c19080300e82d16203d403c400c03108028103444185070705030142041580c417680c2084655802400500030900220455207030f41150600509039600d9102c0498070340e0081da462000404512420a1301941203011019070306c800d40b8201040b01140d5000e0031 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 900873174 1250 900871924 900871931
    0x20607050a090f091406120a0b090312040b041704150c1b2306430c05031c0f0e28080d0306030302063402100c030911040e070306 57
    0x1400044d183e202c8580074080401d00821540d403c81000810155081c8043c0e2a80102c0000780004001445071900840d0640c242c03401c1012005900c03000ca03c08640603100074420405200034407021041c00e2010030184500c0a00e00750412510285100e0036030707100810400d40c9085030090002c0c1c9428052036030f40d40754080c00030741c2c4da0b8001c00c4440080c441030f990080764035810310300c1c241c50030100704c0720001c40d0b019100c5074804000762031181a081c03d112070302100040c50310010740483c8140304209903904c1501c4100c02e070740c2041e05251510b4044480102d0711714801e042c18a10b01c0d04501114000c0e0410301d02460f6a05a000115501c22401c100303110b40e004500f410444201c412103580400c0e42c0e48101290761503c0007a100702d003920342d41e100c0500544c01001c04034040c0c0344070400002c0d100c406241503542c0d551a15015003444c008002065005801c00d1060b00302600981c0a4410803503003e00e0148680c3c0311641b5001c1c3c040707040065041c4039941d113190840709500c081c003202000759007143c000c0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 900874424 1250 900873174 900873179
    0x4062001050103051f06030f020f1512040b060d0f082d1b070b03010603050a0b12010f05151c05160f0306060e0f04060f0219110c06070201020607050a090f 68
    0x41d076103095000090062078184108428030001c1783c40390508407500800030340807000742da4007030002010b1804099508902d0900031185a103c8000040001182d070215000e068a00344c24021400000508110f200c3c0032940c071404040307405a504950384981041c07240360b840c00b00d0407004410250b031100350722028006290074014100310324080d00c650f80303840510f10041d898841c42180c44900a001d0362603901c00920051000c90b100b5400f5035406080f401c00040d20620200000c0e8164046000c212103981d143d5070644a070750b805002e480d412030400b1398500542d001d0034000031076842e01031443c054101480550341051041c10084690b5820f2001c4500382502e40316509225881d8060105071901400d00c0d500003015130040c141c051260804213140d81581c0c42e80c1d03076000040c04507008c07a07088298086c02141c51081036007000b55003183c041d441c0c1c0070602c140008924201070150040603c00d60703041c4200d001603600070a4a613030140071450065640c224000c0c06680c11401030f04006103580381c5c1c0c18003 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 900875674 1250 900874424 900874433
    0x1407020d0303112a06010504021201060e0612040602180a06050403020607050a1a010306060b1606020703020a080f120f010b070b090a0c062007081b040b041401051203030c04062001050103 82
    0xc513004100702030240c078410f070307207030001e0005a20505c0155844042c401004101d454440e00703102d9005000208450b203428045a80354903901001d60382078501b00e0f4009407154443c3c3c0440380074107007808240c2c2d4104456140000c050814002c5120190142c0000030f00c040070428280700c07002d64564000e0317400d00070312800d241b054100300d42400b0440740c4901d04400454840c035040e083e82c04c0010408403030118104141e0f9800080c4d00311000c1202940709010010000403a520007410f5207104402c2d0003522800c18100c0901c00c500e0280840c10a040542e0041c00184122011240e42c250071130721400701e984032080390a140060b5101c018106030110030010921550042940d4800c14003801c19985d040107050748241c4842c0c403403103080c542d6404050303840c04595151024030030182d0002c100254030001200441c0c01d036448129046a00701284005200a10f00406c030f50041101c0e82000b5421032130443e094042902c55802240184180e043c40c580c87e40500104202002040800a0095503036a240 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 900876924 1250 900875674 900875737
    0x905030d03060515090a0b09181f0506030903070f140105041b0608070c12050903100605041b050909060418150b010f0c0b10030c080a031407020d030311 67
    0xf61481041d8440004403822225400c2c3c0b00105001808511700b68600b82861000e0b41c000c007031054110b90740c000008000140d060102d4810040702054100382c49010300368201d808065001981304600c1070003441000d000c0082500c078115881000b81441030303080d007404154010300c1c0d18050103a43c201410001000b4402d5001c21040400c0e080400b2900e4640000350741100049a039040001d60381c0c14860040782d0390b48150007005005080103807411100901090031300340c43d00002c0080300d85415040080382454400c1400c2d007485a013041c444410380f040c0080c024031649102078400d001c0c0303401154096480d41d11024090b03c403811041c0d402c40b01d0303182410a105074203d088240c035150840c2000d05500030f841e03102030803140da900d0101340b100d25075407861500405800306c250914007a4011001890a08000000d00130050013040c0b001e02c02d1600030141e41d281c2c2c5560380781c02c105000020060b12036501007008940d050070003284c17990340d4420000f124010410364034801203111290880c40c07010081c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 900878174 1250 900876924 900876929
    0x3030306060311030103080d0504060608070e0402030d0503011505090f090a05160819020d20040e06032b210606030b09040f021509030601090b090610050d0b010905030d0306 76
    0x8500f4010260070036201c003c140402d1001401181d0204140e01036108564461b652151040000184954840c0c02e02c518060040e003011140d01480401d02095247c00c0124804c4200c041c0341061566040c0640c0f010144101403500c000d10101082c0a903441c0d0700d403d154105000044c100004074582240d00c4400f516043d10211140c1040b1080d80060901c0340340054441c180c0010220b002601d0707440d020000303503c100e285442c11341d5640c180910401d21010107608c0c18899041040c3c031241801c1c600c00400d24080c0a541c842da03c00b4101000300700551607141e0000041c0004012070f091170040c155a0889405400f8008051012024004d001542d000f04182e503000c1c0d8080040080e088148001030720180c401901410f00e40000100500e84150380d4020600920003450038001c903500130a141050030b810a800d180c0d190340364210380b82000c1001e1135010a049800c42202d400d0700e00d024149100d031071743c16603443c0d07280c100020943c0d000f00c60440042c8805011a44601d00c68600240200080d0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 900879424 1250 900878174 900878177
    0x10110706140702060c250b040c0f080c0925020f16030f06020f0706090309091431050304080312130c0b03072a020108090312011e0e010303030606 64
    0x464824074104004030240308040c1900140000c3d211803607201106e801200d10b806640310b00000039504101041c41340c451043c07003078030071305410700f0245000c0e02c00c6031003500f11030b503403161200007040401800142c0c0c00303c848041d2030304040b03526040f60000541168106440003110310001341006030390300160741078103409244281c44202c4c0f04c041d2101c02c050154807010f8008052031004d4008500280d0061000c56007603081d0a1800f02c039a61140c0a490b00e945040e004581960070800c0750b444140501002c25846545a120a240c20380158004c400f60103200c001403101c083c4038440050160942c2001e1580050440744c485d5558800a552503020020840c240750013040401d074682112001044007640c00800088041c2c201540b82c0025000207184604203d02002c10000c1c29a412a11011004500c1004a0804001e00026001220103440b42c41c01c0c0d0f000300702c5c506610000180042c19140e00400c0b40301501c0034085403d40c44c460503007054100382c040310b000200305034140d8083d41c101d4186 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 900880674 1250 900879424 900879431
    0x240f03020d1e111e09040b03100504060c0f082a0d02030103060c050901092706241d010e0f04050115020c190303201902090c040f03031110110706 64
    0x30303200c02c2c1840c1e0007481407510310a44c03d401045a60344020010700308540c80034000080401d81c6500081c80c0901d1104000b040581c0d500611050000314042e001d410380d40c50402c90008240f03d440246003000c01080000d1407507004e01344982c604814849041b000b04035240c01a1101c01c0101c2500c0254428401160038078546503e00c040c0c0f900400030b940c0004416183e41020500d0800054404401001480780383d80702d8070ba4000e1064040d11901010b0000c20203110b200242c00141c07a480044030704404014800c520103900a403e40c0800b4a0030a040c003880e1401c0101000400b0030040300c0000300c1164010b050600121340d45860b86883d400179a00d580c201c81030500c0c01c10038840c400050361035502c20f20141110510100c0d0082550523020001031201c120401d00c50040c0c281810300041c880400140d164281d001585040401290051034000d034041ca13240c03400e00071040c0d10100e848004e05102203060160036100c000d00040f0b25042c0704800901c240386d807101c0074480d00e80c024002141e1107841c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 900881924 1250 900880674 900880691
    0x20a111e03031f12080d0c03111902031603020d08180a08030702101401050103060b03011202010c050a060c03050714030f010905130f060213240f03020d1e 68
    0x314031200c03030056041030245103503884580c2c640310110001c202140088050342da0000d85048a1029003010500a00403181c40c4c60401c84c2d5601a58445a044410503090010000145c07801e10100c84000400da81407504007007094030301383d0035801180c01420030040301c0250081815004a0010500c60b15542c0d802c01569074040007104510980200041541c803000008001170b4600700110b80281d120300441e80340f107107030070041c3d020b0711601d510421f90324880700010410340d41c150081c032001d0900b01001354215030414040c0c1f07256242800b8045d0400a8240d00001442428401c000700190050030a200302c045208016029050070f8a140d00010291480c0f201450091400d80e40034801c1800100f107140d18010041019160150160071741010b048920400241c0810441050a00c5450b0140c0c882140c45050720200120741d0000d100415000d01404050300307140400ca01181c158200707108031a807600000c9000b1302070101640320041c500102c05080e041488012090f4601511013402000c8 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 900883174 1250 900881924 900881953
    0xb0c1920060322030c021c03030b0f060d0f0207150504030818062701061409060d0302120f0f0307120b0a1a21011e0605180f03070504020a11 62
    0x200c212241c108a000c800c40080151041102d1502404e0180c0f8180c244a40c1a030000380c00704003004101554100c0b6034510790b042607094040c5401001045070100801c94611000c119248940700c100c078111650f80c000d03413480045550607245a15003144040343c08c0c240740c0d00460010441520f050380801e10b00e40001d000315a40800d290500310040c400340c03e15890b0282c00d401d604031140644042d08540321401f01a4110911402001307041003003014060700009410322086500182c980d50040d074402e002c100110707800048002901c40820380869580d003e102c04900d041c000d00e85a400791420000c10700c8216030b4010320064030980140020481802c080b02080309104803441400181404001078244260300040540540c014001400203405844400c1e004d018900740c12884100701c0340c500c80b8007980c800c0702504c40605410b00704141303005032540e2103030140315103081114411200000708045d5610300307200d0000208805030096444403804407000d0848018940e5495192045038940a03044 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 900884424 1250 900883174 900883177
    0x509040519150e280207060e121b0304060818010605031005040218041220030304060603050607110705120c0a0306020d0b0a121103030c0d090f08010203060a0b0c192006 74
    0x503c20f41006001000488000034041c0d044181e042c1c424541e641d54202508c402441690200349004030803d80d90502d660303207200c005042c0316041b80154018041030003007a03001084150482450f247c6070800245242c5101d0260040d41c20054160081d00c444e0030040f2000d80040380540d100b155600c2c03030044008181c1008400856003d0030405400940070007035401810900808548080c100d140c000d03042401c40d02d0b6500549045600b180d5916080040c00800d00000c1e801002610780312034444280d90321103644800ca409441d20500d61201464080941003003981c2c4000c2010340403240351a501e04050000b500030320740e40c580b254107100283c855854560147c1702910300d03201403a02c00c04450f1f1210307080c0382020072555800d07100802c0b21500d1010104000300980f9200c0e82d9030f06925041900c10150000c0c1d550010540e0b82c018010702c803041e0360304c0031004180c403140303040640c41e560b800c81e4043c50304d0528042101740d003012440780002d10200c100041114a80030b02ca0000c40b64481c030074055039 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 900885674 1250 900884424 900884461
    0x170402062805040e240f13020c060402010201180807060b010c02030109030f0e0d020a0e1305060c0304030212160b070909060f03170309070303030b04140106021c0f0509040519150e 79
    0xb85c80c44d0450200b14504030a00e00000e40020b0840c403042001019801d04a0340070145810242d840482040115a42405110054072203880b0b520540145940e500c02c980c014080002c0c10700361150090070043e4480e4a02c00701894008009200a01403400c02800b0500c0581201e00081c00d0031200303003800e0a0107002a40d640d64003030241e424651902c0c481000185001d0603c4d501a005000701a0120b1b070108440c50180b1883c168a40e035074200b40c9406440d0400c2d800f5904640d01e001c1c000d101640c1b5070100f50f102401d07082583c01d4083e41c2c0ea001d0884218219400207803030f25103045404560031403d02040b20549128050582c440d82d220341c0c5504240c08101c4000c007041e405180240000782c03185c2c1140c42031342c4003c1d1020a41400405802941407000d07040500140c0c002484110710700d0528121043e4a080350518a07140844550001c0480c0b01300360010740566161004100c1075007064034200c15411600d00200326100208011103c08212442025440814400400c410040f800d040200 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 900886924 1250 900885674 900885721
    0x20c0105100b0a0e0303130e01080c1903020d03023c070f230a031a0604090803011703070b0702060708090705031009022805040606170402062805040e 66
    0x1c0c90f41c1d02c081255400011960150580000d0080e0000319003100c0910f8007400c581d9003101d6140d8100f10a86142c40b4040101c10b2090402811304210005201020025030f40c050307400d014121024103042e13240c000344040c610510407920500720b0104456150540060014803d8030701d482e08402c40b401d548840c68014030900c04c42501c000c00100145007491280a41d503503114144c40340c84140080d003c0d00032a4429151405110401c860428060300c0a81c2c5c802c0007103804020090b0503481e00e04560005020b070040c13002c07800110701d44000303003002541c00c8240d2107850007845203415180251160802e50f21040400c40301400304400300400b0071620107491000e07006042249039013103a130f0b0203400b0300e003000d0381c003c5441c00054001d080c00c4101990300c88865008000c1c0145000180002c0b1100c9a00c0b02c0c0c1040800e00d00701c000084101c500030740142c0c049403203030703100c0c2c081b4404285052090112a80755084080880b020f003034010020384111107070780100d420640c5d1010308500300f07051940748221 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 900888174 1250 900886924 900886927
    0x507034505041b18090e03090405010605120f13020604030c03110a0e0c0708041503090510090209010e0411030d0305040209100303050d0903050f0a03090b0c07020d0f060f02030a020c0105100b 84
    0x140e0082c0316030030302c03110301040310100d141d459682c0601c502151408581c03001b094000203000302040c1010b01070640100703c0351034050319013504464005000d04002c0c0207100c0c0040088040340800b0a0003030043d01068004280729030b695942d1a140d05142094402292203094412610000789800b08002c42101d60303101d40c04201e965500413502e0994014441110f00c0c84040c8808100e2140240001d0007842158400044d210054140a85800c4848141e1001d8034100a03100c401a116441c131141140e500c40454841c5803914079010f100c0308804a4819054810144c10071901c1e03030b0542087e40501d00a989079600b5884008150000f00788602000c1c0105801300031000c00340642d5480500d1440c081e00e485410407210314642c3c0304c1e96002c81c20b00c0c800613445950402c1032041313045145401070b001c5045545002c0b82d550116082c95400940030300708818600940043c00f4403078004040003800600215520300c4c040c01154025000b944501c4115864034001403240c14081d060082a50007090015 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 900889424 1250 900888174 900888221
    0xb1b04060804050d05070c090b041b020d08010905070215040203013803030301030c030b04021906050a110d0f0c05070b040f080609061b0915030421080403050703450504 74
    0xe4041c1088289d00e036005580c5070000519103900f11107400c565149a80503201244403200000c1100e2810b80001301400d207400288101c0076000290020b080031701c42c41d5843c072940c9074000240140301c054940d800754504101603007403061145c10301c8041e041d105200310981c5603a082c1030503524002408020304480c0341f150700744085a0309410265015100400c0d001c1080c80c24a02100e4018065001d20b0119401042c1c0d5271656412020403280b402e080c0c001003807900440034000317080312034400300042409088450301c010b00c031040c8034460240c800c20500964965440e210714080381d55920031400540210004101042404124580100444088104408010303984035445500c0034009580c06039090220340f181000941c007031407141c0e0080303d0001803080e1090242c06083e0340841c0d044200303c20003003000002500030050f00e484e10340601d4085004d501039241081034021100405003204180f210108101d165074155818244c45c1281c030861090b5244244001c2c3c2d11107106d042d10582224400 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 900890674 1250 900889424 900889439
    0x6090303051b0f1e031305010809030c07140f04140109020309031b0622050303010320122104050a05190308030403090305070614070b1b04060804050d05070c 69
    0x50111082e41d8807061400021040b103031440c0c0001d044100100b500200280c8295220444a1005221041020b1403030720101ea0306020703131401e03640078641c1401950350205002a4040096404c0c40310600c04a5100d1f90b250305480ea04010406c1c485403264000b1910319099042c5406090300d280c205c03102c1c58101d81d0800d40c50a010f17410003090540548001d015031030305800788002040c9514841c0020303091a040140424005c240c13003e0828403040c1500081b000061000803c490459400022010b9440781421602c501090000c41050384005509409d00844202041d503890060013a1039405c01542c1c01001d28285014034491140e02068000701080749080c02c441003811920050200709000d900c2e5911101640c10070348040d000200010818800c0043c00c010002c090000b030700708015401c800c01500d40941c8600d020042c000c01400003c0b902d08010030b00c0da2002001020605a01c403078075050000c3c079010b02102c00350381c603109820b05251840d008a04441899800200c0b00a03010f0a1064 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 900891924 1250 900890674 900890677
    0xb3103260a0516020303210417040602060118090b2e0b041a16210203030c0316170702011a0402071a0408091905041407050901030b0303040e0f1006090609030305 71
    0x30598040c002041030544422910b0311000c4031061111f100e03015400c01c0d003089456141818868486003100300702c03e205080c0c0014200b81155047c0354010742c3d0051440e6810081c1a03006d02c002d20b00400c10382030202442c0e4070700c1411030602003040d0305c01703105240440c0c04404480328801c903540000708020502c06c000c404000c99060700c1090b1005454040307100303040104041e255009035141d81d084014007038101c034010407403001141a84021402d40c201030601d0701c40352002405040f20030540810031174805000c0d81c0c079500f0303007981051042c80030720b820312020303010f800c010f0700010b118a2040500001480c0a1099404076500500d01d01c2c006070300d1040d107a00301d01025006683c01c1000b07204815040c3d6500d400c80101c1c038a9000b081254604d42403d2105a1700c0200c2c0b59a000407202c0200680e1681c400262048954240b8010855900782c0c1c022a040d0b110351f4001d0b0385190512010000a5261101d02c0f038003542c3c5501c503881e5295518041111303080c1d418028040003030680036080002c07034850300 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 900893174 1250 900891924 900891967
    0x801051f0309051905070b19030e0c030109050c2b0221031809061c1b350609151914010501080a02040b3103260a05 51
    0x81c00074281407541c07034180c40c02848045a080000e88141c0000400031305010a070000c00d050f42115040c89038040f840002182a01c00140405666004211a0480400c00006160005402008010200d040040e2a1a02114010b005070050f1008441d44990141035000c100d410b000304d0043d50480b6400c114465010000e0200d894070402c070710b5000316100344000d001781c020b014442d5640800440511070101c1008289500c030313a203184c255a002000a90780f40c403485900248424840c00c181c1007040c000a1130f034022000c00404000c0b550b81c0100c158008243c1c1511041e03200c500f051005030095580c5c1002c6940741d0047e04840d80b03181c00040c0d806410b0350015003580000000d81e41c090642803c5400f058000e40105000c040108120750f004098640c01c20303608401035140034100314001d0102d101e0105000796840a05540810b04644034002414a4410005000c1002e03070b070341421002040c0703500e0445401840702e000703041030441917070880714429015144c003030030180904114542c580c040c0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 900894424 1250 900893174 900893177
    0x1020c040f0b03150f160f142505070515120405011b020607030b0301050108030403082d2502090a0b0a0905010f0608010f08060f0c0f0f0a0f0801051f 66
    0xc4007032900b1a6818050200191003101c614a141d1802c480c2581240c1e5014080d040d002d402c042c001c0341920360003400c140180d01541800c510034449111a09190321480c610388a0940034960071001164007104c1440c0c01a0040d011186440d4403441005000d400036244c1d040c500004100d520040a840410035911900400000a00740d4003100381c451250b0405081d074005070808001c0020307440c0c00d4421400f1814041d002040603604018030305949101742d00003d410b04602190b5401180981d01e070760007961100c2c0c035246ea00240080c0d2880c000d40c03c00244c0d02021401400040314442d140250710084a40080107540d40d85c0345c00b0a4803000304112900c294018103009000b0178101c042d40a024002d050103080b148002c1d1800e2001490401d040e0490481da03401c42004002c42c030305c0042c0b41500301000c0800014552a986c2c0fa0400b103219000281d00c90f01c1c004520704082d80388000c007401411805498108010324054401c441440090003101e07848000e083c0c612510070556601c2c22004004d9 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 900895674 1250 900894424 900894431
    0xa0e04020d0c180903080f0108060a0906020c10091e021311270103150e010b090a03050708030901080a1b03050606130906061704080f0d0902180117070501020c040f 72
    0x100c188111103500281c3c072860007141c460340c03081c04044c2e10101c0e02d0340c4001541c00c0036100e5410000000d407120005003071ba8101c19200d005205c188203175541101c41e80403800e03080315002844101410301401300e00b1016107440b068420130040172084643e54044d00d0b54000c102403072034100e401c849030040184403070044102009201c5c0c2c14540c0340341c030144000c00c07148002d0043d82c42040320004040d1a0007090b10f60710002210300c200209001e136100c00d4155049440b40d19250007107017010504200c100d50000e00644100900028503200110042c44c02000c01ea03196005036403850442000d4030007030024442e104a02a0302525401d2007584000d410241c000c0c07415180c580822007107200fa41c16a00704141040d600c1904000168010300348071554000480720541d6880c041d00e6002d01400307016640604154009902013401c045a4442034cd5250b0003092003180c201042040c4184210900501404105039802c5c0340c210311001601c44100c0e54164010112443c0c1d403c180310207409400d0183c001240c4 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 900896924 1250 900895674 900895679
    0x406022512031d1e0d0317190c140d050a020f1b0d020c03031209070302040f0f050a060f051309120804060b0109030b010605160624050a0e04020d0c 65
    0x150041c5080340d24000c0c1d03914444080c1016a00c0014800c410380d941c400c00c40030701c01203840003c0d6580c2e02d0080d4070854605144031020b050039148a80904104807030001ca4208101c5078104d05588505101d24240d020403501301419026504910704203400c551170603041c4200048105640c010701c1d409a06800050b00340b44208401c80b03180e8101e1182d0014401d01001c0810200a04000f403101c100b01501c02460410314040100c2d031a4800c510364603601001110000e401e0000411441e0300850340600b04104d5054610f24100c000c106c100484511181001c02182c5d0700c03040f07030080c407040c0c9452880d000d88542c503000800c40101030305030380a058140c64545420101e000c0d950301c25911151511004542c5c1740910340901103411109132340c0d040c00134040081c800f18000007605815982035007001c541d10b52040711120850354a1190041603241080d5102e901c00c000c0c1540c55502c2c6608400c0480c1da580c0f590b0400c185074095020769100b400c95100041e000d031800031081054980141000d072091174 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 900898174 1250 900896924 900896939
    0x507021204060c0303110f1b010605060711010f0f1d040f0e160902030f0402010e0d0c030c080d03050405060a0b061308070e0903030613050c12040b07110304060225 72
    0x1042a401100801d0150820742c0c04d043e014040c802a0801505095250001c5002900218080d00d910071010b0611820102040c2d00250302c00c4000d410001c004544403141131803c2d180c003496030846280081c01c0300815030b8134113010b8507221031500050780761144030703040084040010410f48004107901c141c0b50600c41c20804c07011303ca00801810740b00090a82d014503d0040d0300d42d540164440b142c114410410402500314191405400a80c2460f040340d0b411084000111440c100b031030060035070380c000800002088186600441121a48002e41e10300620400054044410846010309140c000b41c000810344241030b070142c1c4803020010f040b82d0502c00704e51400926240c40f0340241c40503038040e00342403106201c0b030a150f60b88520300b18020362840c50141c0215020100004190401e1074849000c11090214101960365040341040d00b21114681810700f120680700075034040b404131f0030488071302ea0fa000010080300d06480b4223400511041840015561851848481d19040c0420400e40801e550 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 900899280 1106 900898174 900898177
    0x7020c06130b0309070e010b131a13080303090c040b0607030305070e0607030203040306050709030515040314041e09020c071404020f04080f0c0f011205070212 70
    0x1054008000780000065402501d114200402080001003001440e90101d8000441801040c1d0380d520705107082d8840c4280701e810b043d40303081d803c2c045409000da5140303d464504180c6864104007950359650b00040e0f400c219080c1e08000248010040100201d1054000c100c40400c210440710000891034803c0e900010140368882002405590094500584508000c2c00d66070f075450a900e4001c1d1a0b82c040c0c0800c070758043c07400c804141e885104660100580380d200c070013041c0c1424403500f03804241400810880802c42c104840c0d0750a4418000034100a02804042180450300344200d41008940e50700000d030035a10500c1441c89641002400008858407080031919851142c0e02080203071082a00c05c183e03403140050002842c28000660380c5034000440cbc1907030190043e500c00c0001c000e10f5040310500040390300c03200404902031544100d40111017130048418103075044900760b206 = true := by decide +kernel

theorem cover : BRFrame.Cov 900719424 900899280 := by
  have h0 := BRFrame.cov_init 900719424
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900719424 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900719424 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900719424 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900719424 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900719424 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900719424 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900719424 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900719424 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900719424 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900719424 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900719424 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900719424 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900719424 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900719424 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900719424 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900719424 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900719424 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900719424 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900719424 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900719424 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900719424 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900719424 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900719424 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900719424 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900719424 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900719424 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900719424 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900719424 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900719424 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900719424 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900719424 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900719424 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900719424 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900719424 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900719424 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900719424 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900719424 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900719424 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900719424 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900719424 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900719424 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900719424 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900719424 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900719424 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900719424 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900719424 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900719424 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900719424 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900719424 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900719424 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900719424 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900719424 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900719424 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900719424 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900719424 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900719424 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900719424 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900719424 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900719424 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900719424 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900719424 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900719424 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900719424 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900719424 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900719424 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900719424 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900719424 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900719424 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900719424 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900719424 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900719424 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900719424 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900719424 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900719424 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900719424 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900719424 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900719424 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900719424 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900719424 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900719424 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900719424 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900719424 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900719424 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900719424 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900719424 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900719424 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900719424 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900719424 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900719424 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900719424 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900719424 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900719424 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900719424 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900719424 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900719424 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900719424 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900719424 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900719424 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900719424 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900719424 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900719424 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900719424 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900719424 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900719424 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900719424 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900719424 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900719424 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900719424 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900719424 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900719424 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900719424 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900719424 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900719424 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900719424 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900719424 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900719424 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900719424 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900719424 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900719424 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900719424 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900719424 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900719424 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900719424 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900719424 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900719424 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900719424 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900719424 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900719424 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900719424 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900719424 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900719424 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900719424 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900719424 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900719424 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900719424 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900719424 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900719424 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900719424 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900719424 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900719424 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900719424 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900719424 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900719424 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900719424 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 900719424 ≤ n) (h2 : n < 900899280) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
