-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1849
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:53:57.958634+00:00
-- url     : https://prove2.me/submissions/1ec18ae2-aceb-4951-a5f0-9623a1438a89

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 332374100 ≤ n < 332553956 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 332375350 1250 332374100 332374109
    0x10503060a03060b04022503080604020301180506030f1c0905010c0c0e06010903060e07090e1605130b0418050d1404060f0c1208040b010806040506060925110705040501 74
    0x1c024841400052416446044408005040182441c040d600c103005c0541c100030b04079103c408444250010950f004c540c01d540068181e07020341c00c5501d8001c50b41c603c01c0c07000008883d25521440000e0700c50702d040000e40c2883c8010011035126002c1c032088100e403000703c1c84540002650000303022a5a50081c1400b00c545035000e0f2407440228940689500145405000b9504014070050300201059141c0519040706210402418065203001c407240c003102d00700304102034603800c00b0070020307211048243c10008944054070381d1880484a00e0303015005082c1c5240c865841071501e0a151480083c40b008030050611071022600170341e41c50308087c3e6440a07041c0543e1100c1008000c140305c014403075110094010200d060a40b10950a50b40d220900b494800c40580050b1625080109100020181c070340148040000303800d0f80c3c00c081d2103c80d16500010000c82c003400801d00810b10980814860014450105824032294100020010400103480286103172504c00c0e01c00c0880c0034079040c4160f038100d5 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 332376600 1250 332375350 332375359
    0x615140301051507050d02070f0906031a061309060203010303081f0302010f0507081b0c09011a030c040b03090f061608182a0306010f06050912010f230601050306 71
    0x41e0b107024200b104181c402040d44450081c140300090014000b006a1400031141707401800c08030f41001e25816945026600c1010340c241801400c00c08905164851000c2100082c14039902d07903140b20115043c1d442e490038140690303103021000020b00c0b04d0f0368007550503240300382d54000150301c43c00d4072803074114004c900c15a104c08415504000540c001d00c0d00300360014260800c40e08000e010340ba034441a400100461503410408600d401d03004605000008060104032007030703401941050f42c08625400320061440b1008000404a0200460007003038900422101da4001c0d035034946050007a4403882c1050090140303108040200d91131000e05100d202c041d24031a610440c00b59903208031030480301c06110100c8820701880e4140000d0a00c1c0001c070724070703a12042c034188004d4030410003030519000c0142d000781f008440742c0a041c0070780e95215003150b40c5540304560101031585489031940c010030202d070804903403924110502d0010300c03aa6091a020701c84602c00c1010542c0c42c2c80054551340300c203d0380550320 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 332377850 1250 332376600 332376607
    0x1a0402060a031a0423160504150905040c020c090c0a020a1506050d050d0f021f0c030b03100b1c081902070e01030b0a051006140a0203120a061514 64
    0x1224070a40c8066050030b001d0a0000d41c02c00f459000c10100d6115501c0c20600c2c8000308802401800fa4030746079074005158107608850420405002880e501035405210740508045850084c000d124000c41d001030a40104108a081c1c1c5909000e9600c604d4603c0e40e034043c10008001890701035208065500b180d400d500906400c8040b55215140220340207480b10b005aa0350001080a0310340004410006110724000d20400306070f08400b51030000c100000c2403c40d4130801c0d040d01340740d40004501001d08c03011a1702044602c807260701980645406607085030584a9010075000103801a00440c1e0001d00c01d0359403c08407485075451080d40c032080d00c2c024082c80002c2149039403080001e28001c1c1d0f404103903c1a224550b03112008220740000c01c0c0c1c020f0329055902402d1000825540c46182d8020304142c03440030314146425005000107080c00c0e5051854000032034081030f45da0080c001c0391400c85600041415074a4150b28100003801d80d40a800e9203c1001010008002e024a001c001c88044001d015410f = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 332379100 1250 332377850 332377867
    0x71e061b1502070812040c081b0a0501050a031d06011a031003030c0507081002030403030f0e0c040e07080601030c09051608060f06090d0606061103040e013f1a040206 73
    0x2e0b40c09600c04591100c0200500e0101a468010305806103216028165100e890b00244a283c0300d501144001310a184450100403581c8444899044030000c1c200b0b00c2c2c8035840d00c00180c0050102869010701c0022055840140c2d00010074504e068070904031900011b14510405032503580422151070222662480f0700340013290040600e590b08503c5502110921500d860119040010b00c1d4880e001c0c0c1500401070104164150041c0724202c4913290041240300401303880950744840c1642d106001c0d50303640382c4444c101482448075034080d115000c1100c5440d40d4074a400743c0d0008091058039080c92500c4007041041340100400c4030800742c1c81c1c0e00c007030150301c8041c100411020070b201c506500c08010007049880d9121401c400c1032180c0200400108240380890141205540c2c03024203889400c2040305028800307c4607071039415a468288290392200c07030300380030a003d030a00e06410340d111100300d25815000e442e098001895188509100c9142d00302c2c01c00d0440e540c98041d14001e40c800720600903810b = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 332380350 1250 332379100 332379143
    0x905090702010e28050a0b04020f100c020103111b0a060609110334051207110312040f020a27051b0706110408071a16020111071e061b 59
    0x44c20100402c2c0d040c04c8180580e0702c3c00e1401e810014201d501c0b4030158108000c0d4540039007240208030003078450707940c084000d610003030a02d28980740080c141075445c8102010001c29500740c6507568135078500e054048807a030342100c2c0da52a008401f1905e503800d1080100d007a03070041c0a244929400d00c1480350840c1c44000424500c030401090340308000011507070002c4054411414044840c0c041e80764140e4424622183e55074100c001000d000034403c070150000300c1100f001044404a100c9042405195161840e1102c00201c8085001e90311402818000c2000c1e47c08605400c40340b00100030525044c100110000c0603070f0b20490f103d00410039032400c500c00499264009200309032250740d0024041c14941000304080d00150040c04040d4005582413050440c81504031a150703403403000c6141020749000451a9000c09001c0003030400c12090b121000e10002000000094405a01c0040782d5294131048007030341654500c2004001842c2022270681910b5000b004405a600280d421040804416280 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 332381600 1250 332380350 332380393
    0x4080f07030b01170f0706080403021b090106050702040e0312060310090f0303020f1c0c0906050f03061903061803030b01050702090f130507030b1f0806010e0a0b100905090702010e 79
    0x1c2d98001c4500f60484d4005c140071840c081d1080d91104013503400c00d400c000f8944107190204039032100c0c16515040f01541c410b00c0340c078112075031403501c00c0d5141040e202240c05044000c1082d0a148808285c0c00c0c10043c005100500c607134001d40886504881c0810601d0a894140d10b0103003030008008103040209101307030014002c131030803040140d181070f456204a0074041c0c0144e6100a6180c2d03a180e20081d007943c0045040000e04040c58064203001041c0b894602d1480050012031040702c41387d05606421200380f013000001e54110300300304400c0301c030025101400820280c04500191800403426a03540c002e10075a00e0064010300510307020b5440800707095440c1000b403e85a0341c0c47c0c1e584180c20000c0d808002000185124461100690502c02042014905502040364212101c00001d010b005000110f881c111140c00d0b54568003074640c01c0401d401081ca80083d40e4026141c2c420414106400c0345a0300304480c0f090700c8807100c43e41c540c0812400c039010f003425824687c0000c0203ca42d006000141d6 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 332382850 1250 332381600 332381639
    0x70201140c0619110408030405060903010605180a11070302100c200a0512040605070f0c05060403050115080102190e0604080618160b03040818090c04080f07030b01 72
    0x2124030781a8404101c502d4464110780302d24861501102034010200e00707010300c281c444140c104140c00e107030910003e81c1c1c170b038015402007d0140101040c980c00c20b9909400038401820044c0c010140e401c40b0a0342101d08040880b00303800300f50b0512000000580350001101d4217560181e015142810742ca08042c00608014540282004049080c009e003e01c01520001c200700600700003050b484956141c058103083c12140c0f07201810300d0602c030400415812000700c500c11607008807507288040052402100c860070701c0c1c100d260020000705000c02000415070007042900707070100340c1c0c0da0455038860751b150907072095203000426402c3c1d0340000c1c01c600d401124918201000103114034100340c1c0b1145032a1510100726600543e480d040414071f007031540d040c0800560044042c150042d020300741700304040c1912000e0030051040e0740c00518107130080d0701c0e149120030000c00200360041c1e43c100703404181c4c1d268006001e211107500030400040c41c120400944101280c1d8441300d144440c1c1e103015140825103004085 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 332384100 1250 332382850 332382887
    0x6060a052119021903020904080a021203132618010e10020105040b0c030103030c030813170309010f06050f040507050706060807140102061e1506131a0f070201 70
    0x140c00340400030900581c00c4442e100424400107040a0040108000109910708148603545a080c40542c4410280171383c0242c00c40b507441c2d03640e00284000c030318020041c00030400d5031001005200030354061152024645000d40060b00381c04141341079845a51000003081700c0810b17400c00c4403950844100a09040402c01410034040c047c00c4000460001c40b0350606100050750354800b0013041201400c0d503150001e4565003150f080d90f06590740a080030b04609405000d10800e01c0003e0340010400b040b0164031030348203414000072000203074a2640c6070400c1e11586200d50a0010495050495104080440d00c000340b0b00d071000701034081400020100a44080f0402004008010101344603003d0800100f01c00001000002d00e0b2460400400c0c0c0c00c515603a04541082d014400000c8500c0f002980e039804158203103440303807070322408096202800061a80c0001c0c01242c1803036514408442d000c200d07003007040d240e08107110b9210741101c030744901756100f0004041808a000954400c45000100c80003050 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 332385350 1250 332384100 332384149
    0x11010c0804170906120108010e0a0812060d0f051501080f0705040902010306030f081201140f01030b03070f091506050705120d09080706021803010b0a1221090f0806060a05 75
    0x102141d12948034030080303817401481c0310040186181c240b00d110501031076200502480c1d43c4541c4d17158500d20400000007044107148001c1000365840072130000605a01004c642802c204919049031600452035590020005504c0006412003000c15100d90003403034407001e81010750030a800c0100800000000f82c1c10103503564000300004002801e490b108a0041e504141c8034604001d014070400d805810508004101500b104075075200c16081800d142c03024207000c02c040c0c1c000c00209180c40702c1940895003203842c15800240041d9580e000070120030320241e8100a040d1a40070950b91480b454070300a003aa030011030020a12a400000303440d1300c0914100c00f10321101b45032113003003007900011020380d40184e000408901064440c240722038007040503030007401048112000a0044449403250140c20084200b0103000c10900003040c4c8005844030b8170104a841400000034940c00d81c1c3d00640c181c03d000d032400410714180000b07a40c0d201d00030007800360102c0307810031003803008581416130381c48200307034614 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 332386600 1250 332385350 332385367
    0x11090a09030e2b171c0f02130306050a091b030501060b030103031e02010f09030f0e0109050a0501200106060305010806010f0b040603090503130e06010e0a080c0609011b08090111010c080417 83
    0x44008061130740c440026440c100e00c0703150f604002c0f80d13020300c191b0320b04600c100940c80c7c54480b854605402c99401c00000921944c3d04540349001d441081d0b03000300301c0140810400780898030b90010b0000d41c0d0050380200030042e20342283c1a11880203020103000308000e00c0c84400c2d445030040811201500354800410031007403d14600c000e40e201010124081000c503020202d919500c03100d400580102482d0040c441450038001c00c1d1000310500895041242e815008800011000d0408440f00c200f14006c010b01d59407180000d00a1400303005421060042c18000100c185444004905a8035004c69042c07074903140800135030051010002c02c6940340003d0026550f43c0540581c81401007080c0308440440d860038034001090550220092403180704400414001da00000031210100c5000380c500540daa400b0074010703034003c9000d200000900e803600d9014070800010b2809450034000c00c2c2c076a4400c84400400311800c1e964a44100360015490f480010003180f60904210b4420484c6c1c0c05507072620885 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 332387850 1250 332386600 332386643
    0x105030c0f0d12021f090201122301180506010206070e01081008030c0105010504050619031101090b0c0f0105070314131403160c05010e0d0f11090a09030e2b 69
    0x11145140240e000400080e444664103035156207984071700101042440069800a84810880c1d104007100e290703202e50090b4080c4903100186520065000484025a99002da180e04a80168988200c450810700820520b500001e8894091480d07500c0c1c1c2528480300d40011110424001d100b0003108120030b0340003569090034401045040314040000c1015070605c01444243c42c0b01500880c0218014104140c8908152003442e040c2d0382e208003900150802c500048809070001d400c070a42030390000582e120b06403000102003012100141c000c1c40156554941541141c440c8680c036900c0400c040b0004036414605100030309110710072010b02c4c4811484003415451500282d200d0841401042c1000c800c0c843c160514500419003481c11a0300072414402040c3c01d5905c03600014030f001c14010341601004807810449120003c0500903c50031314150745507402411149a095000ca8248541d81403103080480184c0f038440c010320301c00610807450107032909613514002010781700f4600d40799071070100091 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 332389100 1250 332387850 332387873
    0x10b070201023c120a050f090a15020d1d040b040e030c1e01110a12090b040303060e16020303070e010e1e180115110f06070302130e0105030c0f0d 64
    0x11607040260640d440a0030780d80407001402c4081d02d60340c0c00039007144e0203038a240c03040707403c9000309241094035042e8018446900e401604070482d07020606a401007990035041c048844103250945c2221050120b0410964103030480f42c0182c02c920091103000c0e074403400c058000c054440d202810004034590700118550650f001030840f50b00d550003100c809041800399001668000003240300070032140c0c9180c204415544a284041c2050005000d2161081240c40c1c1c440031403a900b104072005140b405180080041895020f035801504050000c55680c8808030743c1c001c02008280c0055146890341d050a07184101a12005410451200c0034510180c031022880d07006006540c9030140341d01e444400304480d00c01c03406418245002e120b00108520303000b540400c2c80014a84c1002240700c4140c200f21030522540144100d6540704180c184240c2075030542c01400341c504050312001255480d8403500000803400e01c03440b94540c0c0091403508251034038040c40452104014500120700c10107580d000140341 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 332390350 1250 332389100 332389153
    0x209030a060914071e0e07110d1e05090109060e0607051002030411030307120e01112505030a0203120c0f06040807150902060706050406020903031b07060215010b07020102 75
    0x2400c0c0c88404001c2c00c00100b0041c0810010700c90b00204a079210314140800c600c510800350140d103021501076070088d00841440703074070034087d034001101d90300300645404031083c42035003400810301900825504c114169160a11f059680e0002240b8111040711540019005140d0000f020040800015810444d005051910460140e01da1600d030500c40c8841c540b110006d0b0194104200c0c40c0c0000c0d0450341c12130034010860502007904100000129080d0146604501c12032043c005074041d8940580c50124058004984919200e521407080c0344c0c43d8000001c00a4042e440702c080c0e05030b681005c2e0301401011544004841e43d006c580303442103240400c00e86055401060028602050007100b8102c04a500d0403a0400d00641820b035010070a03034812580090446603441c4082001c01c100e40c1c04a9004000040440741c0f00c802d50b80f04184005041c1c4500012071207400d4000400f1400841e007101a92552508180d041e07180c546808a5544901070032030450060804000c14580b51410745038809 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 332391600 1250 332390350 332390363
    0xd0e0d0f0c111504090e0105010b0408120f190c1205130605030a09020604150e22050a330e132003060106051908010b030a0b0d02090c0703120b0604030201030209030a0609 75
    0x41b190340801821284d06801c400071b506410407051000d40000241d203200402c1d02030702141d488007440c91a40090081000034820410600002c20109500c060b10403880e80c010141781144503c00070050300e0f148038405244180896810301041010300a034080c6901845014000c00e0784241903001900e25031144d00403e8440c0340b400041d9800ca580300b034440d0405601510007221f4540d42c1082c821b0304c41000381a501140c0c3d02c2c5c00004210104a07042135001e086103411900044d0948041c0007500c0509244181d203248007010000360f12321144860900800d0024082605001c2507214100005d061030406203c021461715910240d803010050039000b000503989541c1c9a481e11140000e9044580d6091000c100300b4100600c06031029404513500249d1403070000400c148004003088418030071708000b0f948241c1e244200000701c418400101405032003544c95507841d840000c1c441d0211610b50130000d40002051200740015402a40200300b0b0000060071601204910f50b20802a180000301c00c031944e = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 332392850 1250 332391600 332391611
    0x19050f01050705010606210c080402060a12060602030406170103120810030b151c02101b141b010c0c03020607140303250306031104050c0903030d0e0d0f0c11150409 72
    0x814080114261007e1003240c0902480c1c02c1c903c4000c0c90b528001d8000b030311030400018190112405400c01013811102030030144201660307114040e4681c0c100b0b00c1600c02043e10242e02180d44d00c0070421040c180c82e44413540852800011104440d002e40041c6a01c0841c2c145c40d102101198500355413600c1180300480c001400c4076070305e040c40008925111707034500011410700313000d00507a07175460786c518540b0040c83c142039000c0c0f00c01d85001340381001010140c9421500c1d16100580c59000c03418080805141500c4003070124102d004481002010201038400554000c040c00140b91102c018442036000c1c030200c0203188038040a0a0640e0b00941d60403045514400c1c0e4810301004100c800848214a0b0070100031052031510b031380d120744224200480c49503541e41c2c001900c0303005207000e8988031040a0304403621010f0242c07005c002000d8241c5900360610580b003418028900c0b40b40c134010030f6074250340d82c0800c1c0c0f81036680e40600a2202d4852662055003200c3c041c00c0c503001040680020038904101150 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 332394100 1250 332392850 332392877
    0x5040e1903020a0827120606010c0201030b0402070c141210090507030b0702060415110919150809010e0a0816170a030609051003030915020a06090602041419050f01050705010606 78
    0xd01119a1758500481aa00311094149070102d4202d50001d02070030112820b044a20040f002400304c5030b0401da001e0b1002c2554014800c803000014140da003000c182c10300c2410401c0420603480b00340000d240f0746920140e003680f881400c0b41c0048075010711510131500c1d515101c2d5512a244207084811b0030060b40458100702c248100d000340c00c0e03225041c9001c04c100c00700440f907050009103c0c3c08103c9009040e103c03200b111000032105024000c281440d0001c2c0101443e00d00107003a80410b9032904d98640c04c014108002e03060100302045c40342e03400007a861824601421070743d800e42c4460002d0390800b004481e070607845400341c4002c106078040c50340e000800301d080030b030000215030018205d80f540e0003aa80703041c030009820150503020b949440c9445000c2d5144503200f2031914000c01d4008140b0350030102c031582002420780142054801000150070000c844d1400d103c1c02c2082020401844c00701120204070720304212034010b04803070043c0b4041c0d240000c26101c65007511056882800007a22401c11460f = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 332395350 1250 332394100 332394157
    0x5030609070f1e090806090d0f0207050306060d080d050703230105060d0905120a05090a090203280b030102070809040c090e1b040915090605040e1903020a08 69
    0x580c0301c0345a00781120701c012800da00501c1591880540c801c4041c151406240d01401003001d038009140340400c07145a450300445d45900c1c1c2c1110780041c40864250b200781a00c883c00418080283c94000d2b0092000341e6441c070405c0100325400c2c00a60b103640040040070107180143c0145840351a0355100442c4035440504081c08891070144844401613030700c401800155150401c40d12125039408010510080e20f051207810061a100f000c007003c030000400452080e08079000c4c00400d84100c0301c1c7c5012680d1801a0000c0c0d02c4100c3c0e044880701c54136081071b1358070840c6013554186c2d285400c1c80011841a0f04020034221782c400d05050f41c250202107201d040c1450070b80105d0f80b684800e0314180c0003072032030414601c00950000d00312180d5501141074040500ca000001d80700200700c030b00070a1100d20300c0925580c04248060003060442810b204000c5854100f0b030180425029981005000b690340751540c940c04414140400c40440c003402c1c03444008106104050000740030000c41c00c2c20001c900c0c0d079424 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 332396600 1250 332395350 332395369
    0x207051605091b03040f110307120302010522020d210905040c032304060b0d030309030f0e06311502070510080601080403020c090c040515041217070c06050306 70
    0xb0f100719101104440f0b506415141501d8206901c036000614100103841d10503a0844d1401c1c100f6014443c46100144d1541024550f02100707010341c008000300c2e200c4843d08511510710034551410300d004940403d00605102800c0700074a4014080c0c00c07800d860b0703a09100d01217201c240501c40082c0504205010030f00d020700c2144096580d9003000c01c001e82090009501103107a41c071031010502e14100014041c042d40d0703082283c40c12401803a0044800321071a018004098441050300014041500f407218140110307000c01c1780341c1005001d02d0900c076001050705181c980c8103100081d00c984596070042c8000840000002801981c2d0b4001c40111108030000d20b0085194401031180045520980c0c08940001e842500030030286841c40c1d03641da803030400340c3c54441003401e0260001100000c0080c0d14041c00090701c199032084a1000f600140c40c0160822405580070384500c40a02007032043c00030348404c0308001e100318030b507014070305001c90342d22078a07100d040c80d0f030000780414000400c100181c5011481c0b03 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 332397850 1250 332396600 332396611
    0x60f0c030e0c0108180a0f0b04050c12030405060c0106150c050d0302090a0306050a09050a03030b01020f0a0503040b0903070f0308040302010801060c0c2d140306010602060403170406020705160509 86
    0x2041c00349000b100080076901d001e0703c140d010f888040d050105581c0b042c420b602096800c01a00d16101c141e80c81c0441c15468200d405032038500450301351080a1a02c01d90320316031002ca000080d41460306040820640398803c80030010159a12800000d00b003802c40c00340c9224401c652070300c46455603075050050a00c840503441004141c410000505c940c6d4a6400c1001901d80003800054070740e03103400d400001011010400f9005200307004105e01056030540108035801d03c01c0c0c1c00e035160b00f40c110442e01c0e525003045100030f000b90000d000034454074403680c1c050000301c20b00a04960b10b59079201c1c41244500c01540082d5028880040d0502c15940c0200745240144458078201160100c1c64540800c0c210407802039a0645041c0c6141300c0c40c40e48003a40c11040c2a041c49001910140d40d01e8010007032180b8045d00718028010300000044907800407906501c80c90b01925401c07c1d0340b03a540f41820a21308010406c5690940c00c2c007038000422400c221000c00019080604a541410903040258140d030007080c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 332399100 1250 332397850 332397853
    0x50906041703010e041104020d090606152a110d080d110319050709170601080c04090503120705041d0708060a0b0702150403170d05100302090c090d060f0c030e 70
    0x1004005441340065900580000b52240702545482c0043c0103807188030b00503d205420700c04840140005030380000102e035a03031036400d1b5106051030300075a580507040c0d0000b40309942c043c10341d0307500070501904803c035607224904a800f400b20010014840048202046d58000408910224813100c14400c0c689255000808a0306614100c03030240d031004060f5031120910798441e004100f4903030041001c500a0a003c882000c2c1c480000a145a42e408007441f80300030500c00d1955540740c80c20140b060a903d2500000079601e41905407005801c054400740a210030400e041000152000e5010405003a600841804130090300f0800701c009d01e81880900b10324448c041d091010048040c0c0c6804542640380d06545400c0b610541c960400a280120b5101a00f480445030b04140104601001080b0600140004201a03120100352017100ca016000c0290003400c1900403800513038820010b003200000c018801c180d5a28a9a41c060a0b9454074200b081c55545800c0c04206d019054041c80015154080 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 332400350 1250 332399100 332399107
    0x100b0901030b01030212010f1112010509011a030c0c0307080406030e1203161214011503050606180607060615091a0f0a020708070b03100e100b0307050705010509060417 74
    0xc46441c110304040c40024406c030000c0c40102d040c80e50a400564100d1030f9158200400c038170a140e5030580da03100002020740205004000700301440c060328414180d40d49168250703041100040c10b00d4190348080d0a028400c0c03030a00910319021030400007044050310801c04a500c1c0c40c6041c02c0a81950101aa9489144c010301ca0565080c203150040c0c03544654503206031524003441c01c10655002981ca020403001070f04008100c4004e0640403281c074101c03681c88181d60140c01700021300302d0441d281500c00c43c1c7c1c4948200080c144003204001a041e0440c40281010715007a11503490740201e4000341e000f0290328401240701005942c02440485c01081481003c050031703201000012518403c402d0b80c200e0001d408540c62160900c01c02225002d421054106d0740f2a07500c074140d55030160070481d406100542e214038003190010100d4182c9004502141014800c01d040810072046ca42000300fa110800005001007008103c4c00d015581c041d49012000d4409030900e820543c8030b035000c424458a1030341041 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 332401600 1250 332400350 332400353
    0x405060306070c02190519030515070906030c050d4b0504080408070311030c0609100e01031e1a04020306010819060f24020c03070308030a1103040302100b090103 71
    0x1210340f000f0382d04541c000320015a0342030701261076095400860b08012051080d0210000c002041400d89001d14103d03001c81202c800324081c061000c441d000002094032104000c92030094000304241061400c003941030520024964007260320607488070f074040c2029035400d03039450340c10040c4002007100c1c07209800d600508001d250f00391001e20f00e08040c80540d1a4001014040c0d2081600c024120907019240540d5481c1020308505000481a034803c3c040c480301d414051070003108840704c00c100036100a150080300142a102c148520111505064803014136880121000d02d2014103070400b440d002038124403600b8000400d00d02c00182c0c1e40958410000e06c50260f03040b0960340d0b0f00142e20003401d000481c2c0b200142000c0c0400e50322481c01d41c1d650a401045064013040c951040a100141850000301c0d058022170380c0e50700008109816401000e002e2010800c25002545e00c106d440340003099217140d0000c641d070300d540304840640060b040045000f900f82c0c0c1d103005140460f04201c904050a5055 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 332402850 1250 332401600 332401607
    0x70206061c02060408060708041a07091e05130e010614030a02060a120c0c030f2a02010309050f011e05010810020d090c03080306010f030219030902030a0804090b040506030607 77
    0x480606003403507002100303028110740e501411900503003040d405580090a2034103002c0c2203070b001618100c5402d54424009040f00c0c5001c03140030320858256a40850b00e138a0904031040d501200300800f0544504e600d0003140503146d640400e203110b01c0c0d850000880300a1030561600311041a0010742000304c4425191600b0380d0300044100110760112001d43e038442c2c0c0000103a6409003103031010307800701d402c0c0b0224108040e0011007151905000352a1170500c001715850071107030504030000596003180c5403801003441c0002e0440050b40d40f0300c107041c0010200031a07281c01d407410014251502e1241e45070116003e15041d88514910b44000b008024031155040c44025611041100f003000d500d1580031618105444464000403401c0e0b411190a900b000d489081c840b215030f00481ea094040f0705031020f0748041030310a10803a511207881292251000100060403000340010443c20303641031080381a00c0c400704811a0003040140215000055190309050034801581d000070040c52080d00201c0400c60113680 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 332404100 1250 332402850 332402869
    0xc08040b0309070e0f010306060501080f370c03150e0705030c0712020606040c0c0507030f0503070b071116140411040b0a03050402120d090b1e0a031407020606 70
    0x2200d105140c996941600c6a403401040341c0c41100501c0c81d10050041101403500307028140c80c040c840c14803440342c6440066910b2082642c8480500180740005011800100c03c8642203000c0c40c2d0b25050052440201003240200d0040864841507884044000841d05407040700d0301800000d00081000d03140200307000c42c8401c02404c0e00240540040000c4000503036108031820a03a102d50b00d004500040342c8001c1d9109411642c083c002d905c1c00702140069805880610003155000d4014185241155a8080c0320100d0540446041c48203009038000150700345c1035580f04e000c05035900b00701d01902599286c54035000701000101c000790b840090066546d90681e20403000c800365004600103201c1b400c10710f60b41c49030b5441b2071b04444011036400c205540c92f401050041d4021525a581003004542054580d4524071182010480901c0c2c100001209000581140c62640340748500c61444113020445a5100e4013410001a5a60403400f07040c420142c1042d4012965100400f154034158011070103c04 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 332405350 1250 332404100 332404109
    0x702060708041124071a1005060906120f0f0a0204030c05011b0b15121b0d050c090c070b090c030607110f03041e09020f07060903180618060c0804 64
    0x25449000c810f615203499071042c11105145040841048031800a19805d030401c081c2280c4000f0903031820030380300b014048070701e002c1e02c0000c401d46a402d103403000300322050380071100d0503402a8041c819141030a030507006052041d61310100c4c41d80d26241401041c020490010000c0c000c5c9d03031040c00144041800c882001040c1c0e2800c0c2000e09a803411701034480305000c4a54802001c1840f034104000c602d1006001e548500c1c8000d40f5504500700c0382c401c41c9610b84111010020303210f410300001d68841d2a2080d040800300e07009409132407029400201003050038004440c48414001c1c0000c1c07213000c018a0030100c40c0c1c40083c0da00540100711340340740040e4035104050300d110100007060209600c001c000303002c0c080c19000d080007103a40c0e8030740c1c54640501c01c11500725035032030081f190174000071025858001c5034620034841c140b00d4548062681c03520000d0070303450000e80c208400101109252500e00348020301426468480700ca02440240c0d040c24081019041081001903980e185000280e603181034a00340d4 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 332406600 1250 332405350 332405363
    0xf07060b01120911030d0c081207120c0e10050a020a02090612010f0b1f0806130f140610030b0303031317030c180904031b0309050301020c06010509070206070804 71
    0x1800000100d4036000d034880007000007032504141a040043d03601206513a000c0079021740e003070645041c0d41510680b00d00d810282c4043c5041200c0d00000c01c44049442d0300110f6410100c1c80d540f1400c5409080f950850404c0000c5001c0305c117011034600e4200100481c483c41850810b1600c02802c4009450300642540280510010f501042c1750b0303500c0311a0441044002c10080110480005007440505035900c1468020030302e68080c48025008032941d286e0b40c09842d10303800020385540c401c0c005428800c0e414011050b94a4001d00790b000854000c00400640e56611411a400c0100801010908000da56024140b0b0001c54440c41d03140801541d900409000200104800b5801c002104d40c0201340b0300c001080380001000724052a15004c1c0945080c01c070303c2a8000c41d0550140000c03041c2c1680c000c0c001c42c815412000040070140c030041d101600c68a083c1903802d603180040b9003640c019007203d900702d1304407200621583c01e01e040d03090b42c080c095200030601c07410606006031807018080c1028122 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 332407850 1250 332406600 332406611
    0x31409190302010f0f0510080d05180a09020a0c02090c041d040219080601031a06060403080d0605032a10050316110a0609060e0a02060904020c0109060204080109020a06050f0706 78
    0x80c90b000790301c540d400200c1903000340102d40d403240710900148022508071000d0307101c503600070501141c0081c6002451203940c80300c41c03078440c0c0d02203946110892100f1a640c442450600441ca0309000e0018254642594460158080320351040103544c400043c60b4640c4203009000c104001c800d0300560704941c007c210180340d0030743c50328000300301011186205100c0c11050400d000914420002d13038039040320b009209100e8220705002c00e0845003203003540c880d507000ca01448240086414040182000c0c21205800a00d407a55000442d048c01d00200140140020840904413007524015500000080403202c40d0b031f600c0c60000010b0098000540388410892811a034000154010400e0910703080ca03c0c800c482c4500c0c0f081c40c100380504200b1500b01e40b1a801e0000542c041500040c6c800c01c00c950040260b81000746e0802440001d4000c242d44d80c44079900c81c011100031030300394402030026142c05000458213451038014010411f81e0355005008004c001c12440300f5003000740003956a0180d21040101c5d2 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 332409100 1250 332407850 332407853
    0x3180d0f140706051302030d02010b03120a05070606090b0103230112080d020c031b0105060d021e0d0c050102070501210507030906021c06080f070b0d0221010603140919 74
    0x42500424000403c418542018002c010844107134401500d8401c07401c1710911078203a00103d00740c0e80544022a0194030030211040d07801c0c0b0a0024000f030b0101440c0640c20102d003521400c095515a501c2075603059511f250b40b00a65a00d80030340051000c40040c800c4518902e50010380b80715505100f10180c0072a07210380c0104000031641291f00d5003051a01c1036442d00b54000166403641d124210300b524820644900219003407041c0910344c880c5500511aa00004854081c003000511044100c92036000290001c1710a540741035400c1c1d0514060401594154203000001e440c040094202d18140018a2100c041000d14514401c081e00306c082c0c404121034417800740c15400740c10010300c000d1103c0d0012a80c40c24861003140900b140101ca80c0041c04038580c0c1e0400e061b196400d00c04c0f000744a8115010500c807052803a030090000395100480180780c00141c0b13030308000e0941425154041c140f65030004008141e4140540100101000e450407001e040c4014101c2c5d80300010702108241107809400f150 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 332410350 1250 332409100 332409137
    0x315050909070f0311040510050619050c0124060306050307090b0a0e0103060e01050105060307050d05090f030415080c130312121e180308370203180d0f 67
    0x10018401080300e442c0440d00d03468680030905e00e2507011030089143c00c0000e408008400315800c1101e101500e403c3c40c10030700890701940f64003a04003100030301c84100041c000d45242481441028400780d8500c031482c941045002400c40900d900c1780d010035052660a00141c1da010a454044441030400001c0581c0241c2c0411403541c4135503c040d02c4081e5010001040c00120b0300720f030007100c02a10003005240c0c0c13184104201c41c04103440303a200081060000441070b0095030f00c6907801c41c40d60303030407950841f0262903241d156a00c16009240340225170888140d0b0325401401064001920302107103420064940c14405402410b440090320100d054400951032901841c480409143c4641d02840343c402c09101c030b81d00b8100b070110100e03041c510345a50081880000c808105646605035144411a1518141c54540540000381030102510065003480180e00c0b0f8200d1b03401680841c0700c0941c03685002c9120000550f2020a41ca03a02e800c00a000b88040d0ba00104c4038070360020fa820080c1c1114a00c072100c1 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 332411600 1250 332410350 332410363
    0x1d191d070822080a030c021911060f04030f080705100902060f03070314070306062a0206030c0f0a0804060e210a02100207050703050c1207060e0f090f070e010315050909 74
    0x241203004000703540c030042c4c0c0e4150450b5072908100d80844001c42d000020501e42601002409081c6a84083c20407213280740010081150358003071090075041c9603c80e202c680000e5480c1c03d0440b00321000154032000c0080c18841c8c4540c00700549403c100250160f008100d030ba1250000d074041c080000000249401e009501c081020030000d442d081c46032404205c00350051005006074004641150840c001c0d0740c103402e5444040c008542007805010009600340900c6400107404500b80b4002480701000c0d0031410809081d040c10306c2d5441252a0400d4100101160744807030708106075411506100030b10802603488004140502ca011940d02c01d40715900b24144201070607918103050000866106004001a900017075a0041007650340c810194002c1000c40621800c10417400d41108004001071800717484140c84424010340040704070900c2c50005100301c21300b00c4646118a0f01c0006021450340d101598407076114080c01d08001048011076049020090f074421240300382074507030009d0840c07001481807 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 332412850 1250 332411600 332411603
    0x904060f06051207030e0f0d02010e030405010905042a0e090c072024070c060507020d1e060f0f0506011d040e030405120d021006030209071d191d070822 67
    0x56500c0300c09061520348c2c40780104091507005608100440004100100031201110416100c10360154500400c1c032018240c0003250031880e003143c071228100b464030029900d1440010740c1d42c0080d5043c0002c100b210f0b0a402800c44003403440240103007000078a2146880110380f000c80d48000241c1c19807400075401d00218400c0420701005500d610840d5501000038000740781c869008103442549554085949004854021b9880f547da1510301000c01c401d203060b045000140103680c0c0d1800c00c1d81d200e5100795001d0b64485241e241daa9095420b04402c64482c5a42103402460301c412039102ca40d001a4130580c1a2441c541702d160f940c00c2610030f5403010000c0704c00501002d0328500001c281e1203415a01c500d036000300303500913002c0c0e0b00610101d06043c1c070440007680d500805540c800d460b401e0003160391003804046010207281d0503400c484a03030b40784054280c00703040c90300031900d00c1420240c0c2c2e28000c004a06038424620710f128144a85290454020365110204242b118089500182c2c1807000e1403080c3c90 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 332414100 1250 332412850 332412853
    0x2040f0902092227050a240203150f010207050105031828030206010e070f0e060912030306040c0302071e03120614121b010f0c170904060f06051207030e 67
    0x2080700041c80307410013a0180c12001c050200c0c520b542c418034005a507210b00c000c0054100c8809400040c40043c00c28264541b10030b030b244800d1340d0f0301003540100da00644110044000382e1a142001786000320f51803009400138030240217a20301d001e002800c50b0001900d0603411071302c43c014400640c071007041500384020200460081700300d6080ca61350348402c01000160010b0068a0010401d0703044103144038003a9070540c0e140c00b40d299065800b103171450184915654040400c00074908181d8903218500c1d083d0003220060f60340d0f42040300c10002111351a090f00020702d0b00520442e008100200411507803040c071001003000c02460f07440c080300d0450f00e0032559401c851508001260021543c002d09000c44d0081c0e4640401c0043c030310390075030350b4149030311a040806109840304255501c40c2070b184808184a051104054005a40d074500302d9488001c510842000465126228601801500c004060780d0b2040141c45d4201a00104140304025108000b4504503000c618078a01c00d07405800564072000 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 332415350 1250 332414100 332414149
    0x1706040212010e0c061602030313031a010602030a0305060a080a0302060702010b040b031f0b27061c060b01020f07060201050603121c021c050408030f06100903030806040e0106060207030c080102040f090209 90
    0x80000590560ac0c1c04291820100820945001d05420144605845403a0000c41c00c3c8810f2140c104c0c05010001d081c560007001c050710016050004000400c0054440d40140c000c5207042030000342104c6066504502c80d81c1006214401c0391408200320513004070300f1025a03580210f6043c8900a0042002026084240045d18503512801c007110060400145042841b040c2c0b201b0040140c0d245210000030790f08560b1465800010b201c641c803142c3c041d681801a1501038a0050b440c505203880740d401900540d4482c0c0402c415883c05001280b00500000803c2d03051040303003045400c24039815541010b0890b8000398002d0180c91280308884403100c284400c0c800740c9040e140607803140d041580c0e82030310403841078041070041c03a00742d800314052130441e924401030b54519201161101030160400360815540c2c0c47d0901330003800c3c040c1c40040c0001e40c004004041c9146080b5280f48030960010f895a441400284005480740400404807143c0110150304c6044000000c0c0d00c00b910503200b01000401c0b603 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 332416600 1250 332415350 332415367
    0x6090501051312080c0c03010b010819090203030f0702180f0f07020313120b060a05060d0216050303041113020418091a0901061e03020607060e071706040212010e0c0616020303 77
    0x34000b402011643c80903030f102d400c6d51038103250a0b14600f20505002c50884400030b280c030299400030300308845040340080f4030710107a900401e05550103200320a01c0150001401419403c041854030380d10350364143d800020786490400d0815903000a0018150a50100042981c162003001528034502c0400c0b0f81226442c1d4a500100040d46841c20440d000030360000000d2070781c6401c08281c021590041e1001d0300e4407441d41501d000a5124009548003800024445800b05030200701840c401c0744105038171151014048100421241e0490603120ba140c0104400e20050703004d03440907203803081d10902c0030a21078141d00e03120502200b440001c2569040340e2080003618041504010202c51b07140d051401d4000030354260440381d085600010790861801c1003044000340c0d55900112910060406481c402030315450680c0b01100d103a544003a0b0750b030001301400117502e825107205440014880003080001103010525448404c0000c01600c110400304083c0c4620f5980300c040143c1c99402401d4903a1244070 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 332417850 1250 332416600 332416613
    0x307091d040606050303072303070f050102030a0509031305041a0405040501062607260336030c0d0204020d0e0102070c06110303010e0a0f0f0c031506090501051312 72
    0x440d820750340b8500b48034000409040c04000c0300c00064000d21101c100c0200c20041e2019013000100c5800700d44410032142000c50402640409240e00c0b4600150b528180700001e4000d480d000743c41c10400c8d8004108000d5904985c214640840e44192008205008112603102400c01c034204129005401d1504020400106611030750903a43c3c0c905400c2044984030719000003e0000c0c480c904890380c4400c1d014080f0f18440042d956142201000041d511100c808046056130096103c00e02e0015240020003440542c05844910301079009490001040c00c00002130b680d8458a000c02d801140d010112130299200c4d0f804990585401a405000f41f03140050b846000354010300c001d903404010340307d0116615129443c24908001590011030859080945540b060b401c080c001c7c1985542e00c3c45441184001c070300030101c0d603d01c81940018043c00d0114050103490a4820b94808130550900074011190090169020b5440078a0000d403114200152000000c89036000081003048c09884032040101 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 332419100 1250 332417850 332417909
    0xf060b040510080703060e010b0409050312010b120a0e25031401020c0705090a1415011803030f0e011215061403010501080112062c01060803180402030709 68
    0x4068038100030507590240300b0941e540460050000781e03000800208003080c0c1c59000410580d00e80c500000e60202e0714000942116005503040394603800100d420904140c1856a66005013403003076140d46040001c441e07445000c0700040c00400604e69501ca6500710000c204400041101510110f0903a2462010001385a030900e01c812100701101c0380d0001820b01060081c2c417140b42d80c110082c801241003000304045000b00910f40c01d007580d501c049440d44023020544007800741c04e14040c07070070b440300702c2d030000518a120a54002000c0c03032a913001000007a502c890100142d01c41c600d4a01c0551103132600484081c3c5000800c1c0540b41c0c11b0100b80010581c00c40c0c1048200c1b0303403d2b210b410320301103000b200404070b0109120b0700d0b0202c1d0424004100e03c4c0c42d464848203e0307c1c425103001940304030501c85104805070403040150084059064001400703800d1007450003400100c0b0045003815100d030003014a400d1201c101601580e008804507000901a2150001034039401405864940c2144c01000300d060 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 332420350 1250 332419100 332419121
    0xd05010f0e1501030201110a0602030411040507030b0f090a0e060c04051810050d030c05010c080411010201140426070803040209070c05250b0a0201061401080c070b060d0f06 76
    0x6141034508441d207140042c440d00c0c0c0101e46005884240e01e03540040d10300c041050b4048043d8081c0008101c0090700c184000c40c440c51051106071103500602052000b1220000c200b02c0134540f40c45c5580b0655522048003264585049544104543e44e9145a0000c0c3c517680801c0300c81441341100348400101c00300040c1094a00603580f0b00c40007821107000640701c3c001640d001a2103d5482c109201c0d80c104040078158440c028145844902410f5444c50b00b11038078500d0800c0050244028041000070700c80c0b81c01c0761040c0920080c02814485050800d02c114068002440034110086088070780c2100c40c40c03000d0408a0610b00b0b61660301d282848441c6900440b822445403210200003000d06000c1c40480c03684680100040000c44c010100d000b881145d00c5088041450a85000043d00813803280144540d1855130f0011a8041c900913004214003070040ea298180000c0354200071204404000340c80c140c44d0000d0b000700305030319100049022406903900c054600b800a40b038810901c04160441c08000 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 332421600 1250 332420350 332420381
    0x304031a010b03190b06040e04020a0527060d0b0405061b0315221104090e151b1204030503060906041b200d080907091505060c0a020d0501 61
    0x344a40c000c125148035090161825400c0284003003042886120320130a040304d000744c00061014080e800203401c0b50016840404a485014100001c5003080000e08000b4007080d5000c05000d45007520f0001480d1201c10a01808071403580007980d04e64034402007075030300c0f40c10a200c07500c0b60401e130403c0ba40b11401100d01c1c91403150303010102c05107140c0002c2202c2c861000b40740701e400e182c01c8983c2081030b405d000180c0020080c0d0104c003401c103505c14500c140603404021100340e40d44c991420224409562121100000940005c90100c45034402c10b84501c2d4406401c004141c41c03005001e10307014031401414102810a42410104000c00d5080340c01035006540031038001e481c46d0341300d508000946200c19004010541c1134282c0c030780c155020750742e00c8840e1240c203520800500c1241440030b25150403d0300a5000403905000e001d4002c40c144483c00c090400c07104103101405400040103e030b400240314960103258002090001090300348440c4501d15401051211115a1800c20754080d005261065002 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 332422850 1250 332421600 332421623
    0xf0e0a08010203090d020703030512060402091f030e010608060c09031e030403020109052d15180405011203050f130b0a03060f05030c010c062d020406030c0f1706120f030403 76
    0x217035000040d00030440740e148d80d9103450001c0b43c0c0c43c040e50709500600000d8205409010361070060391080c0c2c045c140f400140c001d80941c54031124000301038549660b480442d40e40750000c18440b007080800d50300d901c0010040c80e266030320b900c01d02007813602c6c000320b89004000c1e05a0000340e0300d01c18080000d00440e4000d80e9940015502c1e10700b0000e888140d85480c480402d090001090710360401403446204010007841c200e0b41c0414042c86d03442c0360348000c0c0c0e40110164014182c0040385014480c0501500c0441d1407500000c0459401400744e11910702210400302c4003146503041880224290005043c0320210b05849540346003001d400361050f4021450b481001d450046040c0c200010815158001691201c9036000c00d43c60f680e005002640f094600800d40041e40c40f6012410044170410440003000103980b1850414000c0485d414001280100501e001c2820441907102c40700c0720070340713044c000401e83c0c80e04c42c540001ca0b100146007900203940151400d015200d1b10200180c0b088038014500e0054 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 332424100 1250 332422850 332422873
    0x50c090109021804051012111306050907050309071502030903010e06060f0d020d020402120a06060903120513150c05070b041d0903040f03150e0a020901060f0e0a0801020309 76
    0x5a01805280700c05030310003c10501c0c000d00c0e180d0081c0e9084100c000c000f101c215180c942d44803821060f22010307504010b180c1c83c1581241400030309007080c40c44802041100d0380c2002c000030491300024040c042040ba0103c089005118284000401030001c1e8100c40c80740301110030065229009051818030952a0031075419800101281c40781c89041c0c01085c0303903440908401048038610311200280d800071b03e600100d0300180c07500e2000700942c8030b030710400c0b00403460440c21b402e00780c8049404c094100452200c0c00c000041c013502d400340305105182411500c583c007540e200342d885503490b40005541004040302c0500b0175080491910810f010b0350640e542c1035100c50340707824148180c0c440c03c0480801d10074800c060101c4601d526030018115415640b4207a50350361110741c0031031550015101e4001d207040011000c8414820300c0c8500c41c040e07000c0d01c81140d0b0b0340c0000b24001c90500c588400d00c07100105560900d8031603410042c1c404801130803900100e0300e500906000b17400450300e0000c0391040754080e10 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 332425350 1250 332424100 332424119
    0x1021602101815050f040f180207020607020405041b03060c0e18161e0201140703140a0209060405060309010b100908030d021b10092013090f050604050c0901 69
    0x28041005001c0318540d41c41c0035480702d200c01d1024801c030200311042c4182176420381300748001c0008120440f1007c2c46039082c071a000b1680c0c013290612040443c8100800001078035604280c0300301c02c1c0c04440001d0555582e080c4910009041040b460b015809414040300b080ba0b29031210401a15540e2040403000d0a401032080300c0001c030782d00d624030703045542c00185a08680d044d03000102045180103540f0703040d24040408210160701c1d400015035110502282c00c44003c80b54140d00c1101c40c5024844071407500911403149001401080e4142c0c0c0010702101c850700e03808201c400030f22000d0503540e84c03447c0060307401d8000c090304015a4896507520f05845492031007906440e003614000000740d480c0480680542c0d00940c03060a403808103005500414148181c14051108180c01030040070400c40d400d8501488238481d82124250f20a94008204030180c5440070820461011941d0000d01c2c1515414424111200100300501600c100c8003044208607010645601207807040e100819681d0700e808200 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 332426600 1250 332425350 332425367
    0x307120e1f021c0e010605031903020d03020a050d0c050f0703051201060201020309150a06052101060608090a06050c090a030f0512030705120411060310170109050a030518030102160210 81
    0x81c1039052511801c41101c0074aa00c1302d00c0c82c0c1c00f2000005030440e5141d022a060000702d0381d042200e00509a424401e01d034042c086080400e1451808610304030141c0005031a50107203400b800604c9603286c0b20700c1c1c083d9004804989003211120310054540a680c907004180d548040900405ca4008000000d103890050090ba4042c05408014286003170642510055503a0000d040f168030603214500081c0703540300c0101c04100318205201e1990a80e40900110b403d507440c69209004100c4070800700000d00e0300202d0320100c070540c04000480d131916011030803031290080007121a409000840c001040002284100044a1080c8255406a081d0101d0f20201d40000c80703040d00894001c104181c4180a8a41c440341d002d80700d090440e0841030600c0c0462020b40040700c1c001c45090743c0c1c0070103000e051221188800c48002841c001c1c400d14101e55100d50b1180c0801c18000d05001001c25282c01000b03002990340e11001000d0300864a2b0781d14035070708244200c001001030740240c0e5000300c02d484030761241104 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 332427850 1250 332426600 332426617
    0x80d0c0215040c0b1602042922110906030705040e01080303010e060f03150705131205030409150b0a02010902040b011d060a03020d02040f03050c0a0305060703020307120e1f02 77
    0x8940c811882d00885801304da006442c01125000d5800303840c401640c07584142d81ca92032010600d20243c0700000e00d42c0ea21121411000c510595896601c032244021290300100c3c3c00340005804180c0300303c0c000c980b0000b4000c054100b54410360110810100075800405001294020394003244666603840d80541c0b240310078040d60414103c204001080b40c1003d600c0d501180d4005003c44d8002c5461129051004c203090b648c40e0002000000c40303000b80c042c060a1680608442140303a103111050346e503200c1e520701c150302c51295400e4035030b07004c02c04200400d00050000c0c03001c0301c0002d0b520111803d00a00030460058200e108515085c907165055101c2c4c05007214140e5251015809480d6034030400229402081000c3d003010303020005080441c850b030000c0d200504000c04d600e8015170071807900a007003d0040c0c05190049440c2c41d400c0000c2000060419040030300b5040041c0d4030340720303a842101c884100d84206941103040c00b004902c079060000b9582c1c040490169218000c4200d00707041e07401c1e8801d490308e = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 332429100 1250 332427850 332427863
    0x1e0a15090f080a12050d020315040614130903020a020d06050a1505060d050402030106120c080c03010903050a1b0f081909050303091c0f03170606130303050c010603080d0c021504 78
    0x101940011035007004c034200e4030100e04001d400c0c0644001c1001c01d0303a1044452900304006003650101c581001e015950190940b800c0503458070a6290100d5150710212052440140e10b0301101c03000d141c000d00c858142140c01500038824005107003003000c050101540c018400c44c0c540b410103aa01d4841e0b003010801e0b18070080c080d5103000c905c030100300050400a88140d034155a03031000083c007400490b010300c2e50f10344220040910316103445006414000605c0099020345d05100e07100000a50220454002000c0b600700300c0d1640c0031014400690040e1030900520000c0750000b19028840100c01404c82c018551642c100a0020360b4003c8035241c00c43d100f41034250b0300500100c4424036008041d000314400fa040c41c4040c00d00c040d101c0d694640f40084040d008180e10142d064012402c0c29440ca50003502681c6907440c2039601510b038145108240b0001d0100f1a0105017440710b12400c1d0002001560070495541c0c4070900303040c0c958018118401107501610484171810a1200c041d80507501c25904038a = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 332430350 1250 332429100 332429113
    0x30f0c0c0418031107081603020f090601090506070f0210080a0509070305100c1b060203070206011202030706200d02250b03130201021c02210c06061e0a15090f08 71
    0x15801c4d80e80500c0d05511041e503000d032100102d4260320400c040e1003c50890400386101300c3c0740d801800700f030141d6000c2081c01880c3e4803041000d5640c2180c403c504a03030054131502e6440c200c80c1483e4400407003c1c0b20081d80700c60101e03104144103174414000f5000e040c24403c1004552540c00341142d0723525041c400105035411901c01c2d51180d10040e8002100b08401e418484d455140303070b410741072040503401c600712a600c1e030201c02e01652590400405024204005141d07000400980000b03641e1030341031048a0810806085080210004901d41100384800604441c8500c11001e070103074803050880300d1001e0101c01500e0003010291007241c94130440d49002d44030340c070b9610f07112040421a00d03142d1050b4154440c908080443c400002c0880b580240e40754041c14003450f607080404507070380c140410b004001c003091101d200441e03004543e441e04110229034140103041504a401c1300403003000c2c103132a1710085c1ca5800060009a00c03c549103400060356980c00d0203520313049403030f0300400f2038001e0860a60118 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 332431600 1250 332430350 332430353
    0x2060408030a11030a090c0602070b090603040807020d1104050a0c0527090f0106020d0c0503030f07031509020706050c04030507030f0c03080301060203090109050a1401051605030f0c0c0418 83
    0x14015608090140c40201d200c065030810303c0c641d948280c035061882a83e4020b4101801514a40340001d04001d02c007614900e46003d00948190241403d031600c00c3e040000407400304030300310045454642e8040d0101c01c00401904000803c07a01245030b050041303040200040718042c0900c01c1c8182c140580d25020304150704c1130543d09580e608100d00700720f15105181000c08594540340c101c0e1244a4039810100e071981400710090030814410001c1d011b002d030302440f040003d0130110650b50f003c0ca8a103149006030303a50000c114027030000042c65591000c0398100c08509050560002d190040c01404180141e40783c1c4e5a0441161040f0320002d4069049400140700186c1c01c2640840b030700b40524055244181c89843d007006640c803e82c0f010001da440096003126558011403910b0040c0710131103420a109292904500007030051100d003504110b00000d200407800c641e039180704c11182d0003108807520f55012448618981c5d200d00054892481003d882070203903d85070150b40c1c1c0750b102d0b8a140c000043d246 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 332432850 1250 332431600 332431613
    0x50c0a12050a0e060c1905070201171512160b040503060402011101090606060905030c031b0d0201110304120218090307030f021c02030405011403010e1506040902180909010c020604 79
    0x14041c116401c3e2242201018100d0421080e8041c1304106a031565400c0d025144a4095001d5403401c42402801e11004003d41e802002400b448000c4a50300d106079030f110700c40b0710070000000407855441114210f81c028210000170344169401d43d090f521036011503c1c0e03090345155003e54424194140d004000040055200c0c0c0410380c012a4000c0000c18440c009984160507144035410420024554400c1040b2034542000307421181001640a0140c502d2565040b0108204a064043c012400c02c0751810459115400c0401c5501c3d42009132519035803641c500300010505850240d204410009440482c0315010510710f014480c01e100a516040484d90151007031002c8211800030342c01880180000c01c11658810325009a03140d014540d5142060005804241c0344802040c0161040c03006004602101d5202c580260803881c50208130390003100024071f107101d00c4e0481c1103901c1c0042103e41c41c40d8a0041c41c5130100e1400c5900b82c0aa6484600a600b00c0d03d00391200d0300140d1000020802040b00e = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 332434100 1250 332432850 332432861
    0x30301080c04020a023904091101030c050d1a010f090602101d0616080a0603020904231005040c0504020f1e0408030c0a0210021516051219050c0a12 65
    0x6550050740c0d00070a44040300c040c5407000e91a0502601c0340c4110306d800c40c0d28080c0c3c8417514500c04480c20044090180c80780e000c50080003036002e060642d20030786003d113035000d641964100c0402400611201860000c00100300d11564085804508081c45080d0780ca0f010300820429500f15034000c1640c1c000e401c090300042c003050f98a000360103020741c0809034401020302915202da0407996019001c5079860500400300301c2d00400e05190103280c4801800140c0d2503900c401d42082e00001d0480c0c01a078040c5d544000c201c00492041058490350032905071841c925041584a0340c020b110310503400d907980303083c841030b0302c0342d50726000000b00204076242a0f00a210308000b207440c101c0d40001c2c180b549820b551455079106c4070240300705a03c9a02011308619000c12280f4410420b480581540944252101031000014014110400300022040c0c0c9540c0b14000345d03051005048002080303070070104a80e41e2220000084444114180400540c00000700300440392154007a5580303201070508140040002c08 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 332435350 1250 332434100 332434117
    0x6060105034516090605130509010e0114010303180e07030203130b01090f1a010e09070507050a0305041e0509060d0c03170306090106140d050a20030a0e030301080c0402 74
    0x10340c0001240c82d145030421030124541d03607000041143d070b1400c600303000c840320742584090120381c2040d0b0705200030f4a41e4400c081942d4160350300401e250b1144e1042c507014140700d070351f4100715620f022500c6441e5407415981034122802901c40b0f54848450540e0303da0019418062110460114000701e011248290300071948640c0804441c01c18a196036030391903151400b80d01c000c0319075480d81c5044a00b02142d100300c82406030b904121806d188040c800180c01c01180d10700c000c0c0300d00c54820010b90300364010f00440d0030480e4031030151041c12800d842d000d01250441d010702e410344528409a01c8050040c0304240050382c10090500103941d86000130402060300400341121000003a100000004850001c0012241c403c400c65076224a000024808240f02c1640130101f0044500c4100c2884800c5000b26000704a0365240405c0d15620909880c001e0040306580341140c20400a00b91002114600614007480c0018030910901d0040c410240c2d0324003082c0100590354024282032036031460694001d01c4003c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 332436600 1250 332435350 332435431
    0xe0903090306041407080f06150d17040611030702012f0f03040302010e1c0818030307030201050a0608150604020304030201061a0c19150c0207090c0c02030606010503 73
    0x450390601181c2018019101100d040c01c2c0d04481c1501c946043c003552014001c8500101070b181800000c850b6114806441c410707100d01c1a00141e0081d80f5030a00041d404d80d00886d0030000d420b50703101408401e0307026226960000b911104030703050700d042c003108840540760141e40c0d4402c4820300710303888e910325050020210605242c1420900910a081c4114041800c1000c040c545542c50340c00050683e00c074982e08184600884100052010842d05640402c00d0300000310b41d460705c80f901c00951140666031040303075151101040c0e41040540c1500054441d007442c0c2014001c807a65420126075a03051074405d207908440400000380d0794106940550340c000c0c004d00c0086061503a0341c4041c4c0c0000c00441003c0c0f031091001445032442e00041211403c0100c2442070502140c685445d03410071803e40c03c0621207526101e03000300000d544200000406424407503001c10204880c0702001d45a0038801da8201e002c1c5c007525001452541c050020f80340704050b101003d540340c806c03000e5142440f140306018003c64 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 332437850 1250 332436600 332436607
    0x4020915130f09120513121109090607140408120c19080a03050f06090402010e0a0b0d061a1801120e160810090804180b131401140a0e0903 61
    0xc60346074020041d044842d0440010591010f0810158001c11200a1810f01c80100032090080d0300e400408012501c500c801a28001138615042d01c074400366000c0a940005c107101031110004010030402c0c01603215884804101c100090414030074002ca10074050703290044100001d5500c4110005c10034020228181c42690241c0501c260040d0031810007603c451101145c081081d0b074046c45801d4104c40314030000380c4546072002c0002c520b000000c100a040282c2c0b206103195688810007500e002d4188207070500c0e103842070100d10200411492080344000000300c910490b002c1840c00840b0032040c451441810b0b0306600d00e005540c0c4c5202d001c03080d02029a01d240320001e8a4044c40300d40c0e050b5510307041c5901100e01c0c1c441d6580c80d008055046150a61078182c1c41c0c6c00280d940000c8a040b81d26242c0d880c504800ba40321200010300460111607004201054117401c40031417640300b805040d100c1c0c1c403182080e0343c80d17001c4040329440c07003003540b40c004100c3e25091141c40083c00016510910040803a40fa = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 332439100 1250 332437850 332437879
    0x121b090f0f091303180e04032d23040506040302240c01051006030e100507030b060c010e190b0f450c010207140109050307170c01050304020915 63
    0x341e00c04507950160b450b11452464101035101c5001002900c00319048441e03142011b41d0152442c802a01c028140b0010380a21880d9500c281c08070700018014041541000c008420060082000b40000d41c0b0000d601c3c004603402d9911282c10369041c1c030301c06041c0c1e605081c01c681c02c0c00034090b034428403a00e4580442c034418210702d40a800611905007400e0010809040c19413501e00810042c2d0071500500d824201008200900010424104035100c080800c40b0745600c40c0a400402d80c040c0c140e03820000001e1042070091054214540301200c10b0100c40021286803c0c818540d654801c0042445a02c50301190b100e80c4500d40c256089880410064a40f4200c00350280160f040f840700d0074800c25002201240340001d40348144800c181c0c0f14081e0a0b6140c012000039101d062030b0080e00201c820301000040564400d040b5240a00350140854000c141c8440d6200c2d185c4c031595000b00141c0c4103001210000d5441602986c0c0281e0b400fa10b0b1115a0715507103c1c00300e606410720252500408000075402 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 332440350 1250 332439100 332439109
    0x18130e030406090302090109050f04060b0f0a08060105100809030a120b0a0e1503060618090106050306330f060705011104120b010e0c04120507090207030302121b090f0f 74
    0xb80050b89400300301d0751561050060204050b03102e101101e18100802a42c100030f942a035500940c401e80016a5210510014070304403807008040383c00103031290000c07030100d20006025060b20011501c0100b4807201c0c0008540f60345085841c18240c0c1c00074440915510f00a80c03c80c8100c4240300c00110b0041c14540200b20b0202c0300da8008030000c50801e05200000b0204100c61801a0341070380030304413900e03103000442d585501c5c002110400d07900e03070030029806040a5100c0c5024040060568015080c01ca003202c00c505001e118004041203401141d0340b107040c41d49190010130390302400000140c020503041041c2d98000c008140c0d844d540320103841c104440e50314020400790003002e42c14140f840503800e05924450050f081600c2ca00d80000901002d02c0c01241510b04642c03085d15040c0484189103811404c00095520102500707001103408420140c00d50040c02c2588403011034105255a40c0c40302e4034520403030400c0025004000c01045c0301504200324180317a070a00191500070310360240400701c0c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 332441600 1250 332440350 332440357
    0x30804141504020111010603050c060f04050d060902030d03151503021209030408070902090f0f010507060504210f080712200304051203150f0d02030105100f0501020318130e03 77
    0x2607114118401080119a088483c6000c48080e4100800450341580e0360a561a5103d258291045070042411904181079074221000740902a101200e08081c0e4541a0301038246171904a12a0180d403991081340361080c1f01c1c1500c99080568040303021840c01a121a005002e007003030304201602002a1800408142215030003070314031100950b550b0b0301c1c040f40390703040c898180c00640c021401080101407583e00c1051201045a048640c20001e094140050f03809201d01a0300402050030304c01080140320b910310f846e0602e00c455842606952400810465070207080c500ba0b1008600401d01090030544968070400803609580030010341041090400700203000031010b045000c0d0350020070082005014440c104070041c816003001e0560820001949188079040201400b510300c0750b040c0c9209a960080c422005900600200310506004400f050303054085c1c028181c002d8030080300000c10354800811200c95081c003551504081808008020b6400b610054030085151204c11183c0c200400b80003e = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 332442850 1250 332441600 332441623
    0x4061d0a060803040602101d0a060905100606201905010f0f06030302030406030f090804080303040201021c05040905040c1e0e06011707030507210b03010e01150303080414 75
    0x104841498400600c0c020344405421440702504244410002140c0004001542d0290b03010007141401a8001e07151006807501760b440918400c0091070400c0c01001c0d84856141ca001c1c1c2c090b00e0310003135005680e0b01603407400e1103500b0014000d09100d80c10901900c004c2194505400d00f034800610094914a40e4501011800e8900e80d548494030802c042c0301d80b04a902020410009012091840e10041d4480c015031094005061710f8166000c00d40c0da140c1c0c000100280c0c441040c43d1980d032204021a641c0d0801c850490152040300440101501084032610000e03407560703519031404d4142034410020700800307482242c0c4030001180108080d103441e440000300541c50b0300d6000f000703403410101125426018003400e060100c0710240610221403021a1a44001c0504000c00c81c2c2e00d9803d030480f016281d584007010710701c8400e412905014196001030704010700c12002030005448082c01d881c00c0740c041500801d0100b5039000100f0010340200c01c41507016005206080c0d009040030720480c1018950903a = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 332444100 1250 332442850 332442899
    0x50a02090a05030703020904290a0c03051b040902070c0e0a0506010906110d0311091005030901060b13050d02031509071a0c0709020315120105011d0f0f04020406 71
    0x84400c0c0394103001c01d403035000b48811001800c030146160003044c00c8400280000d008441040000314203d0300c0c42040314407418030151645454644200c0500c01840300b66070074000242002d01040c0004004031702442441c1d00b03166510300c0c1c01d01c1c1140e080001d500c50b401c00c980c840c1507400d0000750101d00130200c500c2a60019008540381c0b0b40807000401c2c404180d04402d060042900c1e410380384400c001036500b00036155050000b003105400148101070b008101a90380d000070047c05801c00d40794000091070080310707440e0080c001962121041c1c44a4090b91848100d00340984008203d603261505a4141641c0040c00340d40d0002c081d0200103c400c481140c161500e5804100c08201e0340c501d0a0211500c3c2160388641400c04102071a003684941c11445400b44098011011174001c0c01c8170452807202050007050720b03000c2d044180080340600b800348902d5035401410904549001c0510703e100d84500c80e080043c0089a441410828071a10b01030004c0c6e800c10307075500c4045150102010f80080d0001130b642c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 332445350 1250 332444100 332444107
    0xe0103060213060804050a1101140703170a0c170a02090603010e0601020712030219051e1006050312030a020f0403020a082b0c030c080c011805101404060f0f050a02 72
    0x2d8004031141c40e41d841042084586400c0201281010035000102c0c1e80c0b1080902d500c048800040301d000208090604c00c6260000300c0f03000309908140b0f010202030008541100d1940e403850060b00b121300c0220420007254003030300003058081901d00d034141d03c440c4401006082010510110305507800c240c00010007202401305212641d0380412841c0c009103010209045116402e40d0020b44600d201c449102440c28000302c0b500400801703200a0200680300740607050105012070f046651001802c058400e52860418089803604011035050000110000c4007499500c603084450025030040f5034001104e50203001c040016610b9260443c010169200103005e902450501c0c08000e82d4440b0540b8105100f20000e03c1c3d45036001206a040940c040c14812a03a941b507040503a801e1154161800055107040440410201500342c03e07001540694102c03145500300d9040e1700100c074070184003e029000c3c40d00000d03000540a40005010403041c04004ca40310024203610310070740d001075856001030b42c1c010 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 332446600 1250 332445350 332445367
    0x2a052104090f020306011b020301110a02010c080c04082e0606050702031009020f042c06010e10030b060906030f06040326012102120d0206010509010b09010f180e01030602 75
    0x140101000b03003460039811403442c10f0980001c0d181c030b002d1a404210140d46d03000c03802c0940d0b0b800c2d80700e08002d10403080c200b0b690f03144620000703000380300e103980c1c0c00042001074003c105080c264409681c280d03600c5030021311415607108840c1021841ca440e9401c1254800007c4020b400c10b00d0240c1e0009080d00d40310103403658401c1c41050b041000b003110441c0078600e400c404002685d1094010030a07141c0c240c5002030400301c0110010b04d41b1070031410301c0d4880e00300d82030318400c1488006941030403035040300031002c0c00392105c05001522440c09c5c031002e4008503140000ca203c41c5041d411071500041c0040840e418009028101820060100c07400e40115040404000300d0607511792106080400303607074000a40350b0520210041043c001d007501d5861407a50710002045443c1d401311103080354080c1040701c15100b20b0b0f000096491500b4000d0500507085800005a1094840c0170384080040507101c5910340102c0f800101c070521000b8408203002850b001e000510001528a9240607502819015070758071082e = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 332447850 1250 332446600 332446619
    0x4090f080c03031506031009150302120705030f0609060714070f14060601050c060f040f02031506040c050c1b0126160509150702061201080313062a052104 68
    0x12400261700441040003041b004550500e150300540341c1243c00080c0c0c0d83d29009100b144403445410081d042003100071041c04801001600c1400c4a40c22411202041c9040902d1522002c003540d40d5841a4032001c080703260baa0040c1200d0003a21281480c050410750b007615041042030141d41d0aa600041000810540e9481030200f07690010342070030715071f01d8226254610b40da1170b4401041d8401c240e03040381c04501000480d500c60b00070785400a04940740865801542c24220300c00340c0d18640b080c1c2ca045003d01240d8004c60070f03a44000c4142c805408000d01c0e4160311450442144030740383c100003d41d5001162402c198001940403d4540c401303030800d01e07000c01000c9280c99902c1d41d001c00d00800348220107865a80c100c0781078803411f03040c00c1c2032f868002502c089209400380c10200400d24100e00004244810b0000103000a007101604518025540d8502951401c0300189440c09031851300c4a40c0098015016901d00d100340305600b00c958141e42c0440040c0004000e15180941640000707040007130760354 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 332449100 1250 332447850 332447881
    0x102190f1e060f05070906050a03050c0706020c03030703050112080f09030a23160b031303030207060f02091810050105210103030207050a0f0b180102010b030a060501051003091104090f080c0303 85
    0xb40d4141b400070181003003c00b034941e01503550300c0010540c82c0d5000a8000039114103490b495540880203540f100020032009807240c07c02c03240000024a007400004903004c46445040c0c02030740040c4007070b140011051030008164040c5d0b44d0160140b203502114400680c1e00000c1103510708440c2640c15200078a8041f481c108240410b0584440018081c240150780101c03040b290454508100741d003c1c5071140c5015400b9015011014091916252030340d64032180580003800000b03c1210071109101485100d605951410f440da10040c80403408240400e5010320014202e0f01410388d2030607403210001e00300b00c0c02003c00743c0040300183c200440401c0982801550a00905900020203c44c103040c82d100d0400350040e000020101c1b0005890072140d83d0003035001010440000e011303074001c58000e003010b502400b020301c03805004202418008108902c030741300d071840e030660094414100c1b1040000f00b01c040c014190046d45c080700c000070194000780f9650000d111019488000d0b41d2285408120589500c9 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 332450350 1250 332449100 332449111
    0x91911040c050c0627030f040509160c1e020d060204150914091e1303110106080304090b06130905040b010f03120f09080d0e0f0102190f1e060f05 64
    0x1428495401c8810011030201d83c0008000f4041c4141041715401d1034402000ca00000c10f40d0000041840d50030341e1280080080e160141c80e040030a441d901f44500c01c0800070350541c0005403c9400c1000001e0600521032910329014402250800c00b5400003503504611318402c4400b0b95000500300302e405000906040009020308000d00c400e4500001c481913004003c484611462500000403648124007841c0e0014010150008030b180c80c04001580540640541c16404a081040b000e55450780c1401094203a504000107107003414a44007100d8003401030152810f0b4001024010110680b0300c20f00b07000018501a18007280034245401c04451550042c0c00804101032030380c00c02d201117070925441c580110003620f441040300c3c029140480c0c01c0b904a400420040c050300f282201616400480d0805030301d41190304c0443c580741030005a9640c0c000050240f00c45400c02c0ba41408502800b000405450180701107047c00c918000c603501c080b80074040200d4501e5a82c2120018041640c4501030b4040c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 332451600 1250 332450350 332450357
    0x312092109041416030b01020a0b0117120f04140303070f0b180c18060f03010c020a0512042106060b04031401140403140c070509070f020f010506060a0503091911040c 73
    0x10f040280c4100400070702c45031300205142e215459900f160f4800c0010103542904110304150650b1120007007200039610000d481454031580940b011071184800440328040480c1103094907180c64510040d200703010200c03045503d17000a11002c000b1401c6018065201e500c01e04401505140c081c1c45001c40340c191ba00004c403a50720102c100e1541d516181d8240641c000c0840401c182540e9a01c002018000f000c29500d8065080c01684946560002103103003a061145085c0c44107124420b5101d183c07400380b4881d018000b00302c00c6289202101c8081d0794141e80d03000305c3c00424000d0311641b50310b05907403160344100c805140703042c0d805601840070304c614040441c88070b0781e0300040c1c00c0c50344004080c441e146088180c002c07000513407011840d10401c03421005090107401000b482c541103e004d030101da03558054502501403414a40c00750001880b8461080c900189484d050011510085070245c200500c81e459921500121100000d40100031091991061080c2000b0450034170900050315407811021052 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 332452850 1250 332451600 332451641
    0x10e160203040501080612010f0b131a0609130204240e01020d0503060406090f02180109081f0f1a0f010f05030604090611070b010e0117031209210904 66
    0x550340d001c81150100c079024a4240065102e800004000f041c4154448100d5881c001c42005150060b4211807506001160204480c030031000214041d039510184044032541e04030220031084c0303000406403030f49110140014180500c0d400505040340c2c40380d0891800d180c040700c070749011040c004000f17912615552811a40d0700b04500b0000c0e595001d410402000e100001c80010a251203640c40311004001104003030150041030312520b00294030260300040f00080380300003204035500800450085034584002010403e10740051a0456070780c101202c803c0a031907003c211408000b5010ba00e0f1309484280c3c00c0700c82224888104540261444d01083c1400f4102482c800d216401801f40c07070780a0f109460205048031030f4502840144001040c040490001041038011f0003a1526414141c580c6584070301c0140c4d0f29103485080368041d4444248461f070041044011402c1c071000420b80080c01e080441e400410484501d00368540034a402414420b00866803e83c2450075000303481103920001c1d00c0644 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 332454100 1250 332452850 332452891
    0x21c08060a0f1409060112090308010f0e0403080a0b012c0a0906060903170d02070b150d08161b0602010f0f0213050913020a0e040506070e01230705030f03010e 70
    0x108080ca00c900141300f0905000001c03107a900a1100301090790700c41d082000103036120b01d4064504c0074280556140e1810005d400b00324290001501d03070203150562148aa19942c4c41c034014041e20300009801d0420048865810700b00399803d4010405540c610610f11390138015206214440003d40e020007207550401c8020455660030403034610a0701d801000d4544a00e00700340401034144208c407084503041d840042d890b01802207414842c0e0054814950b00c1c410a000308040201508a0840c060095002088011014024a102030340324510030050340c0100390800002c1c20f24500e0395400b00026075150780703441500040fa8420341280200f100021400c1008082143c0e0041095004850040d03500502095604100c1c55030000d020f90300401e00504982c4400c050340705802e00361011611441400040f40b80c5900a108014450348181d41d401c078203e00c0c00c10301440b150008040e030302103140c0401031500421802d00c01400002c0c07078021416525407401500341e040ca00000c0c04250511140c080400 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 332455350 1250 332454100 332454119
    0x5060f04031d03011409160b1c0f0b090708070e01031401060818060a021206030c0916050702121b09010803030c0a030e0a0302060105270c0307021c08060a0f 69
    0x1400306840d1030b000944000c440000c28010700c031103c010710a50103040b00300400254000755104c43d0904501040c1c48441d9102d4001400c3e00a00030000c0b10885181815001c4030915400b080d1003800401d004504081e444000c00c0003007c06450280004084108201c107a58225107940100e080a01e010081d1800381c1c81403c444078010b000340c0e001c101d4401d0205541c41003040d2041d00c16003501040c0e4006081c070284900082d80135000f41311200d6050310000c0d84600c2e0108a5130078007900600040880c1da5070300f0051603092821743d14802801024002c10b00985c072020700040a800000c00101540e1a01c0c1500441c0c45840c81c042030311910744900140603804000c42580d03006504e6031091a280c2c0040041900500010615608141300e82a10728090683c0024018101e800903220050701042c00395030290f801c504020119a0080510013094900307120200440d07028640d48150344034551000b400117040c0782060b02c4000083c851b20240455072809500100003002d5482d441d1406a1a060014 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 332456600 1250 332455350 332455367
    0x4180b09090a11061b12040303021014060d060609090c030219180906110c01051603050606040e511c0c030606060906031506020c06070c0306021605060f0403 69
    0x150140e00040f4a00801000e0090034102c0c0d11400000d0702e581000c400141801b036006840706800502c81c0500c0c0711003002e014410441254107099004240380c1d0b0380300900002000104044441c00d640380707400980200c1510601d68958483e81010a8041c0303140104045090420a2102c03401c840389000c0010050b102400f03009004502800704440d841d600b8207900404240c1d5981488613030024650303018407019880700388652084c1d0144890020322440032011120b08541d01034001404100901c80e400d000034805500c4043d803001c0c1030303011000d82020356554030501c2c540c43c2400c064605503980c015211300c00328078091800c2508884c220445000880c19508000a49142c05001c0d05c54000d200c3c00890210203540c2120b0207200c0b4913500d1000401c2055107109120000345400750354242c1d00c20910a11044400543c010640340710080d0400c4010f9000030411034001e95802000800199540083c0000f50003010441203015000d041a60402030002c14448a190b281d008220000780c025002c03 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 332457850 1250 332456600 332456633
    0xf0f070518270109020306010e1f06020706030207110301060609030314120103080912010e030a020111120708071b05030d05010902031306020c0307151a060703080f0c04180b09090a 79
    0x1410980748081030458010700140001079014050f000002c0303854070390016401c1c002c1500e01d1807041d052903a01d26060203122b840c01541c0068200680412545101c1d0f0098800303a809070402d031002020321350000c1c1c01c40c0c8686d07001e03e01003100380c98200103040d04603040e00540c2e100b14000915120400f9011446500c0c1400020001080883c0c2c1460742c1c0c43d1341c03e20032880b09100000308184900120f4041e40c0b6042649030800640c03c0216020407000f4020980380110b40c001c600401540f110f00042d03d00d0400140320b80304001440c120300301d840b82c55400c0310940c203005001071b680d68802c0380303408004e88070160810486207004005001c5020307041c500003450940c000d000141c0307551918030382508600c1215400b40070320410350303010820100a50f100581c4603401049003060b48800c4d905002c042d00035810054049900302c000150701215030441554030540c0d40b5119440e00d031302c4034241c2d02d90040300960010702c41d5540d041890b5074100760010315000780759403008009070b0a1070303907030140942f01c02c0c503c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 332459100 1250 332457850 332457901
    0x120f100c05070f0b15030f1018080f07110d0f060c03152c070518010905060307030209100306080304060509060d02030108030703030f0605090f06030f0f070518 70
    0x1006030858822020b80d04901da1040000c4884141414412482c01d000d80e0014141420154520810310b00000c40b00c0074100741c2c0000d0b185154460645500526100492940c02c04442e90b440c07000803019402084192030200050752070b00400d0500112441e4802c440301c1c080c07884a203c00020512941040d0310031a88a403000c00e80c0150440100c0c050180c00880d0081c0080152020880d801c49a42c2c0c0e0080250b60104582d048a41c060f0385e075000d070b600b51052404154100141c44841601001000c0a0035042c10f184030242d540b1004108154000c842680020742e02180e91003180c076010031a404200c14924050002d036003803000458403031207544240d80500400107804002600d60400740c5400030541d01c0215103c2d0b950b40152902c9601805040780042d25203001145400014405c0205070340300540180c440d6507600c9040c010620014203d1035040c07213100303201160001c042000946030260103000e03000c4189418180070480a005007400341808040b41040080000c000e10180751049851 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 332460350 1250 332459100 332459111
    0xc060706150504020f670b0f031203070f0201060f030b0603122508190201060f061103032e0b03060a0509071e11060411120f10 56
    0x90241080d8010b80c0c4425042400410302090512000300541030220b103c180c1518000041c0d99404011611003003a04106c5540e00c155001062030b440043c540746105821a10049170b40d40040c60040718014516001d1300e441d000e184681d07040507a108a9142c50940c014440500d1b01590401f10f0f0200512083c20806102400900c1c41c0c400d400402c0242014074001c200c041c0c407803c09014201084510501900c59401c0a0202d04681021202d44c100d03651840030901d0000340e00b106000d03400340b0054030001014841084401c0300c2c8581005401e51175000024005d01e030841030507903050306902c040c06010302c0180c659585540841120340c00105070164125103485802e0f09884600b2080c20760314010744001011407240e054800640c010241207d005003c2962031003040840c180c2215410005a81d85242c0d640c00020398a50308840840c03030810404028424a6880ca005070884050320f0705a81c2c000325034181d080c58194040c80e20550300190501d10008110196a13600300542440d019968a = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 332461600 1250 332460350 332460371
    0x1f02091804060f060b0a05040b1309021201030b01050d0c030204051803040807050102120702011b06111614010b01140c030409060b0714010203010f0614070b010803030f06030c060706 80
    0x18000c02210a841042100c624101800d01c03a00820f1120103a1615a01c0c000000c9900c0400d0b1090303c1c50540280c0e55289000e050001031491504410602d0031072150306200810a8480d2f4000303810449040b0407441e005600d0750408615040040c0d2240b4081d81c4250b1249001c208104640001d6a4068034003158685a002c2441440c010000e04503c0c54000481d002c51051804194042101d50076070840b5002003110700e0382c50701c03481005002404a50040b900040c400000b40903a003510740621b1001071494003089172548642c0c02501401800f88410300e40784200001940c1c1c00c076803201030000801c040e10744c4100103400c03150b206035102c0c2c0f201e2010400c440110f904104541c081c1c00842c4040c84003ea58060002c2240c0040104a4a0541c1042c0340002381c41d051003074034101d8802511ba202c10134a0042c00356908070401350440e41e0078004000c4080820850030140303008040c0e00c40259a28580720390003072900c03000030b40868440d030048990303075046070783c0c150640380f1080e0030150001c1d440043c0b = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 332462850 1250 332461600 332461609
    0x5090612060a090510081209060a03050a0605280b03090606010c06090510091109070815030a050f1e0a0309090b031c18090213090b0102160b0d0b01021f0209 69
    0x83e40c800c082d803504100c00c000766000a04000812900d0140445a00c0440401111000d004034403c441c1c104c84c0c10701c40325800358801d4100540040c00401c0c00140305440324040781c103080d00b00e20012004070000c2c0d10010500d404016030002001031045e40e80c250304001802c0b41d15010050009810004542c0944090000d40c0e40400c1d862544801180c05209190743d040303000e0015414280c92030f07d06070380003041d1410f00c0021144520130517a070314582a6200f004039940c0000f40002c8079010301c5144040e00004400300800d51203042003100400c4068900c0510404154400c068941c0c20b07005031581c040013070b4008121800390760300140c2c046611007001000ca40750104040004440498004800042c20341046600750350411404200c0c03d07058803196108180d103e80385040603400d81d132440c20042c03180d03d41d101c1040d0880520658904c01602800d24001801d140c000c440940c1d0006840c8405120303501c40c00c4013130a02800503040725420381c01d1050303010101180403200135400041d4045d09666 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 332464100 1250 332462850 332462869
    0x10305040515040f0b0601030b1305150a030c052403011511060f0f090c011e020a0b01090b0319030206060d1106040308120a0b030d0f09052e0509061206 67
    0x40c00e038441001e078506403c02c42244c01c003825040e605000400d012a065520902035200c51420180c801c0344500e1741e07504010014480200004003410750220350055030f5484421210086014220324000c0c0c1d8103041c01c0082082e882c2e011011200e0544280001c1085110242d038111155403075000c41207510520140c4241c031a00b0200015030141000700034582c02d2981490303004e4607905466101964400071001c0d50b41813a00f42403404640701110141510300144401c07500c1400320302c1a11155949580c0b00d02c0030b00801e81200e07048035240d03240c449a5050402100d50004541c298004428905440c0a5102c4001905007400f426044903054244407010364407161039000900410340c1c4540c0c90500d42ca480d08081c0104000e1f8044201241039840e103405681d10b0040d004010b84071b01d00d20a041900c6000e0b4054117a0207110180800103029a6a2003041101410600303625a80c410300644085034420184810801d1001c140220403250311408242d8140144850700580c45486960000d071a100 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 332465350 1250 332464100 332464123
    0x4050115030f080c03191806050f04030609060b0307060f080a29010e1905010809030f160302150f0601020d0206010e07030b01020f0d03021c06050d020d0609051002040617090703020103050405 84
    0x780005220002d58050704001e0311407c03c61aa0210685403c422285846007503000561114240820300108495910018809229080c001011a1180082030804040c2d91081020403c00001041442c1d040f00b1042c0d0b100d01444000c200c1d80445220100d08801c241541c001c02c0c00b103010052115900902041509800082508050001c001c210f000d85181c1030180a0015800c080422140c02002082d2004030382000841c900701001290074049900400600350110300c030304031000b00d502101c442d0507070040a95220912042c81c283e0000b91034180c1111078442194443d1004002d554408a00c803034202e68a4600440c0d00d074030350b9004074a010301d04100720300b4600a00340400e5540c2d401d87d00030414a0b40780040d00b084507660082100844d007040c810140c10122081001005103001050b0b00c03032051207600b000070703d04041d40b2414506000b551411b074285500140078811541c0142000b0108140700c04c000460f03250608006464030301904c0700038107244e1264042807c10000b40910268103 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 332466600 1250 332465350 332465377
    0x1201031e020301110a09091404080304032102030720060105060c0304081203010303090605270418050c0a080f07050d05010219090e01090b0d0b09100207030804050115030f080c03 78
    0x1c481684d41d400c8a52110030f05201146203041c001903890194000d0440241281e8410300326942e03507803500c51031544024011410080e0807006050701002c200d90f00c0001800d103100c01602d070301e030440c006482c00c1e030b14003c00064140f0540d0125002c0c000002c905064035410b0360000d0301c880d003800405145000f5500b2050f542c1c0951140c0301c24149244001c0e604030386c0031755900280c0b50784d620000e80e01485403900b10310040840c0c151004922070741200c0d0100b2501d000e0700000f05080075007242a00000c403424225150f03044010001801d02c0c1801444001d406140702400d00d40d0300388414159500c61902c503e5000d11201f03220f02c07061110030340c145c2d113110012012003c022003641d04010b00f000400d0040d03003030207210040040340c204028480d500d50303031001800442140b81e01d600d03030398805031005001c05a14451801080c2000e42c083c0080c0040a101e92540f4803503052520b403090079682403984e14100c02c3e00d0418100003240c0c0c15040b00000c2c070340002813542d6495000401c1421882581c070055081c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 332467850 1250 332466600 332466611
    0x703031d2d060705010b030c090c03010603090201021608010b19210c09140a0f0c05092e0c020f0f0d1202120318160609050402090123030108060106051201031e020301 73
    0x4c0c0403064103d1000b41ca070840584844000300e0f0f0810010300e206440001c50741c182400148110390081d8000e032042801401107405c8101445001c400c442403e40195410365103600c02c5068908044031002032192400000701150385c01c08482c5004004d102c2c40c5201d0881e11160208180001c407404c1d100900020103090084a40904541003030380010703100203c07100d1600b108141103841300e00c607020440155a54552910013044100203021001c0c43c202003041a00390030440b440c0e000e003c01045142a144c0394881041468010070514421f1212014000c0d4045000c0403029654046003003016680300d540841c2a82464804a150548091803501e50500001c14400c10301103003c1081404446501255000c000340c813440380d0356610f14071560000ca00d0911080c05546003a03005000021018580401c19a0144107410601a4840389581c0411300010051121040610401d0b01426aa0030601c1c6004440c05200c00000c90511001d8400d030302840715080041c10302d0b82d18048054004009228 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 332469100 1250 332467850 332467853
    0x7050303071e020304050a0501050d0f050117010b031f0207050304150c060c0f1e030b040f271a0406020903010510060219051b0609060c0703031d2d0607 67
    0xc14982060080348006684002c0075554400402c441c280ca401412100419140c8401520150040c079122803400703880c2c2005040b61786151003203e000b03003408030901c10080c00c02c64920b1b0845010b4006039000f50400080803203907a1018010010301d2020010059491455040660850040b6080001d0210001100e1b024456200b404030215a01405080140d11901401a654940b1848074200400d4180c0e00d5682002658112483d80d10198100841c1041c0c40c50001000c81e042607000b02c09580d5078450b40d041301090300c0b200700003141f040c481030300140805850345c1e81101d002c031910101c521a0302000a04001c0306030152030440c0c1000c2d00070710041c20000c022620101c520b0041000522511030341810071140304003410b05080d0004041c00103030040c02c004240c9a480b140d07240340c000305c0c10807143e042a2503090041140082c1c4201420072103040d451300600480d0302050000b07a4517002025040c1035610346811451158001106107804c00b1040c00c0501008007510003a03a004801051120 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 332470350 1250 332469100 332469107
    0xf051201061a0a1b0201020a03080a0e150f1806041502040302131d03090f09130b010e01061209330e100b0409051e0705101d1f03110705030307 63
    0x1100b9005920303445103000c1311241320300008200f04800f0340140d100c003041e100800e0256401035000181f91030040b480344c4041036440d14005004a095210700841d20800c000303d60b80c400c580390802c1d06034080d08850000e80045540c0d40101400c090110300200c01200303025a4594102c03002944d014080b5044007840707058000040c580102c1d20038501d40884240148040c0200841d08807560007043d054211144c1014410802001440b80b1084003840b00c51001060201c2603540c000e084410420801e903040ca10000c1c038410080c0000b80307815081c8090540040c1400c81e040c15004084d4014070141c004041e280240022480d0b07061000519203801c0d0108000d000c114103003644202070050041035890810320088615954000d4115080074111091000b000c20018106e00351110490b512540c40e01c000600c4144004c269401033155650400b6011a0f540500e403000d010888a6558001400c00d02c07007007a94108049070b04041d0703a020703803501224484d4142c5030300c19008402c69444e40740482025 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 332471600 1250 332470350 332470357
    0x3130b010e0a0b03120a120908040b0304020102100905030f0a0e04050c09150f041a0d0f1d160e0c0409060f1e0b0901080601050702060313110a0f051201061a 69
    0x40003031500f40f6003c2d075110b003070000d40d650301083c502d50303007525045801d48100d07400540a0216645151a40c030b0000110b60184094005024040c901907500c0c140351002a1619109540e043e00c50342c1441c7d00500411004000e544036024220315282d92030352000d104603442000d0700103c03588107180c2018400c580144001914a628094a882702c3c0c8120200644402e030040e24266100c4a60400041c0700b000d100a0900c2110706070075201c01d080410700c1800c541518242a5584e03034071666980740c08203400040e82c2100400321701034050002800c0c00c10741801441c0c060301070002101280c20100b0001041d070303070881d0000c0c8480d01042002e05c0d22981d60710880e903070910400d000000407d16400181200c29036100031121b90307081a6103840803810041d1500d01e0010403950500605000d840d0268860b18025845407414184507902402e4034940038908940e03240e0128001c9998103005d0050a02207104101544c2c401ca4030070360400d003000019170140c5002d4000b03480c80c0140100001d000b1b0740c060040c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 332472850 1250 332471600 332471611
    0x6090604050601090204142e0c05120306100c050c0a03030518040204050a1e0b0304060b0406090506010f030b1225050105130510090f0605180306010f03020603130b010e 74
    0x1a02c40c2d590342c40c2002c02c103a004600803081000d620064081603403418520394800c5203250641504462143c4191210034001c061401c40862521191842003000c280201d80c036a8429520090071030400c03001207205911144101014000c549180710140b1000304644800d400000b000d000c001d41d00d07858010142e402c9042c03030f09840031032103030600c445242c2030081d20240c0314007a10345c1e0340e850711b000c2d1001144000c14094500d00d10514501250001c4010021071045000e00e40c0400d23100c2400c405d00089951503804502d1240c5000300f800340581e07200d09008498200c9281c041580f858905c0001c1c8000c000a058180510483e080c04480d890f0000c84110f403401c9540714190100d03a68801074896104a400c0b503079240300d014400380201d10f40840012a040d140d40307070004001e900d03000c4c0c0d01c1001c1081d0300400080303000410901d01d0049404907520000000b50084e20455151020f569441c2d122800b00074424400400000e170802c2a942120f503849411800e41c0e02c00c0d580d5911850460300c400d490 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 332474100 1250 332472850 332472853
    0x6130501061115010501020606060307140a0906020f1b120106090c0f02070b090108041e0606030b0603190b010623031501090501110c040f0902030109050c040513051207060e0609060405 81
    0xc3c80315001462007803040c100d402c180c01904290383c41c0c03c2049043c0d88014036503024042c1101d090a003c440844c00b4107400d08040d1108035940b818a18040d18009041c000d02049600607000303500c02c802e80c50050140d040040c0c03051862003404041441c00341940e1341040090310710b086400300710f450740070f00c068070940726540135a04000c0e10b4400c0c00160f441404040b50105901001150000b02401c0e00c0201c43c1c4000d94041d601c0110580e94442503454940c801da500407444800d024091405000401080c0480d0540854900d12a5250a0003c01c14030035401403205030144580503041544070f80e07032003000e190100f0780c7d24075207a5409903008804428440c005218250045084c1d405401c0c201e0004010000a02c2144d00107001c020140c94a50001c0340c12a0301ca01159005032401d0240d00307903e0344284094904c800442c0c092100f1100010008034040440042c42030101d0380100303019002c21030071800940d581f03406040000143c003d00d103400c08584510820410251004600c1d02c1c0182e100f0390 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 332475350 1250 332474100 332474113
    0xc01030c09052d0108010806040305030a0e0a03080f0a0612020f01020c0a03050a03020606040504052508011104171c0305101805090c010e10051b03160c1e030b061305010611 76
    0x30f0045440090901940c2400e40c001004540440c4c0103a001d550300501352900460034103419086c46081007070b101c10460100380d0b031100344491b5581ca01004d0b41c0c4095081400c1204d0340c03900c8c111400143c3c6488010b40940800c1f000a25964400d00c0303110030648000d000c102e00d05a4900e0700d1544c1c0d034141c1c0c00580c014000c02d40800d1403450580101409941c204006142c0021030341c548092100003940345450241121070f0024507404207020300b60207070588144654450b403400120b40881540c40032030342c5e081d0b00304000d040c0011512000e80c5a01404c80d140c009003d95581d001083c8890441d004928010410f4402015400305a0813252091a507002620307040020680195028104001c5c19544441e40324079812016206102130005d10407001000b02c64120740740780e4282035501450100d009060007260340e100340140d03180c8410040c40e03800107007400401e8403254540e8070034041c0801801e4100c0e030404120f041d41d801000001007090003604000c5542e454001400c02c0e1341c01260a803060050380b = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 332476600 1250 332475350 332475439
    0x220e150f06090d140106180e0d0509060a021f060806010f0e01031b031e030e0d020a060c02060d0c0c020a0f0b030a050405151f0902190f05040e07050a090e090c01030c0905 75
    0x826038501427400c0c0d8407807a0510521404011b9203810000d600c104610a102929000749003840f000100b214800318006000b0f0308040001d82000c1c01608046444a001c0608100c10600d08101604498000b003280000c9001c40d80004804030b507960019041041c13046564589001001d0b541007032510980740d40c050001d6001c00d0080207044101d0107540b15095180400426026802e1110b16a100800083c6010a022900c0044502e00d480345e00001e0b1030300043e0800c606010310000c010703100301440b048106181540d08070982c8802400504a29114070104003009420414a03030500086c2d030354010a860308603d070040c8841c0d5100d04a1840e1a0450001441035861084404e10a0388041c4059200d0100000f5204c848824106004100e4100300001d601c42c007000c9001e010340c0056507007a03070314500410014402800f981001410b52000b209004040c400082e03550811502802c0c00701da0821081015030b022480c0da8085030b08103042d840024202d1540d00903502e10b100d04541103004030801c1 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 332477850 1250 332476600 332476603
    0x317040e07030b1807020102090603010e0406060501080f01031b2403110705071203090e040b060405060405090a120519030501030c06030b0105040b220e150f06090d140106180e 77
    0x1c401600360084c521100301c5024111000c80079a104180d40000b40c41c041941f00401c90560003644928000d4002e101030004112040c09610020f00091070b18003160308100c912248481010f100013400a00d603844108904480c00c0313140802041e03403180c0500041e9a8540c41c100300c54001041200007860840800b040e0a40322094540580c1c00500420900c0c0c100b03820000c00084c0303080c00303500340004101c002405000c008170491259200b481d981c9900d00b40241030000b5218040c040d5841a82410b007080455400010a104555000350000c130980c3c048220a882030f124941201c04107802c44208040d505400d608698100c9106d40405a2078030f6030f902046040714950101640090010001044007a4001000d4140c0302e009441c100060060700d4040c0b2500c5074a41d100c0d41c0483e502204015145e09001f0740b01c00140b00545403e0350280d072200008045e031040e200c03118422010680c0301c40600400c425a41e03400d601c1040202700781900c0b07901d4440c1c0006250141001642821500d0750364400 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 332479100 1250 332477850 332477861
    0x1b1a1e0609091e030409150603151202090406090606060f0206090303070906080903130626150d031b051c051204020d02181015030b0303220317040e0703 67
    0x803000080c1c002e08004401c032402c1841d51501521070f41c4003c0c040490403a810f4402d0040200703040e450008028503080c0c000d810344200c0184604500702c00b5004201003000300c20040407941d0f040300c40d00714640e10b915000f0f00030306400d040036021a03e0030704049482038105281644181154088074041d030303190000b0700d640703100440b07008000841c0d030b00c010000e941c05604142c4d041014a401d9909201c10f09042101301d070881d600c5000012604801c03503a404981401000600011007221942031400c1840c8604207038180c2c420501590345401441c0606208461092800103d610b404000395503901b4020b0307aa403404c501c02800c0d50602001044468094001c44000e00d407120070a94503a5a40d800304059010100c00913604041c0920142001420480714148921103101c2680e00c0c1a0800c80c0503e6014081c000c0c1e030051500d0242d028906940c0002074511031100102c0c0f1580482c007a50304c031848103081d030340000d22031241050200441081d1310b010b40161000348914036503650340c0c070004405495 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 332480350 1250 332479100 332479111
    0x209030a02151210090513030804110103110c030301150c03020705010c2904170f0f07110310021c060b2713060905090307031b1a1e0609 60
    0x24000308a010040c00c001190074040c041d65003405081920816003480800d904070740101c0403030032500301072144040c244101a000301902000c00380441032954050314001b00034001410400c0c11441c51002d40c2c1c40b0b030700400c0754024603a6820742c45040c8134458580e01d80080c05900765200100c0c2d0003c000520a0018880407a01075004042e110301d4071006548002980030b040d80c4c1c0105002c00d180450100c4030360b100e030f1302c01340d06540c81c41d0340362a0a00b0340ca218600e03240c001800d6020440c000081c0b440c042a40e42206258000c3c41e624940ca1810205043c91143c1181d014000c0d040340001424156010700820381c408400104240030b07408a55040f5001801040412074041c001c8008001c60503800c040c2071700102d11280003a0b05100000ba04004d0040c410f004201e48410702800180280d0140c180c002e070368103004601301003c0780e401405040a4041075004040094205414030180804c0c500741c000c0b80ca80d690a45003023849001020341000c5520200030844240030610b03500f070140280d4440c4 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 332481600 1250 332480350 332480353
    0x10204052119170307021006060c050616301e05010504050601091404060305070b28050304020607051204030b0405240a0b0415090e0d030501030314071e0b07020f01020903 75
    0x445412441d5105400c045e10220440c4144044458180010321171100545100c1d1a00549040d591921515040c03009040300c0740c103014040c0250402d07801c0501c10000144c88103200c96200c00084622100380b00300b19001c1001360502c1d80300c440f6403860014100064038040c03401e10041e81c0f28024003050342d00030784109000464001c000c001c04071800d8040a00408001e0000c03c0881da2500c0d41890048250880d0128100000303402e5216514410300b180c0723400c40002080d6081260040c0a407503404000d2000c3d00500c1c0000c2c00008001c8140700198000910103810740d1256202e0805c40a1400d0071641180c45100d686084c1c0b01c1142d0110900600b80c04071568500300d81e0b0340700382038400303806802d515540054440d5150a09006400102c0c400b0704581f0000180e14404108050721b451190107071001818941001440440c0d4428040b00070401c00d44100d50f5230710094503040c0d5038010030701d0305401c016040300707403440800003400700040c029444c6a088441d0304460303005640c00c0384120440154103 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 332482850 1250 332481600 332481623
    0xc0307060e1212010e150306040c090e0601050a06050c120a02060106110c030a0305092413150503011a0c0d0914010914090402060915040e07050a02060a0e010204052119 74
    0xc40c80181e1001e6803040d180c5026400d15820600460710341300040c0c50031100a48ad6420501c00c9240c148110440130b905c1c90b00504955140c080030a811810901910b020000c002400d03100c0c3c0542001a071507041c2591002c1592480c1c0c14074000d465441c00e0160f20700251034280307070b100441400220754500312801400b03030541d0511550165969400064020f030825410b44d050b12040a144000301d40a004986401da034401a0400301c940d0403041c0c0d000002d01c90441625100c0960b8010300752410b4981741d1082604c01d291414035507216008501020515104000324110919400842801100e0380120138000341d0901c5401910048901d0103030000e920012a11140c45241030301d0312680140c0090202c0303283c014003401250200a080d55049000302001401700800f03054840190b5001400e4039040d400c240820f10b0003510b5100c01740c8000075060302c8141c03449036103100703504440c0180001016015804c01600700f84030000b9443d10405098007078030072086c2c801240200308600150b402500d4415 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 332484100 1250 332482850 332482859
    0x30f09060f0f110c060705150c03040503030a0c0e1e0405070201020f0906070821040c090b0904122021180d11060d020d0b040c05041a0c0307060e121201 67
    0xa905450801c901c01c44e2062007141a010344900d40245242030203000a81a452a1071000303d42401020b4114030384000c0400c00c11001c40c0307012060340d400804215011074100004501101c5101c0721055640d8416a000d17055444000e8000146141c1b200136502400140c1e90104141d0803070090341c0f1355111590040088400518280c0000e05000348245442820b01282100c002c0e152a0b07840c3c0030403c02400c210510082c82040c5038000010610540107010080030407000c903914001c060b10051604007003400b49400d450054004c91384017120226518031b00702c04215503681e1105144600b20841d20780f295000c88004504003126a0101c50000c04425002454140f01c4400c0c5004402c1d140a22400760080035652480c0090a40001da0031000d600c0d403c2600c4200211902001d11b18030451506020800741e58020702035600300c64862920b2103c0d601da140c501e05462194105900540c00002070000400000341c2c88408100020402c07510030072590442c030505403161059041c0e015488400402 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 332485350 1250 332484100 332484107
    0x1a0c0408060f010306140f0c0717031807080a03020709020306040e010e062a030106140f1303110402091f05070b1608100e160e030a03021b0a03150b060702030703030f09060f0f 77
    0x7103e01d2045195040002501d200b00d070980d04141c0c3e1400720010003000c6a684402e04015110260940801400041a050e0b0f0080c0d13844e46680b203048040b44c0c010001401c540d6907544410200b4442200074046059071300c1815450f175800720b510606000d4402c100a042d007140306d149068a00010090900e980d092481c150745992404002d1105000304100c000d04400c800c0d0301410102a00a00701c0800b5425460b1405100040302241c5026510602252021799201d0b00c10710400b0710715042c110704609140000b150144103104e0003a00b81c1d01042c00f071208052088035044441d080326510304050b9201c030400390b02852454800c104400168a001c1029107046c000d1030303402e4100d1030400716080c40d450000f180c02d003614004150702681140e0064062103081455920800d2000c6800410b5130782140e481d17440100c03600c044000c400e99507400200090300c440c802c0315050794005040318031855480c580141000203010419000076a2803400049050103451800f000711020348584028495410048 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 332486600 1250 332485350 332485357
    0x801031502040f0f0503070e220201020c040c0507060506060c0a030f1b1401060f08070b09040f02070b0a1404110405040510150f0b071a0c0408060f010306140f0c 71
    0x200c18040d400c000c001081c816840020000f80803800c809040285484205401c3c07030030381d45c0000b801071803250800ca04a401100c00c0060709901c0c001803e8440d4180c00100d1511a075542e41a030002d190440300c03c09581c020740501203441c4100001d01c031070b075604014005240109040d24a10360b0060980c030000a008001c00e07107070065103182c08031a41001c0846043c0480b80d00909642c090b154043c0314140582c28010a406041c2040318108001d10b408061503840300c1c50700c6040c4000401048212452303456802140a5070003e0b2801d41d1980c0ea503003003c2080e9071040e030360041c20510f8030880d00c803065510340322144a00c1d040700300d82c48900c0f0303000e0501000d400010812900c2d4000c1607061030740d000880c40742d6000d8801460305150041e08040311302520058540003004104001e00800c2c0c0014001e9402c088401031070301400c806600c3d18980b060b128082e43e00000c0d41c40c010003081000302d20844400e0350489002d1f500610240d24203011620b914142039448840030700b22140002c2c401d11a04005 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 332487850 1250 332486600 332486633
    0x903070b0f0910120f140a0c120203010b0901021501030206070807081605030406200a110a0312050d1a100f020c0301090f0311030f0d0506150d0921080103 68
    0x9a440c00200c1c1c0700007403c10041c00d01c06800b066048461030071410540c4115101160124410054002104008080c40200400d045542921404191039040c800c88200480701200907003551656181d0700c0c40c0406810002ca044d0040c8a80d610548400101c01541030480e50060b00141c54800f40703441d103030b5540d8440b404c02c1c1da10100030410f81c40038005020507032100d5801030024540711800c10400a1411804040213101214604480310313506401260031103040303500c54071190f420189800071407001070761948042c240d4042d004d14259401d400200030b00080d100104100b001031901c01c40c01d50b2190b4900b49035508a00010b604074280d5010b109440b016510701d004440c5282c4140000909450000c4030482e5102c400100d5241010b070060002c016034910b1134040e5080503a04412050700b40200c0d981c80c444a500c1c0d20101d240f80d00c80c00b02000342c000c144010903a40340c96212206e40070380280b484c200c1341140072002d0940c00520368001840010360f039949090f5030341d1941e01c501500c61480c000 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 332489100 1250 332487850 332487877
    0x70e0d0807150f110c030d0f090f080301032f15041814130b0a0c0c0803010311090106051801030f020909090f0d0206070905090414100b1201020903070b 67
    0x1100700442c8502c4481c80c60816070890104140d2444a044420350b44d1020301c2c5442030303500340300d4034030620030100907545c0c802200240000c49010f144d074000c020f071041c2c04014261444020042040c000a00e00540c10303240110020504107034001007081029400d032140c801d4a0b036441090345654a804400090618802203034941040e8640340d41040a86d80000942d100703640e6500850014052150100d901205000b4200c9411a02d40c494001e906002046012003a50f24170300741480300d004a600c01c0380203401511854a0f90b860780303414454076048180c8030341320301030200c000181984184101c501a1118051002c601e8954500640c0503200d0141886041e903001c0c0300741482900d0b41541148070386410b000420541c20032080d45414110392520034411074114000f0840700940110010040314030980f8050a03a60703441c14440307107500d01d042110145000310300340d00b007818400e0b41003019200001c460692900b070403044080e080384201c0c0021070301a00900c00030003906038000701038a5080071300310 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 332490350 1250 332489100 332489107
    0x2071a031504050907050117010509040b07030908270906031216080a1e0c020f0108040302010b0904060c0906230703050c030c0607030e0a02010e0f03030c12071703070e0d08 76
    0x40010b0503500100c1d2a101c0652101c50308001035030307212035030185014000151004079418003000c510036001c02803011305010138010100d078900e031295010401958010114603158038202018a44403d103d12141e03000b90304440c1001c0c5180f0b82001c0f0640503880060042410100e840e03e8101d041d0016030241c01181613040c00e0b040841c2940004005980f216640c002908009275200014052003550480800c44016030000058507501c0d4400b03c06202400c2180951b9642d16040707024220007085650010001c005120070000960400c5402d91016140d24001a8071490203e820569a0b5880da00f22940204034010b980c0c038042c002e02e909806442c0651a10000c1c0406600c0c5910032440340c08207902c050100040b1561510501da450310310880a44010842b540000b896a51018080d500c2100b0a80c3e611007250303410000c650000038203405071a04548181480c40305504118820340351082e1502c0450003026408049903c14000c54a8117981ca070804014070480144000c811a00d044042 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 332491600 1250 332490350 332490391
    0x30703151a041a031510020f03040801050702061008030f03040f080c0a121422030f03120c09050f01030b06390a0201140a0c0b0a020c0c03030f0a030e010902090906100602071a03 78
    0x5000410203400c00d0750020078681083b110082c68607000a220403044000d030441802a00404001c50304507480c400040d80d100d443d0380c104101001c0b007980e802040e5810003d4510040413002c10030040d25806440c01e03400041c1030f520151120710000001d202d88003400c0002c02c000204601104403000c0b8226440c010550700ca584210b010088240b054010940075000c00318000883d00403e46102281d1410000007441c1c000401d040010b070070f00707050506d616421341007120389600b0141c035600620350b1041807244c40440d140910200040e11110503075000c03020760075001c450020b83d0600b620f9061b036440008060282c04c40b038554004414001c1000400020100402d4031010740602440960200590350117012544903c0c0402052009000390024008049103140c410181c0d0080034003402d010860400d50406a8014000844020343c440b0350207050000a50303000818a1082c0746025109011070b44805050b43d8500c0603102d0044e01c0d10a000b049680025000c02440d040a00c21150b211103080c01c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 332492850 1250 332491600 332491603
    0x1204090f0e0a0c240f0f020a150903170c0703051c02180108090d080a0e01090f030e18010f060c020d050d1e05030606030703151a041a031510020f 64
    0x48880581e514107950b20103120b13900d0001c11080103003605a5030310303084000940d80a0504400040c1650502805050410145d4000d10181d90119400000c2845041e8814800d0006080c25207043d4000b0300d01100c1c030b124400ca44039039140204a08001c240c1407a100d0768007207e0544c044d50446406902d824400c41943c02d040c00a0150800d04035080b5010300024400105032020007041103015034048000d1002d0107410000311074011929000101da0600c000014a025080c01c900080c001103485040f5014141d100013102d02c01107049810500c800d40342000041c00c64020700414024920800003003000310f000300c9644450610251000a20b21f85030b844250401000001030300c08909000d64071000c5942c040b049062008250410303d0960524030b0108005000051010062580d55000c01c9620b029480c01d0000070180e41c3e40d448010000040d509103039400910800035501c4c01e04441d0790b110200d1209a0748181c5402c5400d1248102003420450400e00a0f8034080c20340c010150040201d140 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 332494100 1250 332492850 332492863
    0x503100b062104030f0206040f02040b120708151008070918080a09030512120c0702010504030804060f2307230f06040c080c090a2408010c020f1204090f0e 68
    0x1011407584a5450a4100905a017428403503080440d0049020000002c84028890500c0d9030152000035002c0c140501040410b07141d0102c0031201e124007500091001070000c3c0e0fa950050781c40110586986030482c18010200f618007a400c0345030130800d1305218001d92988546207841462030a5100c00d0000e88035030f0556400402c007000001c81e80c100500a0110812221060512400c1510b16003840190342102801d0080d0511090340d00c0007a4030030075a84603005640143d90070032034040d903990b542c1e84090200320848242c0c1c00401c1005654031510959101d120000c5080300b41c41524007411603681d4050351900301642c0c00a242c03001c80580002e40b0070440c1040d0a40003500030003583c2050304100c04030315095800300000354804121108a621103901e1342e03030841d103401804140c04150044142d000b1000350031207217501c140750100080080e415000309810916603000c0e101e00da0b150504054640e9162120305448000c201b2042141e10499400302031003201d1104009076510714130b4000b41c100403 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 332495350 1250 332494100 332494147
    0x1d0102031c0b010f1d0d0f05030c0a0c080102270409200f0d0201020d050304030201060509040b160e060a1b020901090518010c020d0c0f02180108010f05010503100b06 73
    0x260382d50700111255030400b0035001443d00500340726405050f8a548403207100300380c003001030048030603020783c400704811022210003680c1d101d01079984070100520601d6a44c0c40300b0109441d00a4032810004101406208030b45000b42c851074803200b6969403101500c907201d4032044aa400c19601d89200f80030a040380c0b04000c0c202c80780c2c8074001c0759140c00341c1084030710044d800900d440b8001c59150840180e800043c04d00440f8074a04049450b90340d9801c0507801040c1607400103410103504400c010070081e0403c0c20b144240c010607140100d401d00303108211920740c140c880464011030200442812107000740c3d503140341c403032a8501c2110000c400b40e012940c0c004080e03111043c900c2d06c40c828007080c0c0c007103201091022908c90b0002c010201c07903000025684d10807a104203040c02440b110210034084c4080e80c42d460aa006800390b492310242440050808c50300344038880380c0f940303041034582004085002c0c890403070303000400a01c008480103803028001c6c009456041da00140801c403110b29814040c0007003a290 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 332496600 1250 332495350 332495407
    0x9070e09071b2a080c1305100306060e01050916080f13060f060503120c071a0f120402040506010c0b0406110408100e0601210f020609060d05060a0f061d010203 70
    0x25018161207020b00301d1070341c200041680117007000300d034140c640c050810000d40d24044046025101c5004a22203140b07107410103003149042000100e08080781410950403110141c809010940d19281c12101030015080040009001c40f00030403440f00c0360021307464005100c0481c01d28181c50560b194000c40b84d005121001c8151034103810455850140461200514150011850888981c4c20180c940016000702031404003c0500f525190b040c040550307a80d1201b00d041c1d181e80e45191100c2c0303011404115005c03449541400b000600c654400c03060030a005911550310805134945d0394580015003480a881c5241c0c44051000040010041010841c050311031500051440001414181419016040a1150301c1701c04480703130760460341c00700501100350007400e82c1010482510000790305200c0d07009429405030020609840e08a4944c0c40140200011510408283d0369030020502a00f200d1050b10040b8544801802d00c0e4010461a00b9900358148103807450108251040c1004124546099850 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 332497850 1250 332496600 332496653
    0xc010606110d170121170702040b040605030d031a0418050f0c01050f0d151d09060402010f0503070c020306100303030e0a08040b070302031e0909070e09071b 69
    0x1900050109110345010780ca000494209100501c80c8141d0043c401e00c1108200b08010581711801101200060750740001003032000c90004404082a030030025069105500e8140b41018500d0709105090403200090090b10008002810650040c00c3d0700000040c2da500b10400d100306641e07144550012011020362120300740c0c22909000340340c841da102d22000950312151036948582e070044280c6450101e00c6501c1580d507000300220714042d0a001c06e6217084041f00100c04504410f88810101c0c10b0f803500c0800d248503035284119159075000c2994042c0c04140c246013a041da40f846440219807281d0075040041d140c018540c04285860400c513810613100641c0c58041c82016858080e004140f413080000b46245681d03034941540c907204502c5401c44d003400000c3c200c0100342c002e01c2514040f00d2103500c4640345066059100c40035a00420400e03119402c4480000c00b00c501800340080740d600301802040c0c00c2e54038800240c4034086882880411120000382200020750701301024040001152401b20382c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 332499100 1250 332497850 332497877
    0x81f0812031605030106090510050c150714160209061503090105040b0106231312060f0605180604020313050a0302070302030c060702061c110f0304030e090603100b010201020c010606 80
    0x401c40c0414041c03c00900f000104500c5511070003a0381910011a14a080442440381c280c955120b04c2c481007042d401081d400c070b0036034990030f00c00a103d5003982d00d451220310214540b4030603074810700025800c241a0045004058203003d40c0303091340000090940c0c1561004540141480d80003103980000c0303613446808110410a81c0395005004001a0400c040000c2c440c0740e0605207015020a00a2100000f0840f9004a280c0308040c20080460b001802c0b64840d01d4200280039089608000c0c0c5206d003807a100060300e0400c8900c16141c032044940002d541d031218010400a58005010080806000324161001c10340501400b28903600c40e8004080c403600d144103060030000081c1c0064881c0d42c0c00d0150300d003d0b0302c07458200c0b0b1325080e08018140302e80b040034010a0003840d1140303007180340c4000404c1d21075017192040300840c0158041d0b15940c552410303202c20440100d0040311440e8240e0442c890401c5400c5554104404110b2305000160805201012803821101c41d688544000b5400064820 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 332500350 1250 332499100 332499121
    0xb25050a0317010501020c09090313030309050427030311130905040606170c010503130f03020f01050a0603020a0303260a020414041b110703080d020c0c040c081f081203 74
    0x40082c2c0040d4224611503240c080040e4582103100d06c00c030b000703400110019498a00c01c0c011102c041041c0e100003c00c544d200d0400a10304900350055601580c40c1003d503100d68292540c8400b21882001c600c441039042696044000d1b1030700d03c00ca5a0701300c00a00c0160305011184002401a0508031800112440c15040407170944c0d1041d40600540040c1c001c44240342c00307011030001581c1d1070a003020780e0b990316004d0891080356455200500b4000503440004105a408500303003801d00c2100300203000540710400c03030350211000e5110003940304c22400e104200090040e481c0f00700e0301a42c0746a907200c1032582028050f074404c007181c0e882c10236503000506101c542203d0701000c5d80e00c2d0040d135040108488440301a41d048588440361001d109011b5070b804032620041014502441d0302000243d00c070510018100b01941141a011401d40034144d441c0300503082a20554181d00701c9651403618585862903c186007802070394200d144403c680303d011903000f40403c030190154800350101383c1d40e894100c0800 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 332501600 1250 332500350 332500367
    0x12070305010609240f09021804020f120f070c0f0501020c10060611060c0904020702150a0509040e0303091506030c0a0f0f06140414180f0f01050103090c0b25050a03 72
    0x288134903000c440c3d042c04000711085000781a11340080005a640e01c0b40c0c21170304101c0c02600915503000d400010b8400340f48510034043d01c0308541e005c241e07500c69111082c04180350300e41220314800090a14500402103003640c4480480d95010304001880c04400a019500303100301c1346088401c0944400e0708208081d130118a80741065050005403041e402c01c00080e049a100ea1a03003a40b00700d4010074000159500c20700c113502031905544c01c041d03640a00301c502070700302d40004948a10651800150b21002200030044070b20810000c0045d01e408034030344940382000354000d0100760301841440f440403219140c0c15800c02c0a0130003104a0100705151100a07425408150062020072072022400d01791591600c05840540309140c42070480e070144100400c14205084283c205000c01e20000d0008035150482410f0203201848403860030b07aa200c8006505441c2c40d18001404404100000c108107401d0300041d000842d9020000c8030744078000050105d1204008400b40ca040d00100c03041c01c00c0540080c04d8 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 332502850 1250 332501600 332501651
    0x204090e07240c0204090c05181e010e0f07090f0f1701020406050a0c11130b010f05090321040b071226010e0a090507080c040506030a020f12070305010609 68
    0x2c910111040000d01e16102c044009029603110302d811010051213860f88030150402908103040e4280010350182d25030816158480c030a49105c2401c480f00603001d6119051790145059900f4070b8136013004401203194010441c07020016031441c0810070312082c2850800901003e940400341310b0414002c081490420a03032102036038810082000156000001d4590905250404c280300300150308181c224280350942aa500410b03a8101511202c0c01c0c0c3d00c00c1350300300c40a07a039400c076020080d801034585101e11281c560389a404449100410005c031088069018002d54035142801d65585040409400801d01100e03000301004411038015401004e05120850b80c6030b55522a91034452110048030040c0110600c44403100d00149480c0115001150b42c01d03030101c1114030300c69903075160548458110010750b01c19401c040108406150000c1d812a40a800070306141210148004004400320500c43d145094001c422000011800030310903240201409040442c102c02203c108582c085c03c190320 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 332504100 1250 332502850 332502899
    0xc01060509040f120203120109020403140a03140711030d05040509100b120a020c0708011517030f160b0a060302010e01050c0607050904020403080309070e060d0302030d050a0204090e07 81
    0xc00002c03603681440c008000b90050003c01c81076104c02e1040b0304500c215030030600c011851000014036104140d0041040345d001c0c0001001c2215005181034650f001e103900a00050704409040300c140103184010144503110303c8941c801d014010020a040030904001d83d800b0490102c0c04009508021031120f501040f0340201d000400e0512a01112034064654244440c51410001984060080d41110b1300d900c00d1170101c42c0da1559804003140038000088002407031007102c10b40060012480c81d04d0007041c0703002c0000745042036000b50029005400c40c01c0c1283e40070f410f4200c40c40114020350300f81d40c000d034400900030a080d403c50002419014850100c1c9040207810425055039a6001c15501c1c0c0002c0300d454400e40d10390000b80001d01074010ba41025080d21400003c2c007030481030018072242103400c1c0d030031007142a41d5090108042c03510252000b801507001080711070550380316a40b06d50303809440b80320014109074030344404404a03441c03094440b00700c0c6c1c40480c090000540407020f45000c12070710740 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 332505350 1250 332504100 332504119
    0x5030f06040b040303151d0a1b02030712050f0309010203100e04030e2211121e16170a1a0405010609330810060c1707020409050102030c0c010605 64
    0x81d24404200341c010405000c00d503403080c140d07442d030601a0504000707120047e51161042036a002500c1c9254040e9094070546182c030708070a80140040c4088111a86160041d5007042c4440c0ca4020007007203044941410018100011811414407101541c010312004000503142d02d0035030f40050076400a5080094801084800c100000ba03108a0340c0102c95000d4418044440b49410116041902002108a10340c00c02450425098a580143c0328074041103200034026100d41c07984110301c2d02c0900080200010900004007400e40c150b003074500c940810720307102600096007038034194403a40a0b24545122a00d03134411805180c02d03d0a804240501101c00f0012035140200241c004150741c4031307824910010164141485112900840c0000001484401c0780d40d5243c1004142d000e044070750100e00c03200b46401103022031107452081951a072018441182d07560300c0d8011541a04065000c036031040c0c6031000003000610030b00203107000b0000c1510803511803218011490035075200f504014010704144 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 332506600 1250 332505350 332505353
    0xc0d0b06040323010f020c0f070e010b0f0a020709020d0e0c04050603030d11071b0807230d0f050d081e090703020402130806070801060f05090109090c09051905030f0604 74
    0x8244005112209005030403c80b0b5652101405040348050341d0b0900ca10202d1010700740c45001c1501c0311070300180002c1c2d420f610f447d0501246009428010380b400080103001c4041101c0b80c2100a140c3c041a50045440040d5190000c0c0160b9000d1542040d8140d280d0020120400d41041600c000b520125000d110500d007030408607030f480c00348541d0b002e00541c0f41c10f05c9011490f00c44040701c62041d0002c40c01070b002c0c40800201410742486115001d514410f081e00000c0790fa401641c5c0304042046d9147c0c0c080204068020001d6030303c000d00d81550001c200e0403807030700020381c2000340050400f125150b0080d03d01d8481100d00d440300c0d990308041e10b0420300108002180f00d01194a03026a64115001612483e410222030890b801580000320240b1031041800b04e0942c0005540d4101c0d0000e58410f90b00084545040310540241041d081c0815030318941807244400e070fa004111001e15600c1c0c01400640d40310f002441c020350011a102000094201c103000310b040900450502903c543d0052404c0c0c14603 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 332507850 1250 332506600 332506613
    0x60c05091008150a0f03020906010503100302040c09051e09010501021504080a0c0c060806190e0f0403110d030f0c090303090e0c070606080606130b01090b130e0c0d0b060403 76
    0x18141c00070024000001030002d0b01e014412010240b020344504e082588034000f4800c01140d81c081640b20700b0242000640e15071003035044902c900020015444d00700e1555003400042c00b44000000240130306c0c031700d010503d502c410b5103149050184480101501d400901400f22500c010b801c042e04541000c400c060f0040d8a1110302e9400c103510904c10760b170380e050071841100c07032582c1042d0041c400b0208110000707480d5803140c0414000d01c01142e0b00880c0b0948584501c4078a54944078001c068480301c0c00044014042860065100c0d010f03041c03070007a65401c038607a54180044146601e0201e9030b68080b040d100c142d181701e00d0039000c40c541811a003945c19510081e0041c071036442456480c80851000132401c6044070b041d201500c1d84030788240801c5031280405030715928103c1c0e400b80244a210340480c84582580100505031a0684444407110300b080011003140c0d2100d400c9038002d90305000c1c0003c5001960880c6e40c41100c0c802d51190700d80c40d000d00d900003641d00400701b2900c1114140014000b0a00 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 332509100 1250 332507850 332507869
    0x6021e0c16050f03151305070b0d05011211040b0301110c1609090c0b0c07050301140403120c0503070c0c120f0201090608063012040f050108010b121b070609060c0509 73
    0x1d260b028507003665103400240850604910004101c0c1c02405070000b82c082742e50b8050a610741717040006110507038035200c4d50034001050b10005441c8081035041e4584509040e40036489603940540042003c06405103400c040b6880b0070304000e0194803000107030310315010400d42e10000c0e05400304207108801d95500d507800e84121038041c0321100500094032004215082101800401001c1d000740601d052085002034554012541900450101c820403880f203209440b4008401d0000d8070340600315110610200c07004c850300501103411107004000450280e03080f90390940d8441c071501c10394558840794800103050fa0349a84c006000c0c00150340c148081a52195a89103544034200d5800d1106071046520001106c0301c0701410206000d516400c400d1903c030100180103549a100d02d07906505d5484004480c41d1109100b0140401400c0c060a0300744240e00c0c4e1240d402020200c1c0c4141c0d003611048840c0003d42c002c0100301c403401e9580e09254200040d40c02865151074281c28980c3c203044c0410003103001c110 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 332510350 1250 332509100 332509123
    0xf040209060702090919030305100b070203060c0a1404030f120f08060f01050d0e06150607020307030602030c072018040b0412021905011e02030606040306021e0c16050f03 75
    0x20b640c0400a608950104500c6c1220300f09000d001110121070700b0b0107002403109030ba0b0b01071002c0c0c410101180000d211001c980500d54007400501d5265501c08018001da00402e104004104182e00c2141032404a41c020b000954050380d0540c0300c40702203140c101040c040b0003646006118514684402582c0c0203032910750310080645050341e07562080001203805114216100c80c03d1450020340080303030200040c2d42d0384110041c56064140030048410011075001c0c1c0171000354107038002141400000c8030390300030350b13001440b00d5020b900f011003036500c07440d0800940b407607010100840c210500661521443c0c4d1420382d810340a04500710b00701611f5031500100010006420300c2e410181041505100f04009a940c032104205c03440c072100c10789400c0c3c0c06400f0124490071015001001a51102e803070340300b101d01843d0000c1c044ea15003490b41e5110f0001c3e411080e28280c01080c0090040001c030031082c000d0060b4504840a010007a689001004140032640c003d10701401e510031409415881c0000d0051215 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 332511600 1250 332510350 332510359
    0x40b04080105060a050a0e06041104140a0504051501180f0b070606050d1e11090c31051014031008060a0b010f120605060a020a0506010806070e0405190e0c0f040209060702 75
    0x52303859a01090140206504507540120009000120500b00d014145c128200861711074201565030800c02094034416107242c2d40003065041017103032540c000c4c0608225044a01c2130090220b5070b4006403030807110550310000560600069080c10842e80e8407030040542000c8407444516226512107107142007080410915040b082411041440a81c2c0c0340c0425510008010403110729040c104a07600c1d8000c1130740c41c0300c00d000340c1c0408002c90340b0741c50344d95500c010105c880da2401da01c0d020401100318810601d00090191300841c4000d80454500214425404640b80303440c52841d1101c010315100c00100103c07400d901d014044000c60380e0140c0701e810b2a00c82da240c0b03595180d03d500c81c4480205072580c04164000000910507101540200303122044074007ca0a81d400c1c2d03a40c07080c11541b02c5404482c04400661134400820051916901140d00115141c1841c000c00b44a01015002c0707550310407a43c1c1c2c86030f0200c888182c540ca055501c20f007a90400307403025810109140c0101d0341c18080e02e00300a208 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 332512850 1250 332511600 332511629
    0x60518070f0f0909110904080a030e07030b0c030c0d1107030e0d02090f100b04030501140708090619020405061c06080d080105040e0c0303030403050310170a0b100b040b04080105060a050a 82
    0xb4008540f0f544008880000c01041c1b070760400f0315000119900c80c0034140302090400304001000900420b85800702c0c0d400011074034440d0b4401c0208000c40c0e01c002d0854122038418055140400d03014800c2d5a0541510400d40e030343da803028240502014600e840e100d00c5004860289401a11041001e0b5041034800405415a0b210105180d1141e17000e50800a20903101140020070322505405c24691710f801040090b50980701c100b01210820310440b1240c0080d880500130811720320a0100b40b110804e00c40d5001070416403188000750703d660001040d60104d00c200340c0c400c0400c86c29441080010900c03d0000e0002101d042d502a00c201e40512940e4031456480301c13882480d503014002240007600040a0384c0d50391805190142c000e13001500c1c1e40844451100ccc1c041440c0082c44840551f00c3d8030a0010b01000340039070f0701c00c0c50165004201682291400f1000101c4111050262003d0460800740302d450381e0814610f41d003100c6008140c02c0c82201210001c1049440316441c41c000d0b5004000600503 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 332514100 1250 332512850 332512853
    0x4031e051b0a06241208190e100e030a0813090501030c0e0f0106050f030603150c070515101701150b0a17060303160f060518070f0f0909 60
    0xa00c0e004a038060309888104403000050040d01141a0912501c605010840c0e031100310041c040d03152100303240b2104030841081c18065003001101d05006603116115040c034100c003114001c0c100d0428654060302090149001c0500307483d11021203c004996803070801c40c0c501001000907619051501d003d004800001381a0084a41700d903034040181051500601c083e580d2460308040d500e89512810b1080c01d0180c000c2449071580b198658100c4500e659034900780024448803144a03400905005d07854440c0c02d2a514405030b41c1020305100b01850b01d0500d888a925042031410403111003600a40200380c1c1d01001003030420f142440d815282c8400081c0031a04d203214455004008005c100c44014150700d80002da00702012000780303903010702a65208100b01120715882005042692002c0e41070b0020301008056060b0288001401c0340070f11490811141d440d1030341012035001780c07242c5021a20b050b0b040024000100035038001002c103420703e0741a03170345130214242e0025081d001e081300d42ca0300d5107841c40 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 332515350 1250 332514100 332514107
    0x30c01050901091505090111010c020615030f07060e0406080c10030e030f0d09031b0c0b0c030405060c060103030f0503040c0308031504020a080a1a09040807030309050f010519020304031e 82
    0x3e0140442a4050020440d9803034083e1494203c1c2c1e12207400074200001e50303813100c481801703000352202c0c042d0010078113921003840400c001c0f4800801785400d445052010800014108144002440e181c5c4030800704620b5041440240c0307207103030017181c0325a01100c0ca0080070b41703601c11844c22249003854009900c0050700042c3d81548a81020440845000b00c1c00c62541c407003a0740b05581052003a1500420440d5008541107100490040030303180e0728103541c0c10070843d00180014010406000f041d285082d03110000503615421800c0c074410a90b000f200103000300b40d048401c040050101e800c090b41103203040c0e40c0d00c01c50f003141800003c160b540003002265040d042440110b2500400070015034807410340c200010011503044a2043e0800d0500e00340009110340580b91b00600003003d414044559a10384540d5120391041074100c04159581d4942d002044043c041c0207140d516003000490715003407050420040e804a90700e0f046072603104000f40030000b60003141e95000c2d40c100c000c1a0b44803c2201c80250b = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 332516600 1250 332515350 332515367
    0x512060103090c080d1e122a03021e0408100911060c0a0501050a0c02030d0e0a21030506010e01080103060903020c030f031b0c060715020918010608070c02030c01050901 74
    0x40c807100f80d803400071440c460301140c0402c00b009580c0e5060886041b04400d092018143c04440c03010804604203101c1d045030079000b01c41016810408070441030b030078192540c0c5603500c481d032603400251302049401030007a004000301d00c410205003c940c100b43c18099040d031a40f610400ca001074030382d41d02e0031104002503458000740341040208040e40310303240b03e4421901c034901e103001100c40b9440c2900084052216100d00c03501005660300645c18402c02805410084c5014001c10b000c5100304d50311440062005240038294810640c8c8549030002816006816140054901814003c60b25201d000c0790b64043d08140c11642c0091000c00c2441050034103a08200700d8a10491b0107000c0c501c800628000000b0041040c011080d840c51900d50000300a41d031504090f45242e41c1c0820b04100311800f20b21581c020701000d400c240b00051419900c40006000c540310540303056080807454004000c00c6801201c2d181d800107250900124009a6900094480301341512903818040041040062a44900c00c1c0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 332517850 1250 332516600 332516603
    0x20304020901210f030519020105070816120629040e0f040206071203021803150403031d07060207140906180c0c0601090e0715050a0f030b03030706050a0e03040303051206010309 78
    0x440c00088580e0400416a1f0f10190b21107a41038207080003066114414422240b18500990342c0f00d6054440e070241c2c5200d4072804440c00100100c9241241500300c01d8403071400240112092252158100d0002d48801070768592544010f81050000304020031107044420741c4440d03080c0003120030780da0b40d200061141c00f41560151900003401c0d82420040e4260740109684010300a24060100540741050f40c0c548191220901e45032407103011400181c02500940200840c011f01010850385500e8058900581544501c5c0142e100843c200b0503114030b15141444510291074143c12441d021010540900020180070882c11910b40040e0320401814196501059018152449542d45501c1e01c406850061000c4900f40078884000a5031001040301c21203015642d1109802c059164400361484021001e0b218189900c41000c140c0d141d6040c002021a10b100f1580002c4a05105103524200c40500c00c00c00015170041009001281d005030030b8642549a444103000940d44007001280078040785e500 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 332519100 1250 332517850 332517863
    0x3092403070305010513061419030b0415050c040b0a12020421050c030c03070e041a040615050102010e0c0609121e01290105030417040b04061202030402090121 70
    0x5102940340c0c0340d0011130481d00c003201e6625040c448541c001080705e110b0b100d10411092040c1001ca2182800b1310703074507048411040c0c0010065920f4440c0c00707030201c04903001c031100c0d001010b0500c05804136214007500004001081400c3c541400d407600ca007807144c48050400d2000d0b480c440c2c510303420750b50111000381c0080c3c240b000241d0062420b04030700382f48014048a041c0213a10805055003400104075010316401401048036624100b5611042070014209442c440b210208405640480c011210f00441c821500000c0354000c0800701d518181a5402076070459040c000c05003a0030500048640c09100111103081c2da8101090001e91200a103ca5400c843c1c001e220119019064144418111503555002400b0081111304150108074000103144404030074900c65800300e5202d68051030340548030f5a5404015a580c42c030142268106501c40100300c600010240146580000300e001d000e4030b0240d0940c11420113a002400500b014092603500000101d214000230341c846041c144034076000364 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 332520350 1250 332519100 332519107
    0x5010f050d0507090f0c12020a09031e0209041202010506010c022d03070b091009030203060c031f17161802030c04031407140f01140c0102120f0703050c0c030924 71
    0x3c4d071743d101821009030341c0f0000c68102d00c0b1b03c1d526a5030900807500c0e04403280d502e103901c07541550344110f01e240003418081d140c000d1458884005031140300c07400380a280034520900000901c40002429607900820a60410101c490b404c030041c1c40300c0000c400c20b004800086c081d0310382a2031404848045422200d1350600c16508005800e1100301c0c003c100c1d05205480c5800102401d10382038a00207950711009416034810340010382420790f13400c09075402c0798a0325412040d10085e62214280143d0540012020400f10100e00300c0c4604100075100350aa41003440d0010907290060107244078451160b1444129000070026000701ca244003100c000e994031441410038407030980480c5036030360440d00485214401e14031030b50000340f41c00855040132882c140d41d10322240070b850202201a0b08061101c070000d64080c84045000c51070310484901c965000700c143d500c4c40c5000e29000303080d80c034040d041c00000c1c402000320304030804000c42200c15403441902e41100e2455008004c2c400f484c54030f40b00c28401c11010 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 332521600 1250 332520350 332520371
    0xe0f0310050108011b0c031d120c1f020613031809050108010c110613060b0402160219081c02070f0e0403020c011d010c112e0305010f050d050709 64
    0x141d000070b040c0c40c00b8800030850250315020b0352000c80c60703040f00140070031140000400081c5c429020746012003407001c465101801c0c0b8001003002070303000c5840341034946c21251a01c0c0807414850740400d82c1500c82a0300442c01001544065101c0c400075002c0000c2c0c490b0140c1910a06000300e080c0c224070346500030607000c069902c41c0c40d00000c01080c06900025403c2c09802c1001c1d038400c03032802007040c104802804907520f0b06000d0b030405084030705003190711035203401040700705548502c043d1410745080c1444441c0154288100010440ea1440d01040749c0d42c0410144080480001e143c68071941c45c000d86043e4880c446020303032070070260760310010780f0a01404001c02c1081404503840e0056202c4c0d000c482a4030178501c01910020a44801008a0918444c54200d00d600ca4907618100b1409a00c1d00b00d83ca001460106102941422111009550b14654041c4010110580300c185102602d020030041d414011800b2203025248100743c41025101c0102003030042c180180001030424071000c100030002c4 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 332522850 1250 332521600 332521633
    0x309030d09030308070f090608060102071707080114010b07031d03010606091502070b16020414040303050f010b030f010b0a050d14010f0b03060d140f03040902120114010c030e0f03 79
    0xb800304400284940011520040c0501200005040340d505e40780c40c441d0501500b1126180020300c80d50440c0300b12100014500c2d28480030200ca01c7c0c1c1240034080b171030b00307160259081d110982c4111089907060001088428900c00070b8502c0b0380d40c103260628650310a681210b6078907000850195043d46003960000b07019070048142c1003190350b400071050708042100e605907121078607442112008841000514100d16104107100720891004200094051480c6160a0440d8080790100c3c0425500c1c07080c007055400c40341e4642d0050420403403641c40c41c50144c41e400440d110600c42d40c00c100102040b10a403040c040c0c004c5ea1214030181c54104400905010041c0c4078000038802c0c120021103100000c40c036020410110b900c5840082c0050540f807074155500c2225018005074201c0381d000781800d840b61008140010001400c00c16009a1074009104907040c0025040e80306028407400401140300a90b042000024510303050704020700503424190100b500c0154001081e5818060200a42c801004 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 332524100 1250 332522850 332522867
    0x1c0f32090d08032802070c05101403010801151e030210030b09070c020108340903080301170c0901031e0602090607030809070602120f0c150c07350c0309030d 69
    0x8440c007020442041022800100e124106d0044c1108006540902403803c2801039100d03803000c01c0c41d190300e880200c4800009250001c2c0c1110109075114410990042c42c407015000142c0440301201d1214400d8911151030240d8501c0000d01801801e0a028260381c000c0c1d0119900306d42c042e10f0300c880f031f24041e0030045c5101041d000890200d0300c81804a400d980d0001c401382e005201551b1400050314040500481205c04102600c1c20000c070010b02200043d04c1801840c020308050400d2141841d07521304860a00c0500d49485010f000084010401f05a030281b00d904a00350a020044a011507070504001900c144032802d03402c0b20002075030700d0801d07600c8110f680c03058130680b0039510115150390040781ca07503e030410303e0f10301309000303015030079070340080c0d100400f01c00c40082c003100d003800c210b08181c1c0c1548034200d075244000c5078003148030420702003000c82c0405103c0740e90b00c10780e00101c124168a1900d1480c0584070624a0340454040501c440c10412030320850710003011620004d900c018000c04548 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 332525350 1250 332524100 332524141
    0x906030302030d11040f0303140904090b09060a1a010810050a080d081806040206030c0705011104030203010f0e1b040b04092f010c1101021c0f32090d0803 68
    0xd1410103881c000608944c10307101907030000c0025141c25441c41c1c90480300b60f01e09400480301c41c007080100903401c1c0c1e50381c4501c00485201e981845490310b082d2101c9420f1800c01040910181e0622007140c10301c14081c1b060307a81c0c01c0c400f401c1034550b940310f400620b0940c0100307410480e00020b900c070022034200c40001e13100d80100450f0740c42e0031007a42e03050700700c2c880b00300101c042e201c00d0b0f03014001003801403801401440e0300911040800341032004540742e0b43d083d20560b5040c0090690000750500950400307025188411062202c00c1c4a9503415285503035035841804524000300e4150701c0702c0c03102507840b0340015400c020010400d0040c03c810342400032005c0c0c2213804450040241080d025144144032065109060050711007050680b03054950107022480401224114010001c2c0e05042e0381184140c00711404403945c9100c0904001c050103488440c0a10042c901c00250201444941000d6039142040303a9a00c43c04584440307480000c900f010b511300000502c07541c00801044198120b80030101c2410 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 332526600 1250 332525350 332525377
    0x303180c04050435030703180b01180e0115030210030e010f05060307061d01031d010e10060501090b1b03090a031b0902160609051f0504021207060c0615090603030203 73
    0x490604c50980d000825949400c00d600c0003d0000850160107944508010300c07142001c443d450440f80c0c5c0c1d0a04001c02604045080c203240d0086070118442d5100e001c90000e0030301d00070048002c501c1410300a5640038403000b44280030291030003035968800d03000401001900e070001d10288036940740c4440030303000c2264441e00034890464001500c03403058851412403000b4180494904a001d401140a07240344442000074015880e6803280c00b0109100c0c5018a80111000d4140031031142c820805480c0ba69010394108420810203000403107126040702c691034941c400b40418428900c18460541c000c414000ea03004100d09030010521120f0152400c80c1c4c0d404c04080c10301c16440f50208400ca01409042040303040341d400c040070000b41147d0215403954022402ca070100e0b003602401d400c10038204495001e500780c6034024001141013000340c02e0088600c035405000740310b00701040100391080780c0d44094951390300d483ca0007803030321030300010100a090501d034280300103600c80c10065074a034000d01d03559044 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 332527850 1250 332526600 332526653
    0xc07050f0406030803010614070b09010203150f0f0607060912050c06092a030106030c0b0c0c040e060402061e030403051c0e0717030f0c0706120e0303180c040504 71
    0x1d1034a8400d0400340c80c0e215050f18113607401d000f0211072190b20500b0250015030200000c1c008603c40c6299644100070007000565030346000c015030b2042620070b030446800743e49104944c034003c0e036403040a400181070a0f00c4d62911003595040c000c010b42005580900000b000f20000790356550300030024404c102d1110101c1e462030300e42010080c0d1351a12224081c42106100780129181d16500c1ca1683c3c0218004001244042c0c0b00e80350008500301c60307030144101c00380009002d8003010307090000542c11441110100250300810400d40d858082c0103000a10030300c00081d4049001d040303181c01070410303000511516107078640352601410541c400d034040904a01d0b0010794250f52486401132104000ba00300103401d034146007407403140c4c85c90300c181d02103041030105100040704201440302800c4102c218070000d000b402e1810740b0150407850040095032541c1d042c00d0701383e03100300c0e0300200f22500840e480c814501c0392103400c600181040f98009039507a129042000b40000c2c4642c00b4500314018020780800d008 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 332529100 1250 332527850 332527879
    0x60507080c09011707260106170603060f091204080c01080105041e050a0617031b0307030c02060306180406050115090e011406190908160305031e0f0c0705 68
    0xc2c000e902ca554005008002000c107040040031000760071070b0541c2061248011071a0003c14074520b242140310601c68031038010805e031035000c40713000c0440c03080c141410b042d0306011000c203444030310050807440200c104d00045960031074100702c003007c00c140252165444541b52900703940c40c0e0210301c4999001401403000030900349000d10030020b050f12200603556440000804400c0a0300c402401e0740d0070f55607528000500003020303e0803100300300c45100107940d51700115140c8041a648659000003c2c2e4010f002c12b200080d04003441400e500e0b011540140c0701da61301030020704801e9a09801840e85440803044c001000704a03003045042e9075400b16403a541c1040b0b00300c2110300c880c842c840c4d15020b60a01004205418045401441c401000f0b00310714542101040700140c07101034069410005403c03000300304052003085c000312030541980c0e08010205403854544580e24000c05c1003000115901380c080c92502c540001c101c2e01440354406013680c8a0408941c51034441c00305114460180034000c07201074 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 332530350 1250 332529100 332529121
    0xc030b101d0105100309060b15030a060603050105011b0f0c0b070b0c0a050913090203031b06010906120602090414010902130902030708010e0408070507151b0b0c0a180306050708 78
    0x24103903040602a21302101e03c800084010b048000401d40700c00755543d08420b8542c0f20140e11480380e815100b800e0f9501c1c00d021030f01c0d008030b60a0f9031001c410149000014007283c0c1c1d00400309584044140102e07415600b441c10224a9028901c0e002845240b850341300041002c0308201800c0c6080c00341c5401103040c2d03507020803440d19110b22192074000603c10001c8107814640850071039059500e044000407080749581c0402d01c7e5038000e800c40310b045071102a0003a007900040290601421104c07000b400030628207140c613495050f42000080020790081a00d0031a5242c0d5840150214500c90499226580d1440070100943c030060a0304000041240c1c0807950b000a40201c2e40507840135521000260700e801c0c0d0740850030750040e00c111000fa40421041c3e020600400c5624041d09001c1420323691089440800b8003100f1503c10f0118142c450740f8827000200d08441000c5902c00c8150500c01c0e5903a40d9141c0440f0f29003840180605100d203003840c04400e1100561086100780c0c00c84d151000381e40c541c034110030b = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 332531600 1250 332530350 332530409
    0x151b030b010e0301063c06030219020d020c010302071104051005030706030908030103080304020607121718070618050301090f03031805120a0e03010504050109050c12190c030b10 78
    0x221b0307003002424502c180400341c001981ea18205511003552100c2600e000001c0340301c005600150000307401040e0103000341ea0490318104038039000c0c0001c0055010250303019403516400700306130f81803550200b80780042c400036003180314542e01c001308208000d15040b0b12145200c08107004003402031103514008608540207105010b070301c6030040742c11390840e841c507071322812294002407040b600544144500c03000120440c100a200540607101e182500c40d10144118100c04010f1a44103001c0501c098070051100100c1e10030181c035802c1c50124040012201c000d006500240d0007143c1540c030700321061082c0a4641d030b042c0041403083ea018090070034500c4826000e001031071030180c6650004d150402c83c0c411400014040303071030542843c3c600c01d0000c8000a0859804940641d100c0c1d444074503402c1040824801d115600313104650884040c085900c03840c1c0e17124443c1c20728401510b51b402c814010b0003001402130004660100700c81e049450074a1a01c046001c1c10f20961a2500c002680c440b00901c286584 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 332532850 1250 332531600 332531609
    0x801090c031107140a020604030b04021905101d0a0b0d0509061006050a0e0901090914030f16050304033521042409020112020304050a151b030b010e030106 68
    0x580f81040786a8440783c5280c000700e07601140b5807080405000042e01c0e804083c0000f14002c40c000d20851403d4018031040d03d08505034903980c1149020240070965450a4042e502c070030503d01a0004d2084504101c440980d80d01d8440e40702400c0c172800280c101c2100e004051b0010140414041616410707001c80d0303110b50903640e94580382c13a14001440214030038005414103500d036162007480382e1180c10100790300650a03007241e002503440e410f90768248440b80d21030080c150f07001001036241c55210140003002c0e001c0d00c0c142d908032900e018540c03410300c181041617902a5800038603d072201c00054583c4503101907030b9400407081d0000c1c10984110105484113440030b008844540000d06481e002812078000070080c0101c503003c0c80d442d5070303000501d40c101c0e090600c9454800005800c911900000d00102c144142c4c03030104500400801000920101740412215840f00c141c07030400707109036651005064072041c034418120b01c044c843d940755941608402c400712000e807900c41c0d1401150003131509a0382036001c0c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 332534100 1250 332532850 332532881
    0x9051608030f0f0d2c070302090a020a020708010e030306010807080129070c09022710030b012105061203270424090b1c0f02010507020d030801090c03 66
    0x14881c2c00980038000303090340a0229031891800c0d945519030800c551007030408080c0280310580c102201803200603404444464007004080c50303442c41c1e0014080700c01c020300ba41c000503004503000318150b0080081c42c0103403c02d078000b409148200c0300c400f0360300e41003110028000b401c00710116000070302a0b44214145c5008101d0788882900724840b80c05001190021f40380c04407002c11400010640c40980b010141c1a9540050307a24000740406506891a0001e452040091221040c160b80c1d10007540001f413540324103000c51040f51350001a40d102d09943c0e00101e0703000c1c0321540350142c0181c551005202d41c40490340c001066460080311540d03030042d0845502d2204460000c03840c1694aa070040703002c000300070f0010032a03680c200040306426195010303610402250460900a1601038010b1000d0140269002481c481245180119241c011503029000e4040c1a41c82e00659111300101c3d001980c0280095050700e43e1881c0052503100b09100701c1017024a0240705683d0b451180c010100550420315 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 332535350 1250 332534100 332534107
    0xe0610090e0f0402370807082517010b030601060c030f230a1106070e010f030b01030b0a030302030a02010c020706020705120a060507050d0605060307090909020a0503100905160803 79
    0x112550200c0001500c140d038443c0c1c151005c041101030010b013288443e0b41c1c0c080a02000c001d41a031203a241320b00e0ba04403400c59045a00f01740958032000403400c0d9440126100d01c00c6844586800c0000d10b40b10750400c4080c0b224201000d440c9050540048101320010740c11104903aa807080c0890310303101d02203401800208a0f98401c034010340b051030780044d2030903444100c0140300c4015003109030310342c40522858007144a94101c1540140b0600032207070b001c91079040c400c0d1415040030008100e4001020500281992260f160507a6486940a0099841c000d003807088455101d0401071740d00c1d0840600c2c0001907080000c0740e0f044601c003081440484801790000e1082505200130440a0305c8064107100c024807a87d48038101041660007070500031460360701c5880d03848810500000c19100742d81c10980c01030b00c040050202e02948601604112910740c000041c01801a10016402d108075038000c6506201c0c2c2c1c4884100c01c4410303071028181520038411560f000c140403076142c074030142611500420b41c00070b0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 332536600 1250 332535350 332535361
    0x6052503020c0306130b06091006050a030e0a0b0103110109140103020c150109090b010b03010f05040c0509030f01020409061409061c05070e040b01060302030f06040c02030903070e0610090e 83
    0x9808160061203401075425070421000828036003003086614040d00003d40c0850428852a00f001ba50402c0c0c3c00e8940c14610300d070410b84c00603041c400340300f02c00800c480040c0042c002407196020b0342808880c1c0b0f0661b8640c0303002d804d1140b0041006c8c041902c04c0c2c00c0c0c0141e40f46c0958041c1107282c0c00c9511403100051a00141801540250805050a001c6005140400788141c1084124a0107000171400000f907401403402d011811481c147c010084050040006000740a40c03040b2480c120ba80840c0d002c40d1041070041d04541034003440b85503940511600b088003545100640103841564100e0504100701551080d0311409080c004c402950030418400104407030b4104103014560009600c1104840922140d89071032504207950700201c40080c0c1d102c03c1c003040021142c0c420380100160300d015070450400710b05040441d0405400036105580e02c0d05101d0302d05000340701391940e40b00020152000140d0384e0504642e00e8804483d17280c800c1d00007480744000c980c00380b50100c054440b003071685101541c0c0c5 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 332537850 1250 332536600 332536657
    0x8070c050709151d16050a1b08192001090206070b1e090c09150f010e01210504060b010c03020d0c0c0b03090f1e0d080c040801020304080a090605 64
    0xc824031208074000f01002184200070001080040e4000180903280c520f0715444000d50804402030074400c01038100552032425601c108040c040c080482080012030381d6034a4010b40a00c140210840702c0402c41e0b4030301104980001c0d20761280030f458080c0320406002144218200d50801200a61050041c070818010588800460340d0080c0b902c240d2101e03400303110400e0345c0c5514003110211b041c1c1e813200780080250b003822050b8a403c8843c020070218010b607240006421b039000d50b02d0007810402c0e6528118060303072045040d4081029142c44101c0ca2805404c0c8940180c031040310103403a05800e0100c40c00c200d51081ca6000d008079010b030f020f40540760458408803011241c45038182c0e0002421700b800329018160000950195841c10f00910300851885619400c1c1080100243c10302d40f0100142c0000c18004661312985c001d103442c0480141d40d407201940d4850140c1c8d0012003442d803008c400c000400c030aa40c014122000151601e500031980c800741254240300d0302c204102c4000d4050f050035441200c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 332539100 1250 332537850 332537861
    0x11b0f09171506030307051509010f0209180a1b0c1b1512020f0310170601030c0621110c100606020a020d0203011e0b100801050d0308040302150705030708070c050709 73
    0x24000e045d01d1900c01c680c1c45551504040703200002d00240900c0521088400900c6440180005440290705243d4108001110404c0c0710000d0b01c3d9500320303440001e003051a2a480013074806400c4503200d20510175070200401940b47d4560444104540304900103104030040407142c12200c582c1001c0000101040741282e040d800315940e03414040e0288403404640028002071441258011220090a0300d800c80c059100e03200c02180c49000d8003c100140046400300c28a6001e030307142418401b80c610501c00d0030701d1207421004081401c0794a8800441054154200141407400016040754000802c1099010844d0800d10030007015a10044050005044c202c8014100600040000400118042e1803074161030380141c0c140b10b4543c7d5203000100e00d1415080545440c20240f0f04100550706200c08603040103c01c4201906000d402030001d000c00d8400c06c8804551541094003454a003494032001d041d41d00306a43c136201094400e40003409103440b54010948490304640140011450000b60000610 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 332540350 1250 332539100 332539111
    0x608032a0703050d0e0a05040b0904110d0c08100509061e060105071212060801090305070609080405060c0f0105010e1e09120a020f15010b120702011b0f091715 70
    0x3507890020104400388000f8544200ca5100d03130442c04041410000c039040240c2000b0721552070b001e044040c2c0d8807191101c43d071283c5d100798146040c052110008181c0300c006e440080441064400201d000d42001c19140c0710540d1000051100d92030700c10704107890701c00c2110350702c400c00b00d600c02c0601c6114400485a400800c1810060b2900007241c84243c1c0e0758003c082c01c1404078030341996103501c0c841b440c42920000c2046100812480d49550350040c10b03881080c001402070740e154100f03003042c804813008840060100070520340d86d40403042c2046859180b22040c40c0e40652034240001807400c1c181c0a00381c818890b648210107a1601038801d101a4403016126480074480c102103440006400402454408266002084002c564a12191401000400c0d40342c240b1214401000081c030480241d170174800e041039421009580b00b080c01c90050119042040a01c08081e500040d002e8205840f4200c540c5203030348401e043c035110003041a6440018046502e15444058282400000400d0958111 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 332541600 1250 332540350 332540353
    0xc15130f0f0605040b07170c0d02030c0c0601080a0c1d0a02070501150611011a011e0c0813091401080606100315090c02070f03080405040906230a0608032a 68
    0x1101d0944491086800441d011521000780c1c41c24024542e03042035018205080c138030001080c0d850070010702c3d6551b0080404482d40c50360080302140c005e0300312005071841c040c003410032514690303550040786556007682d580a17159004504000702e0050140b81030901100d111f40324808494448407240030080d400080143c0d0030355603d01d490140e000078000a03100070305150752030600380c100980d510303421030740c0c038500c5420b0070f81c01c40c848034141d66000140b070220088c0c1101b149494810052054803417910b4440000c3c40391500080405050520f2800c400680f0a49181000b03068000203034032001190038041c00700264004000185140741c013a0310701400b51094500403411600d54000a0074112094010422592704e605a80c0101d55040203085d0060441c5421404c41e2841c6840300101441280100f5001e281c5131401c030010b06c20b05801c00c0c410907003017030180110000c40c00d4461080b08016a003004149043c0b84000075000000010384002e8581d40012100ca510704620846141c00180360030a0305 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 332542850 1250 332541600 332541623
    0x307031b080601020d0206040b060111101b0f02210d020403080f030a0b0a06050415031410080601060e15090301091a010306050708091515060c030c15130f 68
    0x8400105062110200c50307150a2140d040140002e428014004515811581b2030410800821901d82103981c2054007030910342103c1d50007a07902d50a200180780c00b501480d041407545014886078081d030300089440c07030340d0300d00400084000072030303c0d6030505550a00032650380441d448aa03207040c000b4400e500e5404030052902d56240d0703030b80c106a04426010019004040b0030444507218601480004910480361824220306000c13024203180514028404809030000c0402c0d84280640c1c460364004051010029042c07030040e102241d105070600404648bc0244800001d15a005085030340c404a4002c1c4034800c156030580d004d080c1600001501541503403156049000310b8012401c03c1403483c020303110a01e056045061038020b8036400780881d0100012801003001905010403e00b1909501c0c03001c00c0515240d017045081d107155110174656110500003502204650b0020003040c0740c8001c0030580e12150700a007460002c03d00b0449680c1c020007090040400010808440361030f80d42d00c1160170820 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 332544100 1250 332542850 332542871
    0x60b030f1503160e0108030403081b150c1b0607020706050d02070b0403081501140a080601090f0902040f05100203090112061a030103060506121905100f02030613060303090b030703 79
    0x20b00f8045000110f108070940100344007003120050f42e03d0152841c40000c603c1d09185a030f40503014410713100c2c80030050000400b4248404410700180c0c0320004104003046890401c44550309076640042e0381e09060040085205800910204229210f110341e600034040341031800c44181c800380d10000442d09126420444a40000c1507a412070340600e0180e40c40b000c091900300220400740405000c2181032241d4204031940005000c4104c41e0b4921091920f03e009844200040c1c85000c8542c01811012500000101e00e00701203601420480d5980384c805003101c2d948406101e42d443c4c0990307020005030410040d01d131180d40a980d0f00c0c440302051400c0010304035910030300c0c260324011140d0124003101c4000010010710101f4042c00e0b0b08104100c0302c030080c0303501c80740c00980d9807024800d250580b0907c44c4410313006e0290900030110742c80c60700e0f401401030001c00c0021703800070740c01255014417030785400c041c030352924046219a5060ba5815240d10360501d050a100b4003054000602840816845101255 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 332545350 1250 332544100 332544103
    0x80603210d020c0708210a1110050403020607170606040302092203091d2502010603020d0503031b07120305190f151d1302041104150210060b030f1503 66
    0xf00076441001400040d0b05045407142408a03000b480c880880070305040c540e00c000321104171403500581e800d0000f00a0b002070741c42800c0914050303c2402c013034500f900304028150080b545a03ca0740b05c540c3e078001d0103a0941301c503400c424000e44100d40c101e0b009010520050811011060304084c00e461180b01000b044144241000f4089104400044000303d04001d0401409440d080b0404550a903011a02c0c1c0b51a46881789403104c915100003040396840c50f08458001c0d4041c02c003654001c0c189501d050120700344542c0e80c2e80181c44d0041d050b00d00951070354021410f102500e07000c80d4460580c4214840b01e502c210041c0c400074028040000f20b0514507a0300c04554418800c1442d0400303800300715103040c480c41110541d4903500150b641c0080441a403000500102010b81c001c010b600202e90684240c008507000b440c0840d120720701d10400240200e03804920b1907284600c91a17550845c0c50000e91404090f040e81c013075100700f52900f402480440e14007160980103a40c049581502050f541c0e140e500001d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 332546600 1250 332545350 332545357
    0x5060405031333090f06030203090c0909030f1810020a0506060103020406090512031210140103090305030a1e1514180403050a0e040f0b03010b01080603210d02 70
    0x1116194000110341c1d00390760320700b0000c50080030340a1599850f51818601c030f00e03e9403180f030b000c4080c40070904940122540111070741c101411050f4020010141c903060054000c2d401a20200030b103104100d0807004510b0412183c520950511002c0d604082015211400d980c00c42c10078040320054800d00f04000b5180d900c100080045036600404007662142022070518001030001410140100424400c15070030940c034000311581505c0076030f80c10041c3c0340c0e03490444c06080c110b501206040400c1c0040444016680415031b01160318040562400c10010750032141d0001004010070828000502c683c80719502c50b81c2080c401500600f9182c1c80b100070141181d10000c0d86185038013011074148107082c0000e0300581302c1c40050303d00c00b0f407485404280c20400311000f0002410410b0004012603c81d1062540e900c00b0440071348280054610300c003403c03028001d0004042c0c040d61900a9011003588580102070007844d02030040e01014002041c1003102c07089080c81d442019004101c0120980c1c81440103 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 332547850 1250 332546600 332546603
    0x304081f2007110915010c0507120c080f071a07060902041b02070626070513080601030605070c0b0408030c13140907050a02030d0b010918061e030309090504020409050604 75
    0x2a55542d03026150185207002000c50b5280690f03e01400c0080083d4101000c10103054242455a040c4941e0b18149241c18015001189081c0204050b141001122011032096912200a41d2410300c4060102d80d92401684646224071115507490440812030300001c1c000c9074010440880c0c1c00103260045800d86540702c01c0c3c501504414650f0180d9070394140000406040c952506000e0040c140c0c0016581c0f5a03070f0712801c0310503074502012400403401242181d40715012045c0142c40181d4404c4070a844071b000344030585405d800d05001408940c865211940746942c4000000740d5510785403540b06454000401c82a22014100120400c041640c2c1982c4000d0070b00008203035164421a060015015001e040c2070180b090901c1181d007099000700540b022080440c0e000a1140100e500403038682006c0e51109042a40c5c041030329403110350b20f804c510706172404d604d00c0c210402240700d050a0404564400500040c1d5102c0040c07051403072507004960064001000480c01e804152681410014107990 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 332549100 1250 332547850 332547911
    0x1090b150a0804290f060a0e0106080f130203031c0b0d050a0c05220515040c081f0b040e0c0403080406020706020d02010515010503091e010c110304081f 67
    0x1c0000700310b4400d2a9070300c550140403803040c1d8408140350401e207002d0081c117600e401e110410006403181d03c4950402e8024900b00c02074a14030b50b51000e0140c40d28a05541c1d400500c02c9203400600ca03003007206403c5000d59400341c010741c94003100140f80e084002800b100d05800549441c80c1003519513544c801d25041c41d000d080903205000d180c0c540820a089142e2081340110300005186c04004840a00385640142c03c00000c9060342d10400c00300c3c48048204c1c141e075070152802440802c80c40d40150341e01d00c113180200d0500c41d0b203080845840110070281c40344043c0c0404c100000c1c485ea4044090507074103e41c1b80c142081c14640c50b66164180e82c2c005412035001a03124003010803025904019050110485000810843c10420300c0040030303c0c03840c40350506200c0d001010468181c810010b010070000c2c00294905d02c10098040203010f015405402c2001684800c4880c00c0500044200d50407115006c006081c0e0301c4024041070705201c803038442e07142c0d42c990741c044421500321038240e41c1001442110 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 332550350 1250 332549100 332549117
    0x1020a030b0f030607082202030a030302040e060d0c1a0708120402030d030213050f060c0715020c12250f06030b0a12050d05090d050703050d1709030301090b150a 71
    0x10300b800301070041011501d1080c0d0040c414032241710f802601c015000000b007200074907083c00fa071407040a00e0320a820300a415114445620050540c0359003d0415201003807648005900c0340000c005030901038400141c0701020341c1804004062001d050821015100d43c1182e04058440e11901e0b4150807098800300c94240b014100001c5280c144482410018035040850070002c1b402c0c03204030080c003203000d014011889142d03508129500d01c4140c614140c208411182c00799120216848541c1e0a0303020003000d07120704d0103030100ca807503c0d883c42c80207001c2890061801403224160707a80c0c4905042c1c501d0350140001070700840c24034810480038020700041e0f180032800c0310f6a102800010307501d40c2c0c040c50b80c192a01c0d4200d4000b9001080c2000e52082c0e5141072503c1e900c02d003000034070001300f403d4000c1503403103400000410032034041141c035801c41051303c401c9990420311380044010401241e144100ba00300700018130a80b00103900440703815102406500d80910f1809903643c03a03501c40c48911001c00c0a84 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 332551600 1250 332550350 332550371
    0x305091e0105100506030108030a0c0c03151d0c01020307110d02060304050d020d05160f03120e0c090907080a0311120408010509100c020d050f0d0501030308040308090705010c021003060801020a03 86
    0x10f4050300000d00090720404d195604d8100b496440e03024422403941003200743c40f024000c1c01035065491001e15003002c0b04581110214030f80f54024140802c201140c0248000001003900b40170035622110303001a00070303615101007656841220780c03030348401ca0790000c402c08589000da02c8540240d071044c1d00c921300400c10640880406031400d50100e101c001003260030003e0605103401041c0c0f40c02480d600060f114120006071800f5034101d10314011b08040f1a2604034a611468400076104895a40680d42108c446d214124400c1e00c0e88420300560322594030015200000a03c01c0d403240003140380400c1524461394015004c18441d0b030080c0d21400c83d9039140c03c24407405074000d200040420382041c40070000402c103510083d49030083c124440c3e0602c00301145500c00c00c6e4050080301c540c1900c21804006070740c0c6034034000d85005801d98056001501e0100000d045001c005007220075203405840e00448140c0d0343d42003101d100d43c0d0700696000c1544542d40010b142e6424005800409810345020400c4d100340c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 332552850 1250 332551600 332551621
    0x1050f01170604020112050601020f1b09010b040b161a010603050708070f140c0111030c1b0a0b0a02031e0c0405011d0a051516030c06060801090b070305091e0105 71
    0x141d5040d0381150081c5062000503a044100502c0d100e078403480210707580c0d03521401030b800e0500c80400c401850144080406010000b03401441d2800c0007225000004c0e602c5081111290040d8003540180c0f0108003d1f04404040c0c009100d204140f0078034004020f03522510070100482d0007070f84420b0100e80c0703034401e02c050540c02c40101c0d5440784039860701301c201c0400048001e2002100d5110303441c41c280001810080e0080a41040e0f0080308241301c00c039900d080c4007840700c1d44c5600510448020821400a21002003408039043c48a00e0300080807826540b17030810110300a40c0007038000b009100080c0516071103c50b80e00030113842401d0754540f0301d80b034a02d03080000d446603a0000c421808900d206990380d20036074840d0707040010f450058850002140d49001c922855201d540c68201545114852110030513074882c04040300c0c03a11410090105581e03401440b800c1e6501d5080042255004800150032280310f60310441d485900c030001c540c3c1407031b1a03140c08050302e08146400283c0365150800c0007100c481 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 332553956 1106 332552850 332552879
    0x4022106031905060f010f06080a0c1e110f031e030408041d04020102070605030c0703080606040f060305060f03210f0d02040b07050d0e0607020415030501050f01 71
    0xd1403e0181e5628021120944001d4892002092000d1304810b00421100640c50301b07645a00c480c0c03580c0b80030b04045239034041003240500011800c0742c00071002604030182916901d41103082040500d0030808044010f0380113500c100002c4a8081d900151421030004a182c1d050b141d8070b940c503180721644200d80c0424040d06081c0c45400da070340c41a103011070166100b60200c078815903a40304c0941c1d036400304030341030307212030109001010219000b5a003c5a10840040180d85070a03144c0d02d0810700d0280036001200065a5041013203113a081091004c01140c8c0124000c2c014082030300340948c5059540340304502d40000101c0c048070455030031f0003038541e1002c1c40c05056403101d40b1a0501c07942d54014a5080c0d6061140702d108900c640e0142411203501c01002c1c004034508001a001c1c840079107203a09082c0e1843e4260070001010070400e20500e4000c06c1d07108580d098075450560000074801 = true := by decide +kernel

theorem cover : BRFrame.Cov 332374100 332553956 := by
  have h0 := BRFrame.cov_init 332374100
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332374100 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332374100 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332374100 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332374100 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332374100 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332374100 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332374100 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332374100 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332374100 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332374100 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332374100 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332374100 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332374100 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332374100 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332374100 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332374100 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332374100 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332374100 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332374100 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332374100 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332374100 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332374100 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332374100 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332374100 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332374100 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332374100 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332374100 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332374100 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332374100 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332374100 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332374100 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332374100 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332374100 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332374100 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332374100 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332374100 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332374100 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332374100 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332374100 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332374100 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332374100 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332374100 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332374100 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332374100 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332374100 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332374100 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332374100 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332374100 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332374100 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332374100 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332374100 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332374100 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332374100 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332374100 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332374100 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332374100 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332374100 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332374100 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332374100 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332374100 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332374100 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332374100 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332374100 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332374100 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332374100 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332374100 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332374100 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332374100 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332374100 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332374100 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332374100 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332374100 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332374100 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332374100 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332374100 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332374100 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332374100 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332374100 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332374100 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332374100 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332374100 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332374100 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332374100 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332374100 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332374100 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332374100 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332374100 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332374100 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332374100 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332374100 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332374100 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332374100 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332374100 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332374100 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332374100 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332374100 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332374100 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332374100 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332374100 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332374100 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332374100 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332374100 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332374100 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332374100 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332374100 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332374100 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332374100 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332374100 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332374100 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332374100 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332374100 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332374100 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332374100 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332374100 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332374100 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332374100 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332374100 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332374100 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332374100 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332374100 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332374100 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332374100 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332374100 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332374100 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332374100 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332374100 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332374100 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332374100 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332374100 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332374100 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332374100 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332374100 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332374100 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332374100 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332374100 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332374100 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332374100 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332374100 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332374100 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332374100 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332374100 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332374100 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332374100 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332374100 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 332374100 ≤ n) (h2 : n < 332553956) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
