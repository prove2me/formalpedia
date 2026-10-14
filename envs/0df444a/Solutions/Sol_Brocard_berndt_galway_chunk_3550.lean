-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3550
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:59:37.388546+00:00
-- url     : https://prove2.me/submissions/62561e90-8624-454f-bb67-d95b2ea68028

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 638309352 ≤ n < 638489208 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 638310602 1250 638309352 638309381
    0x6090a0f1e152409050405120301120605090d0914010201180b090d08040c180e0a03020601050108010b1204171629040803060405060f030a08091e01080415 68
    0x5070000d00d0b002907500840d407a69036581e441c168091625412425443c480090070702c84550915051048100081c200600101c07454800c0d0080d141c191f5280e540a54002c06c914852005040c496080000541d1001458254642c102030083c40c007050b0800078000507110350a288413050001000180e00400c01c02110031500095419802e0270442ca00400034841c004010548101d070400d210141c84640f001c7d20014041c4109c02002d124240150760141259021408045039404202403030310700700705d55800d0650050b0002001804a540c01904242c01424028005440c041c0f001c1d5806d00f5866000c2d00003000c9084e9080342d1658060001c040e55502e0031010f1401d0803000c1c02e45401d882c000b40003141140001d076230716500c00381400b1070075115102d160002d400b81d2440d540c94040100400000300000c2d070000b6050340301d001e55242000007031b1105d449a450070381e640280004111403001d800d00400244003e008043c142a40c0c0011542d401c940c0c00045408041a03945000000c3c00d800f540c04900d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 638311852 1250 638310602 638310653
    0x92508010914070501050901170703180812010b090609150405061c0b040203061e0d080f0d0b030c01050415050f030f06040b19152703120206090a0f 65
    0x2840711070440074a000c2d0402c0c0c1102e1050f030340c1c2c1006584601034031140c1c43c04907141c03c1060f01403900c000e00c42c5a00108615000a407906603441166440c01968810380341d00101095100e48035501000c01d07809003212070b0006041241d07060003c1c000303100d6035002a018540820031031200014a0302540d0107818010501a101d0407030446840c80c0e90072540d4044421800c0003040700c1c1e5070415200301c90103140017510024010107014440c98041c07c4001c2c0f0607401c03003050004800400c280c1c07806007030854622043c4030b907518210780c03081c800c1c0c6500b030030103512980003000b4088451383c00c44220b4048a11000c00e0300580f03030a000c01524240220340c030a4110340d1002003000002c0c0b0282d40740c1d522a000403182000044150b4003441100801072158891854486d0014407003480040000202070300c5600d4112903514100003643c40489101d0031903d408032101d90180100102030060b0f500c480c085100034a245d00c0d00070181d03a511120400060907075541d086440b402e00049402c80036140b40182014034 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 638313102 1250 638311852 638311871
    0x20c0405010b121b070204091529031c110f0a0c030c091a1e0307081516020613110d05070618060206010b0a091203020f0706050309250801 61
    0x4600368030001241c0801c02c03120000807a00c413090802c0da0f1184180e0810305013444c142c3d5090100806003d003003a500e404000c841000030020b1801060000c2600c0050303c0d02e15042c41290a40e4a5055003a151083c0c00a903419848504c3c940e00400d00149945884014081504229410701c2845036000d4414029001190709010041c402001128441d00d40306044a986100d440f08807a84050700b501d607420950381e042058903001d100040103000d8a0145400c040c4854002403900010b9407041007585c00440380f5108002054071754170381c0560700e0392019400c1c004400d0001c0d1078840040245080000f1240300d042841080038400600d2180544030304140411070416990f80d820b0340c460311001405180c1500800030b0361036910400c54980d0b0b002401c0903402c01c0844000c0d0342008841d0001c01203409030014002d554002640f4070b00c0d020342c014080c0c90002e6041a420701d2169004003050150410600084190014002452a0201840c030301c440d121065850196149079211101540c00c102811 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 638314352 1250 638313102 638313119
    0x50a0b042a060f03060605181c0501151508040b100e07030203180d0e0607110a0f08120301050108070c050f030307050406230304140c060a080916080d0f020c040501 72
    0x503090792681e48580c40c41a01c5503c04805a03a414000d00c000110144030180182600c44088a0b45003170041c2043c00c5000c0103019035080f482d41c8501a6000c2c1c0d12504481040d81d03c05070548040c0c030341a01c5901c1c50102e46400602101c101900003081000c201000683c0061840c1114010348040c8040c91210f0400d01c3c4004c0180d0000e85000c081390281d11154440820009031031110351229444006228500d4001c12400340c03c0540d042d61007000304080ac4026903517a1103404007620110504091103070070030300c055203040d4507010070400c651030410040c0041c0c0c0e0031106040d031041d4603151828080102e85440e500303110003a400510030f072002005011040d6000006001a21941e6079800c0800807100300f048000c0803a980c1c0da040c2c1100070804500030030f22080d98918400d1090b011948583d50f00c00200d0141c0e4014400040000c1d506018415191404d2003500f800390b04602d60030800340d003803140c00b9890740580301141090142c0c000340e4101e5240240301603000c003c4024020002981c0d1203580d03 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 638315602 1250 638314352 638314433
    0x20f031603031b1d0103020405040222090504020f040c0309021e031908120606041206060303120207030f110c0909030a030509030a0f200105070909060b07050a0b04 72
    0x1c402003401c0414401101c40034810181c0c0e5903000da500c2d0850003689100030f00300d040554402504154003040080740b242c40c0c0d80014a01c50125500f40c115881003001c0c003922748401904103014043c200014440540c3e00c07480c0c48a102c000443e00041d449003440825030003400d485000035000400c60407a803800c031a141c07089600a002c00c0c0c05440544229202c820040703c0d854500400d403060500020866111100304c0303d51080024255070b180640310098030960000c0d499007140e4040d1280704c240300b0160711440c01603051148040950414029070b8000d090480505006010000c00308442e07194200c040050403414400900758070118200031042640b40e610000d079110121782400f002c100d10f00c0b030000440c2c0c1c200d022643c2d15485048003240454500810b40c0103506290403040403100d280000780316644c000c0300c154030303401180d80c40c00180c9426941e1550101180400a000b22400b00348041400c080a03903202c00710f982e040e511441c00c3d201400180c50902e194000c010003d17400310010580 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 638316852 1250 638315602 638315647
    0x60d1b03110a09121b090b03010c030c020c0f040b040603140105060109060207061b0c080f1612030c0609240f18020d05010e010c02030405270c0a020f03 67
    0xd0500041d280c640003003180d0302c12045a240041c1e42c0c4442006050401d81500395000d1050352206200106040c0350f480d1100c0750b8000c1045182d5070905905903103401d01c51000750f40c02da800c05001c400f020b114042e4803030707614510346805044904d44007011944c841c1c1c041d2020341c800400401002ea240e0030840c0d001c4403035074002241580307020b002c0380966006200396401ca825580c001d00c0b640e410500116529001000325941c0d03c449140c01c40d0029402d8a00c2001403c1140e00030704655031040c6d00d884c5091102c0403520070780d0801d0402813145846204901074000d402d4106486000300610740003000303240c0300b44080c0106a100e20f031403403c0e211404900c00382c040c1a40d420f10502549e05807002c110350404a00c01a208210104000141002e030030390400c003070040000044170b0b11010388803801c1d150002030080040e040002c0c1401586007440ca00c204400044184259244590320150b00100010b0901c5d102c1c0d0f000030a1511072903200b0042181440341304025030352031309400451926409007050 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 638318102 1250 638316852 638316857
    0x621020301140408070201050a11010228140417070e0103060903090e1306050405010207170a110303010807030204110c1b0405012705061207080d111b060306060d1b 72
    0xb0b0724a220145940642d03001d82d41000681c0d24005242d80151007076840b045154083c440b5816080713282d86c00c288042c0c45001c00c24086482d1a943d1440b450111824511101c030512207083d0103508064840b2003a2402c0d00d00c0200003811500107400c1c410300c1c0152980c07043c3d00301c1e071402c0008001c2049a80205a0311486a144c16480341d45030b449001e0b003d0f1040b01d8038400164801d4100000c94040d4100c25042400b80000524040d9640c952450102c08018401c00039480014607480190b4403504035036074400201d0165065504003031425464032810700c000b0340b10300d46415505032620100803c42d100d0000e5582118401e03003000b070300e464082e0700b541b2540b4416458500005050034182410390f441070300d020214242c414158003d05c0040070702034486a00324a81103031a442c030320030410080b0041e100800042241003a03a074002000d80000007201d04807a041004801c0d0142c0300300304c04000100702110356a0301c0f0382d10745012954600071940c0305c40c00b1605040000c0b44603500791802e2145050242d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 638319352 1250 638318102 638318111
    0x316051006080d02121e0307110d0c3f1115060f220e03190c02090c07110d0f0308090d0504140a0b1b0f0d120f0621020301 54
    0x12254107442d100d81c520b180b00560071866820000c0785690005086c5440c4158480d030651030251a0500c1c150021503003503011500c05245801d100c4020804480c0002013403505160740e4486540305441d91300804144040d0181880000d4058200c50307800e840d09540a61101d800182d46000c0105405221074203c02107008002d00d8000299034004403501c1588060b0000748111100003d01c22035141c1503848070322820507080070200081003402488080d412001c01583ca9100000500400e149405400c406000b20200a00010303180e0509250b0710500b141d000d25103c08281c00c210b07100a800140e0b0a5000008110000405c1208030b003401d0540c0c000c6c1e44880342139860340050b035a1012085041c42c04144180f0080104240e60351114941e241d000e0b01c1d031541981c1e034030294035070381d0002100c201c0300c10a0080303600d003031010801c502102c0a041000900030900499005011744030200481e1181d180c0b601814000010340e60000c0e001003910030140213040503c2190b88448a40b0560202c2c840d5080 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 638320602 1250 638319352 638319359
    0x30a021009241d0409080c0d18140607030905040513030f0207050a0512010b040f1e1802010f1b030207140f0609010309021306180501050105070c050f030316051006 72
    0x110081c21084034100c1d03d402c1c2408441c11071400320300d0401410180e01c1605d44c5081c200284002c0050001d000300007004100744001c031213001c1c0800f4070b0519208a50f611036401041503d034260500410460709440c469aa27107818103045a42c008250089508541402c080c050700d8088900c110907a01e02a1b560620041c400080072601c40340c02c1c0c400e541d03000041396024001481c0800e6400f0044000ca40000307400028400800d0980e01d011403811400c0390ba50590101840501c04072440c440c0f0304090030481d0501c0100340c5000b401500001a0403c2401303100c410005000d1101500074a0484a0301c04c5091517614000b552650140149100040b41960310045820aa80c0c101e1340404001c1079641440c142200440c01003010200a0f80d0104406000303188444c040e10030a005040350f01a480c3ca4010145245020750b14180e020604101c42004000b01184c0f0144ea60750980b0320444205449661140000380740d40103050701c00100c181041c0300c00f010008001917126004a07283c4050061540c0c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 638321852 1250 638320602 638320649
    0x10504110408060708011409040525091e0e0604050a0f0204290f0f0a03120e060412171c0504020609180406140601050a08070909110909010b190e030a021009 69
    0xc040c2c5008101d640078041030bd803c08000311040b404500680170313440c0450750b1800c1c00e1056404031603182c50042c01d154480e00000f2154024000c0104c4150002c0680b0305255961a40d645490709000d042c448031405103072f0843d502c42c0c000ae40102050004c140e41e12400c00c03041d0800f524082c901c14490109990300c2d54017810001603000d24407600521260034603145464038030540380301c0c00080d010488641b00c0a9070540c0c0702d02c0544060000c104107060180c2091030a08002041c0e5141c44800c032000b403001c01c07480d4404c5030480010208100c800701d09920340e0f101003003541c0554a41180d00c0075111008010703c90022511031710030750082c07100748401a8410701011641c00140c81c80c0b40065070410603942e500b400746103500d81081c0c00b8a01100605d0303940380d04404640480200201000300061190343c0c519101034800d01404070608498070306401001100048000401d0350018440034203902d8a15030b40134407002c1e21164016002200200c03c0f28002040c143c0725000700000380301181c1c4180074666 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 638323102 1250 638321852 638321869
    0x1120c05210106090b03060a05180108010e01050114061b060c09150a02190c08060a02030403020f01420308130611030d1a131b0212030105041104080607080114 70
    0x2c043d9281e88103000e042806207551030340001c0c04141c11001c109030020751915924a503201d00052908100c550707505000c01d40d402d441c850041c54085a051000601480700541400382126074200c500070340d108600052000c800301048400030707c03400740d0810402d0000d500c10041050a03c129034458850800c4840e5694600940c5005030040e0301182c100c01030f1030304402d05000c03c58041d94254861568507214186170440c2258202c0c03040c1c3d008000c4c0320070541c04100d0405101e40d048000d10614143d480f81c210400d413100401100080a09065900607405180040c402602007004010040e12402c22030401d5218848109020b6a007a07800601f45d48550328440100780c032003029600d0708105080039805051401e100604d0040004000300f040d6403010b901c080040d070410340100d51a42445601040c5450444d0b00500303541101840703201c3c2c1c8903408102da0551308101c80c00503020842c045042003074004d6421003105403041c8401d00481a40100c200c504070303000f481d4158060a0f40f41d003480300d0301 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 638324352 1250 638323102 638323109
    0x1080114010e0a090218041b05030604020d022101020d2a0903020f130c0e01020d091a03090102040f030804050918060604110c010204091a0d170901120c052101 70
    0x503a940c1c0100c1c1c1c8842d540e030842c541003400100005480303a05a91b6042501100f0769044541e100c241000040807240503076035100030a4210083d00a6103055001701c5c8103403150040092194040848000910016013890703034001c050440219201e1750504400c100500800880c04411811000c004198503c0085804450001999100d01c1a4959801d0055031140d011206905c0722118011480d0180c030380c400c070403e280803503881d49205120b1000282c100b00500f040d140c20005c1c0d04c0c00c1844031001c0030240e041c00c64050980e0940e0707959220002c178024002c98102c0b0400846402000061281c00d02c003234416a241118103081d25100e41d03420101c00144a50700307000c103070030020000d00d95241a0f800140d4401d0705a4803c4d00c1c1c4270715024103608983c06a044140703410360f1010f203980340000c210350720440c1c40d4040c4d8103010a512152545c0d1034005245508000c003000020b01040c045e4441da81d10110f04060740340a02c240801e290004d405600480e854128100c0050a4005111501038029048 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 638325602 1250 638324352 638324369
    0x80304170d0c0f020609040f0218040203070c150624030b010801050a030f02030c040518060a0b1f0c020d0c082103010b0d0908040b04080f01020403020a060e01260108011401 76
    0x90340143d540e4030450f0303800d004140d910410034044070140740c0310380c0114804401b0038140166a21002d1020f00518140b401c0424081c610510030080b10356041820700c04940d810203002e0000c102c1c0e01c03204a010b003902c1d41280c106c803045075101402004e896540250310a07420b072000d001851740e840046a1900c0e00340b15284e031100c4881d1041012400c00300030024102d001a003a07a490705a40004074055400540b0201d41201c40700c400c84c000c4480a001d170303c0d0851000b9809020000741d010001e90140303c104449140c8020120480401c24001d00501414941c06000c003e0186c03030500307100702401e14900c5040c0e00d60154507004448086000183c4d60491502c0c005241942d081c900440c80300d401c8031002d100c3c4503982d803050101180081010304001c3c03000c0b00307607555a581805055400d103001200342082d00d038014002440107a48038000d640a0302c815281600b81c01d9035000040f00c1f011100c070354a0130010b4500e500070350270071000d1100310306075422100280100103101d00309410b40d41c1c0900c102d004 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 638326852 1250 638325602 638325617
    0x40b040305070302010e0a030509042403110112050c0901080f160f090f0803030402030d050c03120a0b040f05071e0909110927010f0302010c0b061306080304170d 71
    0xa0059002c1c092032406132000049800011345d4071850300034625002ea012540c041125002890305010305158101010902c201000000711000603040207400001c5c8968002001003203164815100e0450a0701302a106100d1802d002060341e1941e807100e0170b054005480e0400040b83c198414aa19000340c08050b01c14590881c5984200c1d0a80c1080384403004002d80d65500054410b00003050801401c9500e000d11307501c1c1000c1c8101440e120b000c10040c42030100038880703039141030340100c180d501d110300d0301030600e40c1c0341c2e2210b0355200208000b04001364000c1c0342015401588505030311040c40b0300d455403100c100348218051003d0224009040c40400a0200402445400c1c40758001030140d8070340d40081070078400500700141a442c100d440d02e9110003c0f02007404101d034080c040c44e6004251501e1030070040d50460300020044d12103114050007070305400e07011424a0303c0700c0c44070100700078140d08104296500d5118142e1a039009105210012600c0500c07400c098001003580d1601c88682d844240 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 638328102 1250 638326852 638326861
    0x60301030f02040906060807080708011508070e0a1e0203100e1501030b0a1502030a0816120203070c02120312060603060109060c05030f030f07110706120b0a03051c090905040b 77
    0x4040d04c1040822260940c8448000481003401c201650103030a060f0040c1c00c07a5420800a03908503007002038840703040c02c0f04600c100720800d404200e080a9820000004446981d00050306c0042c0181080034506100c01166010710240380e41e0140d80290f44a02a00000381c1c1d540804440e1648140c60700441a00010164603496010b584805802c0f00040d2210151603580c2503d45c3d940a001b0210002580000856550542d800160a81d00130310b070021001d0300c0b5903000001030485c01074429403c03040b58000003055103540544071402c40641d006000340c181910303003801700d030312a08440340c1d41100d141402c01054071407501c40280c0f4420340040c1c1d00c01640e1072800c4011240320030140c034186c0d06808204450013181c4520802188500200a1184480e003085000101040310382070069503240c020380c0e42031122540c0304882c3d4098000ca050007040c4211400001030a064181d40018904c0c854010401d11582e00704542280700c0c281505ca9043c80760b40e40c0900801c0d1203046034010300e82e420040004 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 638329352 1250 638328102 638328109
    0x7030b1c03030b120d140c030a1407020a09020d06121e080d050907030b0619140307080f0c0906060a0906030513050604030c060e0111031915030b0114060301030f02 72
    0x20300d000350003841c000c10b0540000c400302d80d00c0d60081d03071400e045801000401c40c05580045000c11080c5030301082910f42150b100050351280074410381c0c80100b00d4003000f0b9030007003803004050b500b54a4000705024a01c1c1d68540c9003400940c88a0f400400c6d2600f045e600080b8a0704488034805559080328414004003075011882860700b01210040b035003a24140010101e64405100c0d01d071244600400401d02c481c01e5041819050100514240c4600b0901d010000c0061580240b04110350090201e100626011000241000101d402c202c0032442030b1700f04030b802003200142d00c65804800b5528086107450700c40901c1054402c40d00d900022807401c5004012941c402c0d4800d135030161100da40070401c4800c0340e0712030741800020b540990010b0b00c201412000e100d070314419400f08244520082102c01c00d9181351009038000141441180660982e419040c1151a08200c2100e601800d811191a031285490070b035510081c0a0190440400c0c070304800541040c1080300d041e61342100350090718003119800c0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 638330602 1250 638329352 638329399
    0x504170705100f110304050313090c0f030c052101152a08090d05060601030e06060d080d2a020c010c08030a0203040f141b0a0b04061d15090907030b 65
    0x1004a10f9540742c81081c00c01240d5409140920311032006990780b5043c110040004131103580080040b42c0ca8440300300049a040040400301c10180d04010581d05d04c00d8609548500030750305001d140c4045d03803e4140405285c245107038161140d078882c482d401e12110400300c486c035003140c3c943d030058100010074004048615502449151080d807030b803843d0002d80004180f6800c100002200d040c0d206034280139596030103001d481c0782012260010101d910703282002030344043c0e102502410710b400c002195500f51985400c042c030104007a1400e0740c80448044c4004040c10080f8540d8030041c0540d9030b0802d019803194a0344044a504400310030306545070240b01d00025407016000f04d440d00307030501d07090002912480305461504800f02c007502464140300400c02500340c12802c00740c0304041003101030100ca445c50003501c09841551903c0300d00300b00c59125114030020012801a1301000012100d040c901c540c500400c0c40c1c5000b23850036825520791000540640b07010702d103d00d600400c0701040e0828509405030 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 638331852 1250 638330602 638330621
    0x624201e0a050111040311010e061602130501060915111203061f02010209040605030a0b010b030c0d060f0f080313061d0a1409060306010b07030e150d050417070510 72
    0x1501c6030360920303907602030840e0004c1c03a0300101903a02040810600038a040380a041c141c0a0034000348040030f9200150f0107103d0381525040358540c0301006429510340000c440010140702c0000c01942d40c41d4580505000030920521200036040000c102030540700e5403601801e218180001d045410800c0101c190542000b007001c0d80041c00036800d2151a003107e5040e02c000444c075000140d880c880344061109440d025086140240e100740d090b000015030803101141101c903030360304880d01ca44030260408801d00c80c1040040f94681031003c08154400f00d0342c41c180488040600d01013134542c1d6050a1926070081c080c03e100415000941000703803a00400c054820b545a950311104510702e4400015007400b141c0c5c002002c0383c052a81010340e00c1c00c0550705540c000038200c0c000e11300c5614120300d00440e403044a10003410007400d12101e042a0329068a1682400c44160382035445020b2a0313044401458201c90a5680100c5407203240004c40111088030b16035a0000003400c4078100201d07078a07024100403034 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 638333102 1250 638331852 638331913
    0x51201061d030d0f0806120319090b1321050c1020010213050418060f060902030f07031a0d03140f070309030b0108150a090204062420 59
    0x10040e00c242c0e409002c1c400d500001c42e00c44550b625070010008000740802421301d4043c581100742080300040000580f4030303842e81c1c0c038502e1000d100f1010084030107039907a511440c01c2d00b00c0400e004002c580440403060070380d607081007040c10480741c25002d01400c5210b00c074040d015401c05060a000d42c00c100e032881c0c8900d095400c1050b15407020b03900e018039801c06030b1a00380e01a5804a03035860303288145c0070311100030302048034144940e092940300e5000031b10400360014010b640c1d4850229507400145c1140004202c000011916458003191030501c00c8801c035100400640703004d0f400000300c0c0070030b26082c00e84440582450080c007401d0f50159a845046040652115818403180c282d80d00028024a2014440d54508150318654586560703066010b03040035210350880c604c1c0c07082159002c2001a48801152804160741c00603001180040409401134914015280844402c40342c90380b0303105000c0c21a5945018400b0511020b0500304200d940005203da00100c810b42050541001101801c3e00c0c2032 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 638334352 1250 638333102 638333147
    0xa140601111203130b0a020c030a1b0b070c021f0906030207020a0509040503121510030218090c0c10050402030a290403120b120c190302151905120106 66
    0x254202000d5041212010313180a04d2616840802c51181422a08034000e00019070a220413100195102c3c06110450010084442c0d0341208069400c0c0300381d04e40c1e6820104050045c2400c5000901ca141d80c000c090b40508101500100903074041000941c4e0001ca5548010805041c220114080e501010050368000b40f406c10220f40c50b0b94030170489009510643c02555101d1301034804100c0b0704030003080910141151480b110b215283c0340e240450460203031600680c1c416810101810b03010400c403c02c1e40048406042200c2500c240c00100031424259080f1250900442c0341c101c1034070310440f4004e4054011618480c0083c00741034096480e0b1071180c0000084200c0c1e1401c020000038110ba00b42c2c001007070b04032418000021440341c1c0c2030004054503146500c150a00e613942d81c0d034a074070a82c0c5000742c220100421480788201c0a00d80515401841030400e800ca0a8a00c4169004103501c8100c4031020851205001d00660840d080c6080c07076040003016a190010a07a5413052282d0342e24039080d940b = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 638335602 1250 638334352 638334373
    0x1e0a0b0a030c241107030803060105071515080c010903060504080405030a03032a0816020f070b1209031e070204060902070303020a03200717070501060f030b0a14060111 74
    0x3080b0103401030140c82c0c520241c0076100c0449094286400c54405051101e28032108107800000302d030a40589401018880e52034481c074004995500c10104083c1c00700b0a98140d54000d0803c50b000075804081c1940030784051900c4800c3d041d21401d00c030003080e001c6010320744200000303100340e00207a5000d401441e8060805503610040307030178040c2c251070440000340c0d2003030f1040d06010605901510f0b1114003005100314201520050120070010380141c403c07042038800350850030720810520310000300c41810f840b06144d84403c110303161703040200f104010b120031200044d561745000003920b500c100081c0c0f6000039800f110302c41075969442400280d80082d1202e42c0400c81020f03500040c00c0951103646e0050780d1b03101c1e02c0c0d0700600700c1c0d000c00102c5420400c520381c076030944502a420340f000035402000d1000303034030081d254030300c07180c42115801000d80d400d0160004840c0c8040580740212030007030740d01811a07503410074850111040008112020344060000c24019486420700300c040303440400458a19101 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 638336852 1250 638335602 638335613
    0x1081f090210020607030e060c04170a0204060621110a050d090618060b010305090c010f020715030501031403030601170405010207020409050c01020708162c09070e1e0a0b0a03 77
    0x642e1201590091060081150f0f0600c04d03c10884002009018203041c00c079801440c1d0b128a11030b1a030820f601c8030b5041010300d03090003090003a40d0b0081c82045040c0d980e007006403400852071444c0b40c800d07a8040c1c4030880d00c104c80c069120045152901540303840d0030040151801c0c1c204450781c02056640720002c4001851310704c81c0e901c001c60007580001a00c1d0191074540c080d01d070380807031440c101400c2205100c0210000580381c43c0015090900320b070790046401089103080f115910000b1100920030b01190340607003540c016410799019540f0080103240b00d01340141d40384010703030719140002c1c000c40401480140b5016210b0700140310760000741c074000b203c2c0c000030b0680d442c86106913003541006603206090342e010803121004041d00f0004c1c108082c40720324103c1e80e021261140c1010714004c0d40c1c201403090000c06a020840721802408003090901000c0d4a503200120b029441c001d0304103e01140b440c00700042040c01c4880d40c1c400190703490351003810040103040104145900807000c0e40000c03001a0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 638338102 1250 638336852 638336869
    0x60a0c05010e1f09020108181002070b040201080106020f030d2a110601050a0b03041205120705070b0106050306031f1805010b0306070302030408040e060d0c060f020f0601081f0902 79
    0x21590004003c9159000c400c9080b1280001d82e00700c50034a0a4130950060b40c01007140740e400249150605100c40c0507041c001c0c10812003110b01c1c12210320002c0d05034104580c035010780e4001d50003a41c90a135142c0c0c0340d03002603940b060004a291102d500c20320010f25044803542180050510304001c81e90651080d203120820302d41d1030050100030460311041800c6009007049054010201119102500c51404210340300b50301c0042c0010f40f81c3c035a040940c1c0c0c0d02900860883c0e030342419900d6a01c00916000708020490b8100010845200c040311000244081c810010341e405414000c0c003500442540000e41c0c030080c00c040e01c03101c12403034640940720032960001c001d50020718082e40000c94201003600800d0b041042c000e004000b454410300600011074075041c155029507001134584c030440d4540b000040c0c02249001c10003000000c40c2034022035496030050540c003480c3c0243d000c0300c2d0600c81d42146243c07502d900b401840c000c2d90004d002c16450b80c001d0641c841c1a9598a07000040a6205801050620 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 638339352 1250 638338102 638338121
    0xb04052419060f08090309101803020a030b04060c08040b180c2701050a080d0c050709020403060b0f0306041e110306150112060b040e0601050c150108010c0504080c060a0c0501 77
    0x2800030282c14030550b001189103034010045c60240d884e1000300000104080241c041e04007c0019082184100d1140d1040c41400b441d002030034182c1055403450003000a030030407a0102c8403181004074081070b160092040ca8050780d0b00c529000035603591300c0340220710501a040038420502c03c0302d1500320345440301510341505421140a41c10780e0708450b0000c104150069001c98010b0301d40500402c011781021a03c059100040d1500141110f40350074500d262007001e4001142191001a0000400c0b21a80c0300041e000c1d81a140410189125400c1540340c450450b80075103542d0000c40c02c520151080c50281603058441e070003190010303d0301d0000c64a884400c65111b80c08030211000b400c0550307001141d68041c0c6c001e860742030000341d0038100400090300942c41208980608400130500740d0380210192818803600808540005030b82c04850340c80c2942c20f1050f01c07002d510b0140c42d0b004051161080740d0a481d06200100842e030f1030f01d014401154000c0e2031581c200446142ca68000940c280102c0e542c0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 638340602 1250 638339352 638339357
    0x70305060301060e101a040e0124020619110705060f09010b0307080d051b01020d0c120b1c0201264303020d090f060b0405241906 57
    0x24504281850b003103d9032600421340c0700d0180010450f103903540c03000301015140300000c001e02c1c16004103c0510640170b10f030414031036501207000110350603800c84203100d088052240d0054030000c0710f120580e103d2a003038070003810018000c0000f40b08084030b034100b03810200360b0310585440d00c0b5036a00c0b21810604140c401d003001101010034007171600310902401c044200e00b2000744c40000d242a01032642c824001400000307001b40031401c003210390346451508154120600c001d41d07440d80004441401408011500f1000c1001d802500d036040c5860b21401c100c032b50000d06441499061b07202c0218007071a000b0030403410400080d08284080d80b81d882140401e020306201c0014074101354100c00720000200c07514003281f041900c480c0c40349200c030000305110704202803208404082200011070191184032452400c00d410b142c8044100042041c01c40502405141c0c100401c100740c401b000180c031419100402007803260400004841e525110003d00030000805120500300c5030203018280d0401130348030601 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 638341852 1250 638340602 638340611
    0x709050f070f0519180b0a020d0e180106050706050702032106061308070e06011d040c0207030b1602190203060c030a02040e0a140f0601021b0402040f09051b0a14160b0703 75
    0xe0200941c003517180030300310841b0011304060351494000d507107418140314101081091a503584440d04c0c9c004803c1d0641c500b41040e001ca030341c3c51380c0015120b44d01102040b0b4500c0d141000040100f4404815241100d0402c12042e5100c1c2d050038800000da10040c001d19030058040124000d507040000a1f017004101c150f0141512525022425128883c003d04007414409001c3c4201030b400c400802401450b1030403a40020391144001c401c900c2c00034150801011480b000c024000f101114880038020b003540c03a803c135035003e400382191040209030814004c0d09a44424081a800301c40140556444401c80780f005041c15583d68541c15003010030b503030340c070f41c02560f90801d03c18100041035503c2e40714000000da1801410401d00007560303055454821024410100d480c1e00080d6200d0b011200100401e001c0007001580321030340741000300400d5410355a03030982c244802e554000003d00743c41c1125a00e0715005564040f1b14550802c907804a03c002d00d0b1a01c0440420b000641c044129900620360780da400034 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 638343102 1250 638341852 638341877
    0x4050c101205131407030c09050411030a061d1203040305090312070c090b040515040b060702041a180103150f020405061204020406050604030c18021e0c0709050f070f0519 75
    0x5007005807000e0f41e4130194108540c1071010800d100c007a9411120603410028190f9181e041040c1100e11900800d9410300031103a062040c40966000508010081d15480101c00c1d103020b8240e03540e4500c0e80c840d40c04407009000240100c1e001d08050481c800c0c02500340c3d0344a95020f40c101e003070b40d031003800c08848030380c0001014032244080344110000c10409642c104141c0c1840b20360212003494055031903101d030382c54140300d0120f510b559054626440c2e014209106c80740b20718000e941da00059498540c010f0f0300c00141000404007040240f8102c9401ca13010b07a070300e80355404244004d44124011100c5268081000150a40b031b800014100e42e40c0f0f00c102f40300b00341403030303c1000180e49803540828403c3d00b0500c0288049421002c0480844220904000840321144111b00103800340d5903050404000141a0382c4c4258911001050316100d400e042d01c52554a80c108601261410f450409902070204006510325009401031207010a20781883c81c102203c0c0c0501407000041280b4a000013030025443c0e0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 638344352 1250 638343102 638343113
    0x180622030303050a050c0412020f01090b0c010f0e060f0f060d0b16030608071508130203010c0206090c100c020f01030f020408031308030f0702130e030d02120f04050c10120513 77
    0x15800010b41814589071508c5c0c81c00e241a900890000030344100032550700c010142e801000300d54010b28005581d00d46648246203454000c0c55041d004c00c2c209807e0400071040001e0114945104a40005c8000c0850f25681c86c642c0017814000c3c61290040c58082d20324011500c8021040d201e044010289c110903a41f00000038240c0d0400d5111000d20f03480600c05000c08500001314808030301047ca02031000da0348902c0701d121820003c0c1c0b801380d01540307440401100298040b550700e00c250701c10b6080703c0e50801100c09003c6048080302c1c11000082c00c1c111480014a030801c03100c80c3c4401d05140c003013040e01010703000704101d80c072540c8510002d5200240c0c80c9444050074500c0d200516680c0050360400807040380302d40c590311800c2d070028030604403010000a220001da0184641c061035804481e00c0709000c101440c003e611035000800070100138030000d0300021500d082c241c490340e0b0005c060a050200316050019801e280c101d00004d001c1020000300c542d104074455a48540002c0003040725150460601 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 638345602 1250 638344352 638344361
    0x60923190617010b0a1101110f041514031b09180105030d020601080318060f03070801060e0d0f0b0a091709190f12060603082805180622030303050a 65
    0xc0003800b814004114480d120301c00c0d510702c01c60038200491980b0103280c0d180d0043c100080c68400d10030000c21200c2c0320344660f001800980fa901c8400400e514540c2400340d4500701e01c46140c941044041001440c916400e0200c40302140211001a04200d40a80014503101c100030226020884d107000402543c9410001101e04412a0000c0e00e0300394101f1150340d45900c1003500c5642041c0910f02540d1050700c4850854240f0350740d89401503180d080106005100103000c1c400c95000a070594000c080c1c600e030002c0b1881001d40d1119400ea0780b080d40741e40c2c075440024001d061100340d90740d44c10100c01082c0020000c681019101041d140da41d03411a0030070031090b503103155081402885440c00d011383c50903401d0000c180c800c02060201d96200925081000c4d00003508010301c0c16a021407220042d0803241c60494064441c3c0d2000401070104c402c00b180c01e8040ca90496070304008040e0708803668201300d13001b40031b40c4841e0610846d2031280d0f02c503000c0d80e1103001d0b88203c000aa407801080740030b824074440c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 638346852 1250 638345602 638345627
    0x91109190f020708071103070b0a02030301050f040e06190e07080304090c081b0f04210203010b06181507050d0507050f010b0a0b0c010f0e011a06040609231906 70
    0x8505112003500d0303a44160007405d200410074205114001c0c03090390100b004000400b810641e01e6516955510025120b400030b226403801150901c030344219518050003409081200c04005100c2a52011000b1050390584400901042e0b40e40c14000c030100410302c03000000d0319848005581d81d503d4000184100c0300303644003040811403c0c00c140030100e40c030201d00b1000400054003254541c0380402d40919940300340c1e8080048502c01040030a8484060204020118002c07002080b05000450500c0804d206031030301040031404003a8060030518044403403407005801c100c40c076070030221965500c030b00d0620101021004600042510000c10400f003011404c01e41c000c20080c01400c3e5548041441c209050060001f480004640310942c0c100c25484200184070040040c018000400380180c02800b14900c04104030b10700d1800a840d6042400c1194220f6005070703210302d0814a8000788103d018001d1300c2908032440301404452081d40c410030b41716004442c0503510640300d4500080a043c130a140f20 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 638348102 1250 638346852 638346881
    0x608060c041505030408090409140d1409190504020d20040b0405130213031b06050301050609060c030c070e0f0a0e060c09030115090204030c050a0b0a0309110919 71
    0x107001411200480641c840e10b00c0c1042510303038a40349020070300e80c003034402080e410511700180312040c089100c410742d50350000754081d205100e81d1403a0488d403112074181075810000e0700300148412030a048921b100000c1d001c2618410301c540f2880010213a81c408022085035030389410315a030b071554030046206400c01c0e41e14915071905290001e120b4072405980314180c420544088803d10751a41901158908080b0094648200d46c580c6841c92026a07041c10003058103000da00041411402001224162100205080d013005a4842041403d62180c00ca03081780e0300041c0072400e00c80104000c01e50190090b5484000c031454241c0035802c8042000b0110300301c0a04040700302e070710fa48004c00c44c140c100d50982d00540d61071154502190242007550a25200c00c1710304c0ca40010001000d501030f2040e21300c50b00e0985c81441d07481c3c0c2040500c0540d80030f13002d0300300d01c01c010002042d070295110681042c4120f4020258070b04800c002100307100e080300da2886c10110300003800104a6148100b01d04220300d030 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 638349352 1250 638348102 638348107
    0x80106020c03071a09030303161407051507050912010501140a050904080a0908030f0d1407080406051f0b03090105070903080412050c121b01020d2106150906020d0c02010c03050d0902130608060c 85
    0x152233003940c0b04444c0c06800021030041021964061158044503412a00504520740c14000e0302a0b0034004c20091040c0a20759000d1440c3d03c0c4030383790100b801411a14018907840054239035440741955070f0b02c100201c406001014900055401090010741205042c000c1c0c01510741d00320401e1001900e0303901081160030704062081040d050380180341070fa0802d400000014190f6078035420b158450303000902d004004e1100000c00502111040d008605c03801490000740b000ba1112001541c0401d42404014450501884180030090903c0c1c80752040394060000c84a01ca00b40c00c000c00c0075024440c010f524260050b100030340c084050b007401480c16038001e00c01803408000b0309800038000c1c0130080107200e407400c00e1010b8036500d118580000024103058402c0709002c002c104c6021304607164511441000d401610b2581d180a40180400c3c07200741c0c0c060310380c03000407030203542e00301c5260b031050004407003c1d40d88202d1400962542051400c121206000000f80309007002940383ca0104020104101030504 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 638350602 1250 638349352 638349367
    0x92603040c09020a11010204080304030c120f150b0d1101020f1606030c0c150b120712030f021507081801090807020904020303070b1501080106020c03071a090303031614 74
    0x41c0c50008119103a0003001070b166000642d0454401480400070030041d030011401003071800010000f402200d1064852240840d0b950600540380311680c403019207002d42c80d41094021a0003601c40c411210b6290320002502201c61000421038108a0000e03110541550841c1c00345580400c07200300003850403001040e030300f0802589030440f084680181010591905482d41d40030740100e012103029a0300c016101290038000c0d070202c008042c0b580702c0a200c0c11134005002045c49000c20b134102074070030004a01d44103d0042d10160340d4002e6900380f074411403248400b00422101045081405040265202c0f80b6908100e100c2c4500b42d4070b00c1d04200102d901d010181c100081c403210441e20301c0b070b5040d0341001d032070703034443c00024194011100042c064060744810800c806280c6018a540314400340c031000100d90b203d07082240c0c0c481c000f010a0360540e102c41c03400d000002203940303010081c0641b00000c03440c11441202290558000707450001c0c00c1e06486a401030b180703801140c84400c45001020312403c0a00 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 638351852 1250 638350602 638350613
    0xb100305060307050f0109082a0108011401140403050a03021c0e0a05101b080909010914041115070807120c02030d031505100e0a0e01050f060c1009260304 68
    0xa031003810b108100200c1700c112076900032404400242603090a40300680c0380718201d100a44a8032403c2100c2900182000031030b50b00441440303043e502c95200d181074a4074034000545103072034804901e90800790309200020018101300480d902c05803007030f409007000d074110903041c03032000e0301d10001c2e4030500c81c1c207481108198a40c0f400070012104201c50042c20a100300100743c61520540080d00741d200e001d4041401400070b840c00034010100141c40d80603643ea644c42c56401214107401104006130180d00c00f1402003603108015450308400245201f903400104800e40c54a5800300004035288040864100180112180e40c1d0380d0701d40d0181444100e00c050b9a0002c0e444070701d000c1048041c9a680c14010300086001034061010f014050000b10680e0304a1002501204880240b07603c22620741c5004141350500c1754440e8121000030b8480c028041030013082156079000680c020016100e28803442003d10440c0c00780414042c06614040800d204018400300101c0d0300e40c1508400d0340040060000050 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 638353102 1250 638351852 638351863
    0xf2a21010b12040c08060c3402040c180f0914011505070302120706060e1612020906120a0c020f0a0209010509060f04060806010609081f021303080705010b1003050603 73
    0x300549041c071035540e0b580c13404622000440c0c101c4c17107030344c0300da80c041254a62102000f040303550002c5666500200740a80603e01101c0014140e0306404170040b030b120010f041c20340200c0ca14584d40c0c2080070714810480f02440c030607085548040100315540e81c0402c48100305108050384201e000e01c80684640c103200d0701c0380d150b001242051040060024420702411710a01035000e09169002516035100e119041650180920b406141201c0300e141c0d010600c1d29520055a642821458a400c00e0400d2560002c074025044540100e40220042003200300c501c00f04ca0002e881005890800220300c464400700a2500030308080d10340640d84031040900c0540e80e0211524112801110b09031400e586070b20110b0360084e00c0d030010030342040c14800c02084454011070002e0580e030860b07490387c0c2c0c1c407503441e00e00e00d40c0c40c0d03041e88000341e0700c060041a0161105180d001801d408075220020625203030b4030b65403c1c0b2a58003400c02a41d580e5510b2001d038605242c01d43d0300ca02000020301d81880107003800f0740005d8448 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 638354352 1250 638353102 638353117
    0x611060711030d050f151915030b030601080d020705010c0b060405130204020c011a060403150e0f070909030206060f1309140a031e050708030f2a21010b 67
    0x3559140360141c60400450329801e05007030092105003008401200f1203042510382248004c0e0010801049050040144031a0044a89000102460200d010500c00c0d40d0041c120700305501c4640a10254a0800007140200900c00051243c0021018020b0409840380c016504100010a0002c04944001d5140b0f802070800c5800043d10b40310700d03200303036052010401d0080d006400400c4265032000c042d4003640c10201d81320355010340c59010300c04000b0759104070700004000d45215400d4822445c155801421001c1c1c101e001c40c1d2056a81d10102442d00044c0e500200ca4076071070705201410190304ac0081e0f41c02002c00d840040401d402400011003011450504101041d584c220384001d004461815510b6092004260307030703819480c0d0900030701c0e040386c11056003104906400903400e001d114008590302641c09c941c0c2c0f1415600d070314a00c0203c05401521a0340601484404148810440f000b0680005a40821075680d0b24407174501000e0406100c0c03802240c1603120004100c03500e800012550354 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 638355602 1250 638354352 638354357
    0x11505010206070e0105120c0c0609010605130f090f080c10020403020109060815060f040504050c030609010e1003020301020307030c11070b03131401090c2d062607090f06110607 78
    0x10041c110004079070b940907c120034100c0c4442207050240015001005064182d051015a1040e50303440c0a040e00b42c076058403805811256100920032000e0301c0743d003c9004048008804501071626855503604a4050314099a5408001400951722001080310f98000321007880d0550600340b03035400180113545184038a00c14420749030000303888500c07900c0345503118040041065854003070802851000390081d000b0540518540400704400d100d200041e203208d214000c1131000e4603800c00c201d440b034210000d0216491110144000300c0169400e0001c3c0d4810740840d43e0002e0700a018010052807d02030070301d4007405800a0f64103010000140c1e040343d61160508503504c1c0c21000600d4080700049120307492200035482c0000c150200005039850a0861b2034995482560100084411880340f40b2481c00350445041c418081048500900c00d060190703038400ea0001d0390300045500101c869004992400010720104824005100703103100c4203020300400e2809880c0c0b49020740b40b160f9181e4000c0e100405 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 638356852 1250 638355602 638355617
    0x20100c02010804060908160c0f08060c0717160506040c050108070909020a11030c01060317030c180d06020d1508030a02100e07030f050703020f041406040504150c1101150501020607 79
    0x906c5030340422145850850481070700e000f80281850706464045000b42c2c2521200000001145d04001071a54041d110038042d15103061140d1341c0f40b24580101c0c203a1848101c0341804030407128030002440e2860f00780188050011481e092415074018100f582055043c13048480610401640c02010b103002e4500e9450016030317443d148501940c444410a080888900c400210034294103010342002e4116403044102098140c14800d0a211900048502c5004e0500912045d00c0307044200240d01f0103034101410380c2c1201443d5131074030b10590340701d0448039503140d8036460304070058201205600700504900d005503091145014009403618915801e803512151981180c40600b0790510065004691141d030700800c044070b82c9416911105d1a2005a200700c5900000303031a03c0c1420b0050503d288040020346171a6070315101000010080600159515134201e0092006135800344150311030007803d9154903c40c0443e0660f420700b92400c948542c03520350b400003010003843e40c0001d2150741103401405d2850 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 638358102 1250 638356852 638356871
    0x20070201032c0c0105192d02030c0c1f0c020a09050f15011d0f060d021c05060105070305070b070e03031615060e06060a051c02070210020c0901061b20100c0201080406 73
    0x816400d401c507c100081d8102c1c0346d007080032500080140a02070b010380580340c3c104000f80401c0351004800d410094060004040f40c0b904901c6507280565040c40203020001c0d9903210464941203600031600040ba10381c521041c0000d000c603a09040e44410804d10306101c0a540202010000712020103410740200d0308103800c10110360b40e42d01990b40301d1030140b508640310011030071400e60050200c401d070b0309602d01d09130209003654824401c50780000d801d03444203880d14545559664004200418039000c0150441100c1000e507414002401403101d203148002040511342005415400054030000605103000020050903201d25069035002c03400300c0784580c4561900a0689149c03207405d0030120242110303a0740001c0b49015a000e4a4414020780c0c0c0c0040c90007d000c8140e03581e04c0d0560740903a20401c658010444071703105002c107030050070092404028612095a99103610002e00144400300c044000d60200c15050072040502d0058580c6011000d440c1316400203070000e48003401c040d100350b0700c80c03031301a = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 638359352 1250 638358102 638358137
    0x30d050f070501061a090a0b09030a1e060603060e300702030a0c081b092502120c0321070c030c0f0218040605070320070201032c0c010519 61
    0xb0700174100a860700b8201c40d1883d42c071480030360088200f184100c00200001c6610000c2c241510783d0382038045d0042071102890b031034800d01601000d0003498441c0948185d000010181d000d88801148140350110b5a02004120302c3d00700000711444a06004a00950014600314907031640c1d00c40210a80e100d5458009002081c10106a9403000e402c041c28070f0f0000802007070000322910070503540d540c1002d980800038100500e503441900d1580042d00c4159104c52040d1217401d02c0c0d040c40000e401107400d82da141e0342c0c600100350801d0815030010703080805c41c46160008074a02c0303480e101218220b9079061034038034405440c5041c03522004d010818045c940d1003c01203490b8803110045d030003c0c5400202c0440950300d40628400300d0301159400e0600c2d01055019000e4050001c0c503140d0006e5221201340c0800e85001c0507040040700b64109910361602d036114070701210210580349020f100341d080001d501281c151400801724003c6040040402803100d05d96160020319080241900d44400030003810780b01c8 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 638360602 1250 638359352 638359361
    0x91505070f06090b010807050906010503060105072409030305061e03030d020a0512010b07140616121418011b0801060503060a090c050a1e080718080d1d030d050f070501 74
    0x140071400b20000801d2011002803280108c031800c1341c5071040c907650070004482a000c00ea4005012170350601c05000000c0c0f940914100d0501d070759502c005000c080c04200d81c01c2c2c600011050300400e90720f0080c02840c0c1009003025411030f0040207001c048440c2c020220340d99216105202070420340c089100044240f040c0c08031022810805444095940c44075149103060344000811282d1145642e281c00c0844004180d240c41396403520845c2c6844030711301e1000d50303400d44442e02081082c1c0d0703146044005030070601e0149014402480381400c0c0566014162400c40d24156040010020100d404400d5035038080855419141c541c50459100d4403148049038120941c0c0d0441c3c4001820080a81c0f1190383c807002130041d2814554800e003980545400c004000e02c003410320000021000c1c00050085805204403602a10321003460000c0303240d036080143c2c01c01c6a840d904200043c42c3c02002d80d11046038035504203c03448101d01410003e03600b02e001504e00d100780301c0502d120300c0012440e6014007500b07522 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 638361852 1250 638360602 638360621
    0xd060f1a031b120718050a0605071a0405070305060f01141509030a080a18080a0807030c0c120c090b09011401020703050114180604050a0201030b0d080d060303091505070f06 76
    0x500e10f03195941c9a0a031002000115102d400181840c01c402d002070009206101c11180060284072046051030f404603640d0744400e906441701444e000342c0b03480540781c28140c103200c1e600a4001d081da440c118036107a8140768000d030160300e40380401401413014074540002000502d004450301c403040708141c02443d0890081c00f0095615020308080f20342440f103000c0084c581140c1036174072071403001c007000c0801010003014002d14880740c0c00711031081d0024010900070080c2c01e01070f0030a009c003010150b44101800c4607075000f0320880d20f10038114400300400400390314007800010000b401414001c5001c80d00c00c1d80305206502c00d110100c80200200d900030301c00d980c00345400c080284240c6001d00041280040c05858100c000034510b000c22900b00008140903018951100140051106076001140074090441c0060340c440b500c14142e20020702c03028020480180020b1010441610394140546070003103940c4821001c43c51020190b604941c00400c0b1800240d100d05210221512801c005004044907035 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 638363102 1250 638361852 638361901
    0x70b13150c1514090a0c0b2212150606020a02150c070b18100c0f02040b04060608040606061e20030408100e16050904020301200d060f1a03 61
    0x3482d0402090a400005035042d207005218500e80f16500d84035503400062002810303002d01400c0500c82150080c004089000c030b802002103940e489680f050004c000c03940c2c40f41d1828076020103d0400c03c1480400c848107504514130400c0680d14121000c0e448860303925009114510350988201c480b0070400c2a250038521090486108036120000390126500841074246000100c10140c1141c3c501030070210401c4129650340428034440b507451620700e4075541c90803640a0b803210034008098507680b10310401000c803076807800d51900f41070030301e071045900582000c406c101c0107680031a0603045000c40d007000e00003c0d00c0e002000140441e082e0742003041c50400c009841c0000a00081c80840028904480e600f401070101300c1d001a4280d0140e4682c004120b50081a1021000b04000d20b0800152940980042d001044070100141103080c1122a0011076a148002089007500c48400d03220f840050840c42d031440580c82d0400c12400d03402481d00c102c0000f031020020000c1c202010351003020400c400c180 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 638364352 1250 638363102 638363123
    0x50307110601080d1e09060507080c0303130b06030d081609081b011719020705010f1508070b16081b0303040c0315020a1d0105070c0b0a02070b13150c 66
    0x880302c3c152100101c81403240010b100a071809040901205c54040c110016100c118080d458039a017501c2c16041150161550a01403004c00d51000051004504c20240380b24000407029841c580700e4241c680240ca014000e6000310011143d480d0003417003481d00448940040c1e600b44010302d90484081d00580c0101400c0d0042d20307002d4501e0b490100e440e08030441e0989508580581345e20a001007540e048510841c0d01010751907904403c00c291b070082110ba40200000324a00855840610960f449848035202c144032100c010483c2e00d00600c880b001400004103854540303900f18040c0b10b0718446016001e090310307500290600c41183d10020510b070b000095003d5039140c0c030b0701e405e001d103030580d440c44242d5504020103040796100516100b00c64045003a9103641ca0240b200b40444c01c00403641c1c02115040c8a01008108003103150904054010036440700c58070364032600e03554002e0400d84181c0c00204c140806110b004003072001001168162501200c5d2486400e2516904035103040072840003500c010280d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 638365602 1250 638364352 638364359
    0x6061d0312160c0b09090c070309031106120708151012270305070201031416140c01020f070614010b1606060b0a030212060603010807030314040801020a02100b010c12050307110601 79
    0x14409081c03c001d046403034103442c1da1103801a81c7e2034410204d0080005807507031000c0c0001400c01045141010001e06080c0c01d00d200e41107119440141a611400880c10341ca0421080240d140da001120032026030b424003030341c1c45203d0042c01424000000840003a20750800c09103508102c00070b20004010b6500100e400e00103070401814036444440c05a00003401d1000c803a04e4503080034091401100994941c08030b8001d042003c480015000e8005109050308001005444909002400c0ea0140c0d400c2041c1e0359402030702e01041140c00524040c5003c0b2903090040081e981e446007074451024010526210f1f0001a15100c8010041038002c001280408964031540c250700d0f5010b4404513154404082c0c49072102d2007001031303030f00003441005220740c4031402c1403001a104503e0401900ca48002207403d16855030304150a907000b116100006901001c0491008401801442103506003070074444602000c544406c1d40b4032620320070110512800101085141c0c3c40340c08005c401e000f048080d5045540c4 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 638366852 1250 638365602 638365619
    0x20609061210080106030807060c110610050102060901050601020303190b04050a02030405010e1c2007030501020a0210110904020c0307020d140c011409040b01020a06060906061d0312160c 82
    0x1c01e0b51040440c40542d03001040703150b4141304100580e500030210320304100d0560350358005414864841e4041140d40550503207071510802034070380188610480c81500d1400c0030002032410200502c02159a0306100611000c1e903000310480342c0040c01d42400c00d100c1e0852160500203002580304d400d811602e8801000030541c817075400307140180e220f00c0c003c3c0900014680b05607a28500e6030b50000407030f2090080c0584840c082c01240340d84020204000400c080500302d268184a400d5001b078803d6500001c107951380960500880070007802c0d00744100164800c40302d9461705401034070f180034016a80024000c92811080003610030040c1d00a00d142000d00e51492303c4000d0000640c0e100c1d1140c810100003066940c09050080c1100c08802c00003030134000807030204805014410300550650190000100110300d00780540e0003d032070078040101e221031400c42c0c0100307003294100904c2a00140003c07516400e54003c07508001c0c03880c1c4101c915846414501083c10466a1904010014440382030700040c502c0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 638368102 1250 638366852 638366887
    0x31d0f0c01053115051308160b0c12040b1803070b0a0815030a03090503060a11030c161707030e010801080a060507030f06090b04050105060403020d060207060219030b1918020702060906 81
    0x2000c002845802039901c107d41c0b40d0314046140b010001ca1107000c414041c0c501702501800d050040442150500c150b034209110303a03039000783c016800c1d82e00c00103290340c925a1007038502c81c640342c7c003070b401002038500d421418241c600804482004004106022920f034421400c481840850018155030802e480c47c64058040c410610509009019035000181c41c9903403407041b500140e003403094292540d1748400c19945241d120380760030741d03400c4580031024005c1032065a21410807a80e802e1040e690380001d08000d4000001c1540060400148800502c0441f81c007240b800e044a900140100e80c580b1204410360103800d00e420480185407a1403400280001250050040e0300d40558040006980b900140708040c81a80400303034104030081040800143c599000b4030080f805503400508003880d8054400401c050090701c440081c0c1c4840c0c581c9805c0c604554218002007112801f1071a092510700503114650b42800c3c8044d007140d012481c0002c1d92078183c00c40b202c1d001e004008642c0d03518590030890303922 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 638369352 1250 638368102 638368117
    0x20d1209061109120c010207050d0c0308040b1803010b060d09060b090a1d0a0201140703120912020c030105040302250801022113020a0312031d0f0c0105311505 70
    0x4c05498140d2040007601103030703051004a042e4040c4c11446d00302410700090508420045590720f00950000005c11080c0c40500f025110b02014941e0720401007078595003218280120701d01c6070341b5061280d0070950360703401106c05001049102045444207800d00c01c1c003c020500c007590300011340310108001084103038003e07030103004482e2407907440002c00c2a03100d5480b55244002404107032000f041c19181e904150280125034400d00e030074000c0c10150310f0302c0420703074009541c11110007003403980320488103030140b0400d03040d0f078001e900170000c9180c5910020350703e843e0054030b0040b041911a500480d01031418815001d4841180295550b080d00041603443c0707804a56040c100d02c43c0800803841d8160388182c03002d0102c0e0018418800b50341540c5900c055900e0b814500e0b42410b40e2034009031072441101c0b03401101103440703601400c110030740400c1a0b4280499401254104001080703d400108130f100f20301418180f14034000765412000708200ca040111940140e40c05400080d8a00c20b0b041d40700d07000b000e11 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 638370602 1250 638369352 638369359
    0xf05160201140408040902030414030a1205091501090e0a05010e0a0501180507090203060d021c0201020727050702011805011505010c1101081515070b0f07020d1209061109 75
    0x400101e54001240e040c1683e00411025040208015a4080d0340141d50001c0c000e034452003240c4140074450786594090a42c22010079400080030140038004c0c4641030703000500034068500d1750444020105200380501a03290710300c0d030742c1000c60000002005800b80c0c90358414002c00c00203c0c0841450b90b40d28812400300c41e15800c0103292003903002c0c1c031460b251101d68818020720000d805c10604201940004003400e0b0009141410032025030742e02003c2c0307011000190400440d128842c0002414881c00c2e802007805d0200004038280201c0f040c091003015081a40000101511102c2041340540954045800a02d0b40d92070088240901988841202442e98400800e120740d1a4019114402504005851484c09001002d940e50240322003039030100c03402500740d0a40d1040da0008a81d415804144102c1e98004140c0000f000228150160401e0a0403900b10380381c50310b014003e5941103044c5a00c401c0000c0690f826620511a800840107550b1180d82444417842e001055803541e0440d03000342d4803 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 638371852 1250 638370602 638370611
    0xa11070504060f030c0602030f07060c0e0603040807200303040306020f04120812011a0315010207150f030506030a050705060d02090a1502060a0c0f0e0a080d05070201110d0815040f05160201 83
    0xc0c41b074000000c64036a038031100a42c070704210383d54403050005d01c80b03001400248003200c0c409500c1076541000031449184507101d8251125010f04150f89074403402507080e541d84104403041281c030364002064804903988084050b80c1c0e0180d2075041c004502a40e8481903106012000c00780822580070060071040c01d0b05194220b00341c3e40d8500302c41c503001c5210602d1400034010004140c08400c00f08074441c201c0b03018012600000e541d041400c4030000980309290000d4028075001207986e0f4140a41900800c085000708001c07181602d849459031071074869a84500d0001900051051158043d00c1c183d9900603c581c0c250355030342c00152020302101d0a210014020200003841d003098601c00c1000c0f10b02c40356039080750280920016510556500b035101c0d400b41e00480c001506650402506588440d199211902d4160341d100250035960303480d5401000d50403a003a440315180d805841c040e0b01219005c0401e1140300003002040c02841ca40f09880d506904007020440c00c0e41256480308105600c81d4000c11 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 638373102 1250 638371852 638371859
    0xa050a120b13150f0f0519030b0a0f1409030406020118171e2b0e151e010909020a06090b0a05210f01060e061606111303050604031e050a11070504060f030c 68
    0x419403440c48c04001c1c02585008080340307119985921095040803030384000039120038610307100111540100da21044643c00040c2c180700480d8280245003407960032510401e000040c565541300011204400c40ca4405000300d440240038486804400111031316115490b55421800c0c000b0502c0c3c008039070001070100c0e4102d82c00c00510003502c644607528030f034480035044803801e009600c81038060290402400c44103d482d0013005042020b0821b00a01c0103050004003540b5502c1803007002e0321164060018080000c1c07040000304120001c4541c004414a8200d5a41841c00b4040c07074032a0340c01120070044071000c010000c254400d191107038144c2d01503456081c0b40000034010407185201c0c5180e900a5198030100e0100051156000310401024440005051000c82107a80c100c1c0151588295155070100041c03109150b081541032401c00c0c0c03a0509200b41904c114005099445900403103403c1000212500e01c0a0009000c91805030100030b0091000a95a12072021030030028041a0386c3c2c41d10005002 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 638374352 1250 638373102 638373139
    0x4050105091605010e0108151809010513081b100c0503090f1207020d02060d05070f0e010504060c02121e0a02030f1903140706020a050a120b13150f0f05 67
    0xb1030440f071050f92030b41410094170740115680000500b1400407401c0204003191265203019a04032481c04400c0c102925140000006080d103030082d0840044e1441030540c440884c03032101c1220031100b09071898245101296048515001000c07210020803480d04183c6008564040001c50180c0e22107030480e04071501c1072006030b80312401d901170f05081003410052207006003030411441c410340740010001030901400318900419501c08039030b124001902e842c02064210781041c214615040c00386025800c250030854081c1c4440d000b00300181c401c1111002d14103661004005a07441d00c1c201c9022503240700102c130200c40d9141520003040344280141a10300c11000c0700040c000104480d802103400980c3c4460f1810f07100b000f02a1301035140c10b8400c00038903001c03139003d0000340b1030f5805940e03866603145549140108441400c0c00806002402e18150000e00c0d900c0b078181c201020f4001c000002c003c5101c5011500490703040c2c0c084c14069807c4040010304070220810001100c80546808030000c1c81035024 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 638375602 1250 638374352 638374393
    0x30308060a05132a021c09051e03010207050a0303050105030c1e060a022a091503061b04230a0b31051c021c020312031e0405010509 58
    0x100d6801070110b024054144a40d5000000d60f00c80b09450103207060070b00c00041d04d081500e00c9000002d80e10426107880300c407a9803800314083c00000c0c50000c0042c0e04150000c0c0888401000042e03d80030625070002d059074080d41116821940601140d8a00382c01c0e01c0c002c1d001d480248160f5201c0d00540d0213040c442e040c40034504c40303040c40151031400c01d8400708003007042310b810842c030b500114882c10100039048503207816422410701440601e000761030f4080c4200920188000d14a00c4031040301800d054040d100051403503001500503004809003140c4600c81042d034011548448460039134503904c0c03500351703211000a112400302030354840d6031035407160102c601c3ca00c2079103104440c10104401c1d00362a0b0b20030000c4101d10303607040307400021425030381c8001851544401c6900f071402001c0307501400852404203190380402c00811007a85501900d50000381d02c40e00010700418640c080000003d4000003080c83e0030307901c2c605909401d221810b0a04000780200011101c1c0400c62040071800e51513000d81d40c50 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 638376852 1250 638375602 638375609
    0x108010b01021e070b040906050a09090308270703240e1b010c06020d05060f0406050a0315150b0304061a060405060a030e030a0c061104141e090a06030308060a 70
    0x400c0031000392000f040c64946144000407036802030313020100b0060000750007080104140d450200d002401e00081002103455a40105a800c2c41c00d1803020000b508588442e622201030301651007410282d6503000d030340c41190713047c1d0038a41c010b400002c001c0143d140e076041101c055060540e001d040c1a4a07040041b1807030003052580b036034001d40b211868010728070600441d00c1d6040c50007100702840e680d980c0c0140d820841950910680b580704014160401c0c400441601e542101d0a11036a032410020555040403404050f0640413842c0003202855556003158400e9204410844802c41e900c0541c1f2003181c0007078400b11503840c11702055030841c04003a8812001a40002e00307440c601454a020060380354000c0ca544400d142c1c50302048400341c201800909900c6c5140d440301e90b00315410340341c200300f100c08550341030302482c405010512a061507202a007c2d0b0301d0717080d150f20001410b51407002c2240d850210310181d0000050f010001c0f84003154103c5d604503071180d201c4031841e844520400100016600 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 638378102 1250 638376852 638376857
    0x30319080a020702061e09030a030f0e240912030d02030f0a05040c26070303020c1801080c011b0b100e0702030711040203131e0332090414130b0108010b01 68
    0x4003040150314090f0703007948883e4004051a00c0e006044001c2400c04011f09c000754042070300710300d041e018583c110b4901001e910b42200c0e0802480c011002e080c04460380d2540d4030600407000f180b5400c10742c403410707420b041c02092a42200c1c0c40b42c800000c250301950046a1001007d5482000309000010718011788cc00b071a40040e074807806504000f100c81e012401c554442d0b20700541c00003d86860341050103010041c601039806000c02000110a120340140c002007030b66040c01c020401040502c0003c519042558402d1038561600040d0110315402c030010848080d01c411600428400880c011148590403a8a06c062184156490308401c0e600ea0261220282c10300c003045e5010400f40c42c1550085030720507040c10128864440719281e942007170080c0d503840240e80407107082d440c00345030f0031100113102231051821440290b0040d50241603c800000ca003010101004107581d42c1700d9031142c000403009003000041029500d450340700e200c0782c4050700c0000d8034249001302c00400d0512040c02022505941038 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 638379352 1250 638378102 638378107
    0xf080c060f030406020310032f010903050c12120d05070f03050c1e1b010b0307171c0e090406021c0213031e0f0302060907120b0c03070905030319080a02070206 70
    0x903104c00d0080d5100a000c459074042c0d0000c040000741c0c1008900b0640c80d030000f03500840d03d0b548020903800806940b0018103204d0410000c02c0000e0001806042e030500540345080c03076440020209241c180c0255460f45440004201c500c502205030740400e10030455660307040d10b188400202581250001c0e15408085001000b00c0c0348544851000305000106540c242c1e45000c540604940001428603150300040e5140c44a0010314030b420468032029000c81c0b407a0b07440c3c5800c1c2182071951030144001c04003100c041e039400d5088080c000c4c58100b0140c800540740c115145401e03c0c10307400a5002880d8440c03126030321502c880030710500740309880754581e05090030034100f811074444003504a561034007550390720300c0c4d40b80c550001010111800c000314820380060526050000701d49040a615401c01c6500b0381c94000c560020441100130b0750780200000080c0395498840e034404448203202a005640c043c800003a20420000c10614400c0d14284070350b8449150f6161001110280d2041c640080e5101005 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 638380602 1250 638379352 638379361
    0x20a110d1121190b0f06061c09020301060329010e180106081510060c02010203090f010c05060711100e0307020405060a1d060a05010509032d06010f080c060f03 70
    0x241c1d000b608035182041c0880955103201c0200c2d0700d00484826803400b152180e5020b4020000c1c0d501e4116089219001103070403074540b034400f1034103d002d038484402c1200030310070110401140303030340c00543c9050300135000303008075070300c07414410b042d1000c040184151010720075510028460407400c0da03050b80e1070903000c2d2200c2d4480110195449841c07100f03001e800d55803140005103404c0f0800c0403c0d8440140b240c6000c3c03c0c54171041304100c4400a81c8400c0174800a0425030700140e9000c8102c610301c0c40215690a40c005855004880d55075250328001c00c2d91080905101c0c4194010850a200d101080b084400840039215020700b6207003100c1d240006a442804032100616098110b15440ba030090007108000369601840040b01160680c100b00b1011204244081c0b81804191800506003e080c442e1428403003401099540301007040c1c16030490700340310502034404040c080d01d203a8011048100c0b0200d5841e42540e00081c0e07510300c95000980700d0400d151280c0e0511070182c450503040c01052a0560ba81c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 638381852 1250 638380602 638380609
    0x7080c07020a17240711030703050706020f0f0703020f0d0e1f0513030f020f100804060c031d070f210605060a090c02030703120b0f040b060702060406020a110d11 71
    0xd8066503c4494010036240b8081000300046180d9004041d00440d00303503003000e240c00b42070103010504240003a042008150b0101c1e801c2011070710519072002c00160340e803208044503c014010303080c3d4584520000031b51001410340c002504014140c01109694078111203030025100c5400c00d8400d1604440303a4003507441c1d0f00c40000c0c2180e041160a0500c6480d00c080c0d10070742c212000f00e680046a022140c2e168100c1541030400c04030329211400c3d505146210380000700a8240c1f40021300041245483d6448047d41e00e1103908191034519200c0461500411810317140c81d00c0341e15900a00120110000b030004580300c43c681c0303000c01e101020b0240d200e243c4c600d40740d090103808010a440c1d0010500e400025100c55180301d188682e00d016400b9686540c4a840c00410740f4042c070080303220702420318401a42a940d070000117140b4184c00c5a000400815003008180c85000b8000084d602140228000507001c2d008600c40480382d21840101a08900c90402c001c010700d079882000d40003c00702a48121f440c00c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 638383102 1250 638381852 638381879
    0x50a0b270a020903070608041502090108270303011202130902060a0c14100f0e2a0d0206030a020406020d211e06080d092414120403020607080c07020a 66
    0x120150002d03141c2502c95000c0780c0713080c507140d0100d00090203c10401c000e000001c506010040c00408066107001c0f91440002d01c0d0707020240080000c09070b80200302c00035010300300d0200030051606041e00d840e583d44d803840c05101e031003c10090f80551194a5400c11201c42441800f00d400c0c0d00504030f5041900994044584003810841107413441840c00c0c003002800d80403c84071072002c00d0194081250700d090f480100a494401c2c0100c00c26900400900507004a118403801c2015044903900c200100d01c540002c400c04031022010f5007040001040c070a010155800500c142c9200b038088443d14101c035103046400361103040200e0401c20420255550309041031304051030310000e88030b01c44070403041054800e00b158000e503c118004c1c1d03c401e003074000594121310164000c0c0304000e020784a03034000e1110b40c030609200c030104400301700c0d0070803818400038105c1050b240482d00481c909111441c140c038010b07603500c0f000c1e01c400003c070340404000b4070000592402ca40c80d881d07002c1c0c0340814151400813034080d0034 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 638384352 1250 638383102 638383111
    0x612010506151312050d11010c023c0102131e0b0708041d0405121303080309120c0c01120e0a0f03031b020c1804030918020d0906050a0b27 61
    0x3c42d0400707001403d0481410351101d824085d5015103010420000301400f0036091080581301e80c0d042003019407035180c002c921503894000c113078801859100d000c8816200103007100c850b89400c411100c1c00d5078036000c056001e042c001d94004a003e500ca5244d542d60b08421074041d842124492007290180148681e11001d44006481130045600f800d0710764590307000d21000b01e031030007803400030301f030104030038001d00304070f0400452402c0340341c60704d0302b0004a11000c1c00125408041d100070390000104501203010401102c084034004030403515000150403a5440e130b0009215980020b1042d10b00d02c001102520130b282d01a00c00030000c083c0031950f5070ba01103408038500426001e041c1c0e541c110b01c1d084200d44800c2c444158041e03014150b0002840c041200e14250440c4a0008101c1c10b010000025004180c0d00705403070a01004204031408908424060300c03e1961210549e810440c2c0d10f0104416070308014042c0602078414006603803102e05001300503088401690080140b50300130607003892428040f5422 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 638385602 1250 638384352 638384377
    0x50907031b0b160218160e030c0303040b0d110306010504030210020c1c02010201061706060d050309041d060a090b06240c1e0601030b06060a050c06070503061201050615 74
    0x1c5a41e03500249098000c00754002d8022440a0341004602d0420003904407107603001d69203019414007401c0c80a5211580e42040d05101030030005450584d01005654114240101104e0740c0d981c503001d0122641c0c0002c001155183e0425042c03a100c0300d84802664030405046e034036281080d01c3d58003006601d000c00c00b90390081d4002d0078034054041e251445030120034800c20603403241c030041d10300c00242103850329030200307840d10f0701c96031006140310011810350380002c0112156100080641400c50452181900d070301c3d4424035002407481d0041c0580c455004171503824050b60300da5601d502e4948240c5003403880082c002001c100008a8074500005000c04140003190042c11900307420034010519401707880301c850141c1c400322407500900d040743c00002d00341805170f001c0e00565156940f801d11a140251400c0d10822003c80c00c0b08059208000703544000d0030032403c03030f1000e0810000c040d0040d4810744a05000d500d0340400300104050500070f80e40101c0300a060042010490040100c6541105402c580f5 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 638386852 1250 638385602 638385653
    0xf0703110a03031d0304140d051504050a020907020d0807120902041e050c0c120702010507060f050403020610030305030a0921050d2016050f0a030e0a0905090703 71
    0x600000c10055401c600d84aa1000150710b50511503e4201c481e000c10140c0465100b00000d02041605245020b2031403c1510500c401642034505a82802d0344218243c0412075050100700501800082c2c10440340c1c002e4804401949400c10100e03280c10740e0b81e80c4100429058070129840a210741c29240035442034907000110a0190b40c001002e0b21610418a90700184840c07100214078618414560000000c0300c0305450144c004007074580b614011040324075015008607000056900844c00c403440241c0c0850100104400007048400500083d1070943c0144105800101241c032400d003044142e13601a00c440d8203656607415084003403ca81c2c0340480d11040c1064010410b00c04058890b40d00d00c80c0e68031025100d5071948820310407240d441e100400305020720602d4008603980b04080352500c6142c20000d0007610060b0401501d40000040110014481c810321380d0245540a400e04501070021510320030b07496075600c0003a065800907665807446801078881080028180036042010b00280390304410b = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 638388102 1250 638386852 638386877
    0x503040f1b06110105090c010f1b0c0b1905091806030a140f161401121b0203120c040f05061615020901021005040c2607060f09060806060f0703 63
    0x707002560342d4010030105040091155a04800b03009859105008000520341c24080c2c00008001000d040c0203e024068004601a40a8054040c0c00181500b040b20741d4107041e0b0710140c480c0ba0307034800407802c5050115030f40034460451087d0308a403004100140081e04025071b0030350707050115401070102941407041d00071000009403c103180d000c45501d8540a807448981c00c00e18203050900030003800c007503000c55040612258103404040000c00d11f080c078007800c52020b28031080b0700038610707495070880c0c0d9200100f6542a40d54000010100b204068141e00c5003a00d400c901d101c00360142c1c3c003801040e1010000b05005034100398025210904074070310b1840400c1a1500d40c203080700d08040701c10f0b9001d500022034034034658041249203820310802200f0022442e0945407000140c80600505140f40380384040070b28854881c00c1c01d500115503050a40c4d102d00d81d1080c019140035000800f02c80410400c1c203000890038020240039100309070280180b407601c0803107120030307869500c48913040b410700c681d00007000d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 638389352 1250 638388102 638388143
    0x100b09041d0613140601060210050c0c0f010b01030f020903063d031a2406040e090106050103180b01060e13090b01030203010e0304270e0a0b061504060503040f 70
    0x11030040001e405410364050b564180090040d04c1d0720f0105005074840e000400c041c59000940c3d6070580ba07428800522615030510042c05407003449400c2489128030000d1521050301035210307000c0841d00762003c20a0480c80c0007040141e00400301e216034160000c000007200d01180d04011560120503090203450000260700f103080c2040540c070f04c21300208003500107104104041c0881114545940a00b010502d0b002c841480a5802282c48080d0044140c110314441d0300c880060390040c14250303050000390715007815001c0c0284047d120b01c0c3e0000703040103134481d03030484011001140d030758100c00f144509a0070071000351140d0344213101c45030304540c40349a004c2403560140700f000d13078a134801d5003070100e1940756004260a480314002e08201c03d42040108114450340910500c002c40142c00181500103860030724100203103400f12010110703001c2da83c0300c0d80400108100301380c032905044546582b1400b145580840c80c0c041d42c0030b85804198200b0200b8042682c03100c104442c24402c3c40e0102a8814500d00d0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 638390602 1250 638389352 638389363
    0x60301080105040c06080c070210090801020703020c0a060507021507080d020309030912030a0e090402190e0a0608010b011409031011071104050f0403141608040303020105100b09041d 80
    0x680c1090750b641042c0320030808901620001403c0c507160030100d60030104500020b030711580d103000744a080301e800300022050103869490010505035000315190600d90074040d480b81c5000310301da031080d001c0700400b00300b0b280514151101c10f0780151403801c8458003002042c15580c40301000b41d03040a03003070114446003040d40c00210f1258210102540c2c840404800303020150306002c10381c3c03560750800d0080c15191580900c01460440d03040b00da41d10f035510303540007082c1c0181400d000450b560184880200f01c00c448000382601072654a1010408503640340011800c0f940a954200d000401a40300012826032550140284090007001e48256620700070701141110011020810b000c82c002c0740e45001e01040c1c41540d55101000d8030f0030b20062500d58002030000074010002002e100d030b100319802090380e11b2020f5035800340d0341c00d080383c1c1064031a0500340c0d42c5030010b200c118010b44c20940050b0007046403008220445280450b02c0342000300f002d04000140000203554440e880040d0310103804502d04104 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 638391852 1250 638390602 638390609
    0x9031303060b010e011d0d030e0918100c05030a020309030d0e0c0a050415170f1219030b0108040213180f06050610050a0503103501060305071205010b060301 69
    0xc00040b148403680014014000c80920507042c003541c600a00c044010483c908000340d0401c507441080d4480510f015100480c1c0c480c402c5400c40b0280c1c0401c0312090845800040405258040b0b400030410501d550b01038400b101c440c50b00250080c404100381080303a80185801179440c81c1030f2411310000e0441c100854903d074860719419840701421849604014207400090841941c0030b0001039903038044004038030824450000c410200840140321000240203c1c1403294200013500c8a4407103030a001851500840c84280c041d240c3c0d40380c900d841c00d0091007000c075201f1040e100c00031195141c5e02000315422001d804815400d0b2900400340c404108c0404900e0301c1846071011701c0d40b01d1000d04051084440060400e4010104900603000c090f0b040b205070b6064031038a28000b41d0300d43e42d2111a144403c440c0d8841095500c20302190000000180d07d89e8400358680c0c1020400c0c04051003000e4240c0b5018400a0180d030802d4100703118003414142c451190600440020400c1000900404c032150300990 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 638393102 1250 638391852 638391863
    0x1404080f0709110922110d0e0c0103050105031504170a0207150c0507120501140a0f05060a0612020c28030f08070e090a1d030c0c03060c0304030809031303 68
    0x290a011488880c8140b00c043d1402d400700c20300703000030040070600440c000400c04c411801014000c030750300041c42e000000600d41c80c41246444003144a40304001c0c00081c07020135818050401c002c030032075109101e100c1c1201c00c014020100f00701000740c5a095610090001e40b0141d0f01102c85101100c031000082a24080783d034002d150140c90402503c4c0200702d810030750810450301c11031460204100280c0c082c240c0300c0100d9903580b0701c070003031030518010b10b15680408425003404003040f42c1e88000307611078000416415410f0141e47c1c1d8040800150080740d0003a000411a6040c985c0200c074550380c081c080610000c0100d0740d004195003550811100d003500c1c401c41443c0c02500c00030406034401c2c40101d0003070b0242090300060620703110280664a4105180d40941401c5000034104200c0360000c061020000920503040f4034000201074032940000c152105510071110401c825040000d04036100c0c0a2010350f80341151519070302110380792000342c080c074031902c010301c90205c0300d80540355410001d511a0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 638394352 1250 638393102 638393113
    0x4060b031c02060a0207170c01092f0f010819150314070f1a07030512150a0b0702030303180703051606080a02070c03021212032a0313031404080f 64
    0x2001c0249040801006202ca190052200074002805000200801501c18034840d40ba040240009401445114030242915220f280c0303186040e07410141100320325445007030040031403c5d8402845004041c8001103800150180009500c99444415001500d44610f0010840c0c402030301d000003565078170360000c2d640002e298441240990042100c03034018070601400e001d5440c0340100441101d50b00640e890007620000420300300b0544200211411013600158511040c10040d001280850390040c2882c0100003000010a20f0b2800009880c08154010000c43c0b55540d000d5805841c00c2c0d81e01845184c511401c0c80c08400034ad0240b16131100c42102420044005140030401082480003410343c070200d03481000000301041e8440d5048040c3c0b50140d034100b08000c0170440e00c500e13042110740400e103440004400d0100d00c1003248e0540c0301068115040c00c4003400c4002034803696110a613130108240d214a004540040c0c001c0108900c150300d1815a03a0078540d07114015410090000300c0d0200a4016 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 638395602 1250 638394352 638394403
    0x30f05090d08330a031202060a0f0e03030a09050a02131a180601142203050c01030b06030a0509070b0705010209210307030e190f0e130c0e04060b03 65
    0x8044426848000d440301c250b080340303141c1180001c0b812038041c003200c0c0f5400115406881e0b2607040e82d09008503408000302540d4100c07008000e44400044c1d880304159400c110010810781068051200c00400e00d4000d54990b4840e440c66038010706800e42c00710380e00e00030600e290300540d43e00c24048031881540303100030034106520032590126000340001c0d00e100d9124119803c85d9105102c0b05558414400e08150500c0c03480038a201c50705020710705440b02200a4001c2c140800c02c40c035131800080f288108103c034542840880150240c4049095544e04a00f05000051122807560042a00b0180b141c00b5078240544496403050943c2c840381c1c0c159040c0c0e40004034403d183c1005503211800340c04000080c42d61070384a50351591244515400901045800030b59040613540750745010080307d82c0c1054059203e03030b558002210803149407080e4400351181400044079551080c2902203441da11854640f4280d0601d0844050010040c0090300e100c2e5486007000690749040100703e00c51031840c095040c54510 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 638396852 1250 638395602 638395607
    0x90b1c0f02040803031009091a1e07020304060206010e220609080a1106060a2d1707080d03020a020a06051317031501020a020315061f08060a062607030f05090d 70
    0x10035400b0044181c43c010395234012881d0a0380418030091380d51000051070302d03003110301e001000c420711082035807041d0003052068480d0000001d208484071b42d0240c0741c85a990b100c481900500c1207501800803000c803c1201d465213142006012054410500002c032048203480702000c070b420402849002c50b036548540d40c0281c3c81002547d506c0101110501d8146042114008454401650b040542150b0313821031102552030040c0080a0401207039100f25004907001941d40e161064405c0d003441e80150b04141c036500b0700c01e0003100c01500300b40d0020304000407259141c1d002002e0090400740c20090307590060380013500d0000706010b040c0b1109042502d90401c88010402c1c00c5d0b010680d58107540c451000340f001602d002c54a41c50980410b80300d510640d9400010070110302080c0ca50882c40d406025140000e1a0451640340c01020103a8031011882d48520381664004e40e0002c40007580f101154410311544d6000031817503880045850081402c15140b8191019102c2c117a0701c8001039000710341070850890703 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 638398102 1250 638396852 638396881
    0x30a1d10140c0f030d5c030709060207060806130b0d05011512032a05030304080a030b0607080d3201050f0d080a05030c0708040305060412090b1c0f0204080303 70
    0x4d46c0301712840302c2a8482480d02c282500008a070341c1c804144101131038a200e070b0315032103201c0f01c41104200d00c203045c0814030242243d104554080102d416003401040e0244001208020b0b1a07047d11403407455141c210801c04081c0c108900e8040d5192105401c18654440200707605403588124008203607040e40141400142e40380d074103d0307181c504a10a0010208e540102940c1032035012102c5d00e5100041ca00f040c585058a40d50003a041d844004180300401000c00c00800708124a0b54041140502004c104546445041e001824410062024400b0100740354414118111600710398640000c9810140c24800020302490300f04005038001009941400ca20b048605036044810840c880c40d81d80e1014100e0140060002c2044000300024800000318011107120329004038150352a5666454815034070581100c0494013944e071100c1010401d401008614161401c80e02181e0402c10048028114803030340c9140d0800d4252038151801034140c0030300c020409001da04003c1d641e46c1c900009180e0415 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 638399352 1250 638398102 638398121
    0x2a0b072904210903020d110a0612050a051b0306030c03100c0306080109030f08100f140f03060c030a0e030412110a060512040b0a1d030a1d10140c0f030d 67
    0x100000040c406082c0e0100d6048143c1780e048402d15440c10391400c0c000681141c0c034540383d8001031551030200c0ca5a0b0080c09054030504002c03001d00c210b583d40c1d0b01410a4880c2503694191000a20035501c590368444006180d00c0800502202d03a40d011080c000307850305030800203c803070341581e950000802e181c1c540101d20203050b45c0802845014803d82e4002d2424003458031613410400c0d5030002c1000040003000d100001c3c04c0045204c142c41d0b80300c404040030408450314203480303210b80550702039040c20003103501c61045001e4810f45040d42d40f03181c056000741011010380f51850104010100300e04400c12001602907000d101d06420305078059048c0950303400e030780c1c10000030301c00107004409900d034141d0f2013907903c542d2220107081141c0f952050300000c2c0540310011454072032440d2201c030003004004040d090780c0080d540d070040c42d841200f0800d10f092000c03800d115005003070710368480c05960080301c5000c008100301011501d00b54031620200d05102039a161207810307030000100c0000c400064002d52405 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 638400602 1250 638399352 638399393
    0xb190608060906160207080102030709090f0902010c060f02212a0a0315091e11040b0706090f0503180f102007050d0308042a0b072904 59
    0x11424a0388209580f80001031940e107100d041c0030100d0b001c040c402e0014500400314000295100c0c1041e21000d801c0010b1402000041450440c500109448900411000310340684400d5801c144584032500503203a044500082c2c160200510f076201e181101242541e803e61b88584801420000501a289041d079068080b80003041010315089020120840d808045141000203000a415640b400203208a61201070214075004a001074003102d02c118003065090710000300940007407804540941e004602900460b84000d1000c2400982070f584030340b6410340500307440d056505896a0f1203181d81c0c40611010000c4082078010032142c10311065001050500b1a040003a1691101c0003e00c1c807043d560f951600801c0c21050440007100c00d2000f8070140c0300c0581500f00d411054200a000000305035000c82d8042c606034021400028620f4054208035020381c903941c581445d21407070a00680180500742c802840084540840c44540f00d000680a2204180daa14510303160030002000044c0d01d020154 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 638401852 1250 638400602 638400613
    0x11e0e1807081b0916050313030903020612040b071407060203060d140d03050a09030c0b060d0c060f0e0a0f121106040608070e040603050c010f020f03040e190b030d050708070b190608 80
    0x1740d4641100c00e6941c0a0300890380300f9404400d42c1400c03030b4004803550020b904020000b4002d80040080c16a00c1e22640c001c1030b02c4501034480401c2101d45142c407841c0c64410b000300380070000c0010000e070011904080300525140c1040c8040d21034104043d5058200b00d225031007807840d01e08094150240e10b500802010b000c00c1450301507140905062400c4c040104000c5007280040c0b1141d89010502c403810343c02031885004035072106401b81c00160318001c02d002140c0704280607462450034a40c20300a45520030040058689400503a80c4400c5200e5002c8807205144203850f80f640d16080007070070047c07069030f80e404ca00b41044c00000e4109500d61180c50b000e10309110381800880c000003480306d8181801c1c41d0481000400384400c0f82840074012194416004c00100000d0400c0400350040c0221071080710441c0c0c2a44561030b90b811501065002600743d08110b807403122450042003e1b12009024030701c11498528141d4844500c120100d40411680d00240003c280741400c500c0b605001c2d114000c010305 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 638403102 1250 638401852 638401891
    0x170901020a0c020904060f1505150304020d08030712020a0309020a0e0f0601050901050f0c0d020607050705210c06131b08070924030b011e0e1807081b09 67
    0x400c5414080b00207802142c80002007410810240d1004400c2c0c0b10304a0700b000100d5981004100c20645841510b20075a950303141e22110140d000210390295a0003004c0c1c503e08101627541c10026000185501c003800000c00b2403040300501c41c001000002c400769000180384107644100202e400080c6c11100310010320360704121901141c050300e907401c04000d0800310303180d2210b8401252148109810088d81c5603010800b40c6200c0070000360340545156540a40c1c66a5803004000c0350709000704030015007594000250020b4200d0300081c6081004000c4503054072341140c0400c07103403501c4400c1e030b80d503441d4402040c2e0030380508c01e42c40200226142c0301c0240030303011480d00300303d160346e10a54001c1c04801c80d43d070307588240e4107100550082e10900503151100c143d940e0347e060807641c6881c01d01c05c003070116405c40c400600e101600000c81056412480c80181c854441c03410415007c00360711a25405e03071003841004114460200155110701d01101014296004204e090100d54035000c1e25801c0307100064041c51 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 638404352 1250 638403102 638403107
    0x706030902030c040f1e060509160503070c02060d140a0e0304050102031206041b02030304030e1801060c0510020f0408010b04140f0a060b03071239120c170901020a 72
    0x450340c0860b000300e1300d1701d00c9200341001040507001c0d00405060340c1c8103140c0a81c1c0d0300d4100c0000c07143e08650001d00c5503910480301c8105a083c2d2101c80001c1d03802c20008840501078a500b490440c0007074030190600b081c094101089a0a40041c80203804031002080103610460082c41c80d0960001d002c0d500b060701d8180040e5076402400b400e9103015080c0000640d40345c0b06e55110300314141d01d902c1e9440c00141d811102035260f40c010f45040d4000382041012050303034140003407084003103801d107040f01c42c0c1c603072801608540b4100088800c403a140108150010221907030300140c51145c1c5c9401103942d43d545803400d50b60860f112806c00728015418441050001a071850081c0d85c0140000c00c0b01400d59142100b540007020260805544a000403040c0039000703500100054071107035811000c1000b0b164440220b40c840c1005210143d04280e11854840c410382618800000e4000f0350070010071144215410b6410f503407101070030500284189586408203680e04504903004a004002140380c03200002c4c00 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 638405602 1250 638404352 638404363
    0x503060306070f14090d0501020f070b01060804020904060b0102031902011a0409050601050d031407061d0a020f10030b15070501060608070c060209060d05040b01030203011b0206180106030803010611070603090203 93
    0x2240e13502c00110b00101c66444016410171015400802190380300020000c807020354001041c00d90340c000358240041500c81c003d28900703004540091003140b082d91a591520042d081000c04141140420b02c0031080301d1900d104d81b03403a42400340e00040f49000d000c044100c045401c4000c058440c41c1004050b501003440840c0060550b0410360b05112503012a0409942400b0000c42c4045120f00004261082c400c0301d500007140b003031810040170b02070780030101b04c1c40e580c90340c10f100079500a600e001c410913203207032004d9030703101c0340c00c1509010501801d8880012803000e500200301040020000d510010814203110b07520140c216410040b2403800c10140042c110740000f0001003149074000368014240d0355000c00d80d0030303801300420b080c0024502031030070300d0480c242880100d0096017040b250340c0904400505045003162194000c0c4107680e41c00884990200e1000b50324081550780e441c2c08400702d080c5100440c00b07000c454a60f18056603e4070300301c0c0e00e130050550010b402c0501d00702c1c1800c0140d03004543e = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 638406852 1250 638405602 638405627
    0xa080301090e0f0a0809010311040302030c130608030c241b03130618030207140d0204050606070f21021c0807090806070201090302010f09020d150906020a0503060306070f 75
    0x40000e0b03034082503010b42d240c450030201500051083c43c00d41c2042000000003084030013020b90301805a420300903000002e900680c04002c1d4140c1156a01c4045820b147c10140300c0b40002c01d001080c01ca0340c44440030b0550b401950307000350542044078180c0c40326401141003440309030306200a03441488c202080040500c0d10048000010324000007054604600052020107243c00c544108402c400d4821428501101d021084015000303840000481c110305022000f000f4001a002e08401c1546500304002000010300031548820103000e003e0100b014200c040443d5841009002000c41100124218214001d0198011503224801c4650708902d078050040c100344560501403c83e49400005981d100d6507500301050902c565820008203a605401484002d8000d4008000229402181d0800c0d507422103400b03504032414118801c00a2116900d141283c3c010303440010b0042000e0784c4180503680000102c1001503404001d02849107010300840d904241e403401d0200c411030b1401000742140c8201c0d031 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 638408102 1250 638406852 638406869
    0x206030121051c0206060907141e070b0711010509071202010314070f030c0e090105010c08160803010f050301050f06121e07140a08100903090320030606030a080301 72
    0xd01d00040c9100c40041208101d81c85010b0f6079060011208000c5203d42520789040180b1494010548504040752803034080c1c4c0302e0750390384100c109004082005c01c1e446188da5618114540d04408441d00008024024884c42004101e42d81e04120100400b90944d1048860090749004107100d09520005800d008451991019100c025010b00041e80102000c1402180b8041410300b04400d04d80c1c44418041d5050842d00d040004070010002240c1c140c0e002129203812000c904018003ca41c0101620031100384211002440c040d440c922003d9994006001103414030300200061046110120400c0054507058000304910710381803203901103025010304514018084c545103050108801e00c82003140c260078628442102400c2603019903241e6992050501c180c41d000d0000d2000d00c0e00841000445034a00002c142840300c86410500500d82e80703d040b410f220311060000005251400041c000303000d451080c04480c2071500526050000c0205110301c20f800c03140c0044000742c0c0311405e59056400b0107 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 638409352 1250 638408102 638408129
    0x7030c080d02030a0b040c0e0108010b030c0712090303090e0903030402010c05010b060406020a05060a060602100509031b01020a030f020f071506170610060507020a090510050616060b0a0302060301 86
    0x50814494601c140121114080e0000041100d800d1403500045d19074041620200f0905903800c01c2103030502100ca0203940080e4040d001000b612285001a541042414440a14190301030790b03034010b1200f15031800307000324206107000c0050540106640b170007000c5088626083e868010070705600c03032000400090602c10324040c54018818258000d003c0311101a001c0d6980b40c1d1103a00103541c4d006880f00444540c8240070026445030503070700038442103030550b800421444006502100103404020400d1f101d5120500503160f09888005480e8226034001000594420070341c5401801d8a0440824049540c010840008a09140e1040b02e80407900040d1000401c01c0710481d03000900320b41e03803001c01054000c00540300074450101d01e50f0300030759808030705103240341d0f440c2d4081d50203003e55040a035003c441010204414651070304007036400310400d2044403141d5100c000280039500030100c28403030714032080d50040801c600c1d4481c00c90310b68805c5600a50030b500e180d00181c41480140901c3d140106034 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 638410602 1250 638409352 638409377
    0x705040b0d0605031603060b100f0507030e0d0804260705040b03071208192c0d0b01030303050a0e011521170909060616021516060204140a0b0703 64
    0x1542c442c2010708001001da030554281d450080e07a000c003407404252107403840e140413050740d07140c000006008850a83c42d0a0003a40c40414241d4860b04000381c00e40920514a03070451590350b03115450310360507100c0c8030082e80715414034907081c21000400b940c00d42e108000745c407003000d0108e000a0402c101d807000c603070101f50000313800c0100b401c04080f58032103800076400c40f404104002190001d40900406200711440e11104007400310f079440e0002800030880c07c00761071020203d01003009200000300c0b01a040e1003480000d0303038900344202c20903403040d000a40d4520902c09000030501584a02e51245d80c0240300c104010100010000183e115244482d40958a549481c00c00b0300120462076802c408410303441c50300d83c3e80640943c2d000b040c4403842105d0220001e0300e46d14100303055803500b0000d80c1001600342c0040d801d0100d08480045004440300041c4001c14480c115940070b40d03501d612a01001d82c0317440c50820210300d0104035143c400d21803518044280f1a8100c00015030700d00c07540500c1d0100d184000c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 638411852 1250 638410602 638410627
    0x15190b0a030c08040b04111503091b03060c0a081b18010906112d0a0f1502030f1303020304410d030f0309060c081e06130b12010c1d090705040b 63
    0x507040c0c0c40f00c103402004001c100583c100810000c3c9400402908c94bc45001082c08158840c0011038492950100c180704c4440c00901c034510003175100d13901e5034414210101e00c0c41c0810054004184030411148022800c1070b176542d01422010080c00203007000c0c00c00e02c5980400c1c43d207511001041c007466900c0d001c0758040c25182008021515103285013991010315190600e00911640d4002c19103040c041c00d48000c0f05802030b0f00c2201e2281d14140e4401c1415200d030300f160041c00c00da4200980441c4008d000106600d5614610341d807100d284010410842d100d420550301030b610600511000500400035421403a4481c100c0907032000354140392100b10007584010940007004810300c041d10300d9292400041c01c842d0010141400703180c45c010701500349039100c241d0401210044520316084030b200c0100050300c00c01d40d003210038410402090786c603002400c260207a084412080017400007582d031218510000b410459003030b030440c4041e80d0f40d410300c0c41d00c140040d10780d00c114400d800c0c2c10714001031041c03807404 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 638413102 1250 638411852 638411869
    0x304060311070f0302030c1203060607060e0703020618041503030c0b0717010e0f1303020304060c020604051c0c140105120601050d0507080610021515190b0a030c08040b0411 76
    0x96100710759003c21078450400a599400a0303000a18512030000982040c400c207100381c0c0e10400b00140340d079180002940c0c03030001615014011070442d1003808000300041c1c1d13440c006003021000f00d4103c10b0840c20060204000d40e082080304040d500740d4180248003080d4800513811a542d0802004496a114400200d943c0b4003e401700072540c5503240c0001c03c2e50359203e800d0901070640906040d405071100c20540d0100100d0410040c0175910401c0308000d807500400031142e0140c0028022030810740c0d04c8001c1108405030b81581c03080750b86070080102c20010500e11001c0601040113000101640c95030001e03140d4402c101325041c0152083c80043c0701c0780e2080d030440b2a14581c2002c14421401d005d1006080700000350340640c0b14801c011440065548001481c400f9000071202c00c1c10540c961900001540c030040342825040b00c0800c1e603101c0c400301c0b2891880010059081003030b9980031003007001021605500b00e900204804c6a09000c040390b1041000c0c0c1e0442d400644644c0418039030030008140c107 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 638414352 1250 638413102 638413117
    0x206070807111201050720030c030d06091b081906120f030e0105071a2a0a0e0f220e0f0a0209010f030b18010b0a081e060106020304060311 61
    0x40400500a01003025410110380b90700000d0f07034581114007586403954260f64040b01e0b040000780c014418860003400d6490040c54400c017007402c0d00d00d48071324003050a0a40d071100c3d41200116884100030001c212292240c12088515a0261203441c026800d0040041c1d0300505803410708150301b00030600c010b81d541e100350010035036002810a4007000340307440302003203e03615029404100c80c140b00c0708240d4001d908603140075502c104010901d04e189050900c0024000e042c1030f00004000f0b0034032507230fa00f4035503100c4031521074800c01c186c48011002000340384010b203445d514095441180c3c0c42203242c0750729611004000e0001207844240c4100c0404d0001071800703c6075184948600020b00f0400c030700118210150a00942d403a44440e038071450700803d00d114034440182844450000603a170b140007402d030700300888460400030440d4004440016011003460b0003135405508088a40f2003411041100c414191503264042e1100c4d6140c204007030344a0040d0310419040c582c03a04840000c240e203c80484685 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 638415602 1250 638414352 638414363
    0xc120a0906050d2304020f06040605120a110307020601080c03030403110607060f1a01080a020910110703020406030b0a05070c03090b1803070b0a122a031e1a1804060504020607 77
    0x10713251000503e501c040001d032070130380c010f0124008410740ca040890441d4266001c4e5128180340c03e90b107038243c4c0300390b16000300b001c1c003195074420f612440b120221006500900e0580c0c020209941019606414084e04c0301c005d0380b09610400c020000504807035140c002048040300c520341c9a00e41820310902400000c00e80c40101e07441c1c052102e0120401c08642d060680007a030f51044140d0710213105100305d00c1004150f0f688050f01829046055103d048440c00c80c030000d009942d2055541e034041000d542c81d5820484800481700c041080f204107501c6102c4e4880068540f880341100c5549018050131964018900c0e4000300003a107000003042c04955441d850f40103400c032038601740d0b1144080d0158001c4208400003803241e1400381c000315498021850451403000e481c1c810045c0d6203004501c0a20840145400d054850640380e066868200107003501044002021844038a840300310300340c4500c0071007214841c000700840c00640e1006005c0c16a031150744800001000e0319a400010721038058100d00400 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 638416852 1250 638415602 638415641
    0x30204110d110d150e0c0304050a1707210c11151308060c0403051506040e100603030f110c0907110f010f0b0a0b0304030c030908120c120a0906050d 65
    0x40100c001c40040402c5410720500b00100c903c130070405114036603140304039072921038000080307521004004d00031900503101740c0440750300030020780e240321740301107070755a000345541010886105108030300b94402d5001c80110b0300c6e441511709040d0301400500300c20038040c3c24400501c11003041c0d0740303d00e0140415500002440c07600e6420a003050003640c042406048168091000814065603c1c1029502601d600401400c3c5d040320561403100b1401c1d00401c0d156000fa00e415070303400300300400d20040752041d40341c82c0302081c0d41d4210b050181a00c0c44248905081240b440400c0707511b000701080050a485040b24030310180c0e1545201280e8843c8030f03052000580c00748812a081340fa03015440b622140c10030038403e200c018444400c100000c02d1510131074103040030410010b00068803d01d03891503000e219080c0b80d0354040d02c42c0c0c0c107986070201c040c01c0341108520000c2c0c1c0c0c12164104010341c8114840c84d402483c9086845000100b5440e4a80b01da14248040481c52600041c80d580040120403890400c000 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 638418102 1250 638416852 638416871
    0x12030e030c011e110a030504020d0c0801140106051303060b033c01020a0f080402130c03020912060601090e0702010e030d02190e0f061b0a030201151e030204110d 71
    0x24024800f02d8400600d20103034041d502c0300702d000d0b070242c04d2220140c140e64a0600517080c8090703016090050040b44c0c0700c190150b00800007100e03407004101410180b0000180e1001c074041401c6185810f800800034014140225150031080300c0c0c40794240ea40c802804206544fa8202080c80c01d0148903202040040c410404003a40d50203070801d5001640500150341407040500c500e500302d100341a100400180d42040c0504141e01400103250010b20141020340303004c800300120f01c101c0d808044000d0009030000345040c0a403519100051000210301c011382420306115001a003041210b1141e0714400d081000010a20781c002c0d0b0001c11200140c0342580d40d509074921201000394081c800030380fa40c2c04011142c522051042c2c0c60b020f181032000d418000c0780000c0d00f00704480f603000111480080046005011000c940038000020fa04c0c2c0f09400103d070958040d040000c507030f4030075003020448088044900101e204101c83c12021690107840005448840d08403680700c85c0300b20148007104500b000c0700e15 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 638419352 1250 638418102 638418127
    0x1a1c020304030f080709060504150c12050d060519050f060d05040f1703161b0212030901230f070320060129220f27090206030412030e03 60
    0x222001c569992540c0440d45c40040688007411640140341c0040c05c1884280580d0031528503924004100d800e00203121000d41c0d6803a0081c411a01c3e40c000001c3e008116040ca25500d801800007504040311000c060310128001c0c04803400e40e0707200b414800c4241342c0140d2100e41300c032402c4034404201102c06009a260a0038031070b240060008040300d018000082080a20a5890540b0701801000490984410036070400312200d481c040715645540c0c40300d915540040e078071880505510451400070795242c203404000074180c00003c400040003111103d005804c0481d5440440300004100c10206440f41600e007000c0303070540306c1e03803006000c0715500848525240c0340c0040d0b031030b04030380e901a41c100380d100e5480e000310a668000d0200b160000c806004c11480140c0800441601c0205200d040380115603504103002c00d0420307607000040501148082c910080400342800d800d54a032080180b041c03208a5000c02d515110090025110500c11145443c09900c207070010f0318000c500b4400c4949410b100c4006 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 638420602 1250 638419352 638419367
    0xa170c0301061407030c0f03020f07030b0108010501061107092301030501050f060f010906050309160b071e110405060d05101e14012916060b04061a1c02030403 70
    0x2c41c030119844140100304200c1c400211241164540e48400802c02260703203074941c0100001d030803002d50051001540c2505000c1202d40001c50144002283c0c6524080d851400c40d10184c203e002001100c05410165920010ba41000c0703d00b00b1100096030203e40c42000c10349900808603a80c3d17009d0386400003040c0081500010b000300250040c1c0901500c1c0e40080111984c4402d4285020403280442008814002c2c0c0203594080812070986541079400b18000f8000c8140d5003000b4400ea00204006081c859a450740107800084180000080c1c64070391141c804100d180c0b2904d520440d250300002d003880d00d80481c2452000c2c4d1000c104c8008036110b1507074a0140854440503c0342c845555819168660340e40170701504400c200e501c00c10140d081155000045178250b0790b0710090618034440d441c0d5482c001c03004181c031903000d980d95043e40c0d1141c5000c1c01907580925034540f040342440350611004e03400240c415407140329002e41c1c1d0b9076140d840d0740c500c144800d21080420901d201004110901d03400c00038 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 638421852 1250 638420602 638420609
    0x703060c0809060f060a140f061909080303091f0b040614130203130f02011701030c050111150105040c0c02061c050f01080a030f140a021507021902060a170c0301 71
    0x15280d2550b00c0c20a20030884c14102d072003543c41100110108a020718155481e160640042c1c1640070b0a243c080220f2016404203110240722006144240c034215440040e02002d481c240c40074502e14103040f0092980c0f017039140d6107d0080c591900d800d40c0c0081301d0364012804824041c200740200751380e0710161016071504038071150003012001840408208280700b1684500d40c40800203084000540364044c0c04c06645104a042c00080b08004110882600d810760007140300d56045200c140c1000b0004041d100c41e81400a4a540496103d01c410011021100d05443c07055400040c46403034048103c0c1c01013207510010350004bd001030105010560800c46100000e5408424005500d46070b240010b10a070911405903250022103d03140060b10030000c0f4900b004540c603000a0b8600b00a0b000380c0d03e940072050354005641720482c3c10071091984503041d039109400e070014003001d0002d00030400c020341240f10300078031a0500042230f818050103006039080c02c08203440c0c40e03c6145041c1810217a42d40c420301 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 638423102 1250 638421852 638421871
    0x302010e0705010903050616030204261009050a0b190216140f030412020402091201020706060e07050405060d0609050712151a03182a120303180703060c08 68
    0x104003250550013000d8034411260301070004c152a1b83d45800b05640c00303800300c45407c00c241e0200400200c1d101c8160030421140d03100031010b114150800407542c9401000b1070050031050401080d903010400100c1e40c501803035080443c140381030381c0e02c05880d01010122900f10b20003a20206003c150200900303065010f2030f108107141c2c00c100c40b120111541d038a0740c0400b0440c4960080005200d80c031050b08412100350b10140c03015007050342d8140051840c245404909940b60350215103442400304600500e4024110705074203ca003418a2440100349106034043c45000b071800054407513410100d0360101000700000c01082107a81885040240081080c4240f4001a030900380140d4100718044911001c0b146e210f210903110700c4110300c0381740031b640000700144c03e001d500541e03441500005100c81030094043c00c440c41c24101c0c1c2140c03407041c200300b1040300a015501c01c04400090b46800821690040ca24500703d00e014068000c0491600030545c2000b0300e00313810003400300e80440c2c100e00020701030420340 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 638424352 1250 638423102 638423113
    0xb091b091201052d090c010f0212070b2220270f0c031009090f1b05130b030a030302090a210b06010e010e060307020304120c050a0602060907050910030501090302010e 73
    0x9981121500c00340c0304490b0b0354011b80c206c001c00e58020400001103403041d0040c6e40328002004604036854001c0305041d15069000c1c010485e000e029010903c0c0350000f400081c070b403250880c3d10368100148040070301072040c0b071854817946500d0760780d40c0618006800405400080c600d9035090441600d00684207458540f041c400070464800044090720300c200d4401480141c5542f070684144003400e510b842c1503421520780d420510225038502c541c42d240d686003d0038041400d24200038000d054841c0340d50b44840620380b41d00340e400303aa40070490407112509071030056110404c190001e4107103021036122503458640c40602d2407514200881d42401c981c0a0f000c0130701d2950745da0006444403005013500300e0000c0c80384075913a01c403481c08402a640000052040702d0402d51505084011940010741c2500c540c5c42a8408100c1860200324034009040144040c04603800c1054800c0e550312410300030b03284075420503800506a61900e076600070095402c20000d0016003c1410041c0c000c008000741108c99000b03c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 638425602 1250 638424352 638424421
    0x803180604140f060d0e0f12070c050909030f0307020606090a181b0b070c0302280b0c0c1e030106060e03030703080a02160305030702010b091b09120105 67
    0x24064400325400701c242e28007040620820022681d00b03502c401e9510900601c0030703407000402e503c80c800c01031101400038008149000040780c43c080c0c0a0b808807050440c00c04c0031a00080d070844250013140c02c2900d03005815107603003400034110b0003034001e0394034060008401c01542c140e00203500c03030083d0426110305156071242d003510402e803520841e0594451840099120004900b9001514034001040b803110001d0f4a40f401ca00c00b503031104500f501e002444101c01d0041d80380903220800308555070514400080503910603100340498502c102d008416000c0782c2c030700f140f14007408102c15103a0028011040c0300b480001e0b01c10402da5080a040c0250300c0c2100c04034401d030040441a043c0c1c2c1000b4011414071074a5a0122000e500042405003529004e201c2d5450340b26000540d03176444c0d8429140c541e143c0c40c002800900b1a004070003a40c1c81900b019060000301c41c10082c240020481e00c1505640c0c0700c01d03400126035490f501c03207080c031910340c0b808040041003d8400d5204694603105494000e07401236 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 638426852 1250 638425602 638425609
    0x60308160b090d09031209030b100302041a100f02030d0903050c1c1b0201170103030f020d0906120207020f18010602102a0207030501060605131d0406050601030204050a080318 77
    0x200346803d00440c0c44250280080350400e84406500c0701c442c0340004100ea204d54800c94036013025143ca20b0002c420110610461400e030260424032101d11101c10981c034841000240c0100c41409031000b401040322541d01014401c0c022151040d802180a0080303035240c2c0f80040041c4d229020600700c0740151400b00741105018080003001d911595203800c17080c071020741030000482c040d480481c14018200d5594140b060000d20302802540241c0fa02c1680c90001d0b0806804d0071070203480c184c10056405400d100c2c0d260012000515039500d6500142c551080340b02040061036084909640038070f49046603030345034200500c000c2c1615101d07400e59400317242502c1c0c8003003962190000b03611b08400794482c10300804030812074031440c142c40f84111000745e580d9484860846805400c10400034000061900f8040e62440b2404010500680141e001024100284444801c05000240856225008180180c0c820b405890251400400c0400c6580c0c0d5044481d40d00c8d80080400d103590b00120750403112524 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 638428102 1250 638426852 638426863
    0x204060c1403090a0308030a0f050109050901060608101208090910060905030102130905130206120411090702030a08190e07050405180a260a020c030c030f0c01030e01060308160b09 79
    0x5000c0d1980407a11705560300c00d0200d4200503c50200150f03101c115440110590041a00038043c01800060307504011402c1401c0d10600c0e00704000b880422014000c8003076507881d0700340454465403c0c0c1d45000e55540307000c40c2540710f1040c06542c082c51100034080f222851841e100c080b1403043e103d25120a80e80ca0905080c0e01541e1402280d0082c030710310812441801d80c01090340490054110708000060f0f50000c2d5403900020307201036071207030a00100400c02002c0c0756907182e0444201e80c547d80520384914001e40d00e1052041c58000c0104650100b459210011500d0b00100890a000d00604081c03030308080c2da4024a2099900c81d070b0920001c15040000324540c40a9090354001600342c0807500d442d0a0180300480308000362403031038460703e0001e1a600e00003414401c51103502500500201c44109458651502c581611980049103080b00014000425504060b428240407542c4444034441c0e500402c0c1c00d0340054003c0d40000b810110171440100d040c1c0c806440b404145205444a40c086560755 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 638429352 1250 638428102 638428117
    0x1e1008010b07150902030a080d0606050315061308030f250503040e04171305090601080903090f01050f0c0d0807050a0c0b040f05070305010f0b01031a010e01120204060c1403 76
    0x4804004000100303c00003004070300f81000c00804a500d9980354042468150b5101c0243c44000f000324128401c0c1240f4000c3c000100f940e072418030304600704469540c420b106002021407090b140001c014449041c0051200c00602000741230742e4542010300060500343c1c0c400680030984250740c884100c00c2e44031203081c2a509541040041d4100341c1000f1034424201c0014101380c42480055403103400240b8500c0c000c00c1e00080104104a001e46803105204600c80040c01c0681440880e201f0030207820b80c00000c1e00e001801c00c8a200c840900c2407001665240f1a0701100700400e08000761302d20848000061240262030750760ba4144842e680c011045840d030107903c0c401400604c4215010b4003141004217580e8100380180c2800c074209009641c0e082ca003103210b41c0122000c2c1d44802103c00032103428030459044400c00c2c201844039500744002031108004201e01c403418480214260502640304010b80c0c080d881e0707030340011552181c40703182c080c2031442c0450088422007004821000b100c00e0200955010 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 638430602 1250 638429352 638429369
    0x15030f03030103080f1e071217040b060103180803010e0c0c100f0f1401050a0b1206130b0a03060516090b1812100207150b010801060507111e100801 65
    0x19a403d56441040319408913a9803c1482c0c0184450384005180d100180c103d2080c0d4035103d43d69400518200c0c020342c4000c050541031200e94500500101028003069500603400903031300f281680c2c2d0200580c002c018010f4440400c815840303c1404108402d80154182c0703424001e41c04990303581c1c001d02c0080f840b401c1301f030541d1504130a800824000d416004141c61401142001c076100841003641012aa03900c0035401026481c08010000c500b05142075601910100707049a2920b8a1983e01031415000900300c4c0340584580e20070080500c0c12036007c0e0094450007020b0341403a540c0ca04082008c2c0506a4940f07103040c1d00b00c1561043c040c021400b2100320348500036042c1c1017024a0302503161a0309040e04240e000b0b03498000d0212584170a11031045580e1440d040141c071118030b420025012120701000800c620b03e01060305056a800400d014112030b1946880c0d50340300c040307142580455041185460304040d42c1c1040e8815000110380b044800c5505a40c0c2001e000010340088625010a00c1481303034 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 638431852 1250 638430602 638430607
    0x13803060c12040302120a03050406110405031b0a05060f0a09050117010611160b040f05030a0b04080a090906030605011d070e120703051605030d030b090a020304021f030515030f03 79
    0x40210b0010b0803561003806401a514151440c07068403529031712687d50440002da0320410401049000c1c0304035407514130900c409508041c20a40469a41e50300c00000601c0010803854801280e56141d1408018250141100d40c4804403c88200b040f42c0090f800340002c11090380c000b06503540b0503080400c001032001145030241e4600041918034070090401d06403540541030240303101c840b0380c60031440203181d0850b03110fa81d1490489140c0c00c40600e50003480c0300c0d400281070600410b0303001100c01e030025088001c560f174403c00e1803419100180c4942c040710000703052482c000240201d0354031590485200140b0011f201ea1002024220f4100481d804070100f9000d41d4100854201800b0460344a0310f01c004484500e500e9407911840c00458400803100348080003005d100d18201445a650301103024241032020a52000000d80084002841800c0711031740440002d0540d501c0543ca1121350000e0301011a0300c1001e000003c01a050481d004682540d075034912900c40d050000316130484a41c0d4401450 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 638433102 1250 638431852 638431867
    0xb090a12020a0e0711060411040612080a05030907170102030103030801060c021e0d060f0504110a08070513020706020d0b040509120702040209030705100f032714013803060c 76
    0xc40448016041408020720030194400885e000c00c2618011401488070080340104e00c0c04010540d441c0c0d411802100c50741c81441070015180d0340c01c0c2e038510842c0d42400c42d166a00e54099914129003540401c10540c40009651504031041d170040d030581e8000e079a1084a0381e213900e0142c50440c180800250071142161005651500b201f0314841d0340c05000381542c21900480d1a690165201120f00207140c0e40c0d9017003440100142000b03da2192042511240c18461820081e152078401c50310559004440c80402807980c4c2800354102d0390401d602000c00c54403000f0502024000701400c1d2000c41c050b51512011541c40000040c0300071500c622010a0380ca005425400d00001c1c1d0000c4040607058441c0800100e8160782d182d5680e240c0c0003140d910344003d00d4406000034141d41c0c40c1c82c0b46107102004038420f2034140c00701c0c043d80a401500034181046444102000c503004000d07411082010204c03d268014910400038810188588480404030544184600301074640c00f090311224841c080800020 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 638434352 1250 638433102 638433119
    0x5130201020c04051f030b061c030503010306050912030109140105010e03070b0d025508060307090203090c0114040b03011707050d120206070201060803030604091b0b090a12020a 78
    0xc6620000c00c5c0900a18084450300080f4030400c150011503020549108014040c2000c3d078840702100381202c450390b56004140c07009400d9110600019000d240c96000240400404000a60410700d0300d0700c0c030075601e40e500d260450040c0b580703034001c1141a0113440001495032040050913032108000307024210031881d150f04d0300300340e0b4828030200d02129001d12000b00600c9040c07501010461180d90712101038420024500d00d0320568803090144106030202c00c1c0500096820b0b14100da242c7d030b041c010442d841d03c40010b071a114080c0c2c84400494000010040301c44000304000051503800c0c2c03140c5110710001030741c42030b031340c01079004100300340006200410054106c08070941c1004118401e550307440383c491011508403403050a06454081007010032082407541000010740c00141403000b080717100d080803800c1c1d4682c400907007201e00c10764481c82450144200094001003a1816804260207255260744803003068124007102442002e010b1400220340b4003403658030b50703590342c01030900c1c1840d0308104e00c2 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 638435602 1250 638434352 638434361
    0x20c030304082814091507060507120908030a0e0a05061005030d0903082b0e030310050904050c13020d1803270902070305070204090f020a1208030a2d0207050105130201020c04 77
    0xa0541c84005031180f080406c0f090001000c003c0c0c0240004141840c11203006002e034490940c2100e01280b400c50f1140c041640002565004040c010003c11000308030f0740c6162501059540180c100d000c0e42c2d007403115070b40741d50900d82c0071601d01364141c0340041e09011050318000d9107840f0107424440300300080728030f5904010103078000783d00c0314860940541c4044100004c51340900d4180360503030b00000920220601020010009080445205d02985042c3e950161075506081200d4051a00c1c2c40f135103c20b44c2d81640540e5042040c8030b40400c0301c00d40810380ea10041040200070b401150507000031001906000c1c10444000d0140c041c1252030300c1c6080c0000c3c00a42c441c0d40e0507804c0007802c0c4410340059580e80103002001e07018400703444010310390b40100021a00380342c0c4103140c140c04c05012040000c8921013645d601c101c889400081c84412819912555082f104080214201c2507904641080d090b5000d170000a00a10080044da0b5551100f0008041401c2000c1d0150b804a84408502c1ca00b9400c0b = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 638436852 1250 638435602 638435617
    0x1501090605070b130f0b0c0d0f0b100332061009060807050c07180f0609020c0703231c0f0801050603130302010b030f01060623040513020c030304082814 67
    0x79802e441142c01d8848006d1400103450008440c2c40025000801c4c3d0158003c04035001c41501c02000400e041000080c0682400501c0105040c4c82c0c41c1c1c140d0144094110b000940d218403800110075500c4030000311501d0004443e864441c0e0300c900044c80700c842c800c140e0350081e20741d180c481c054cc540311800251090703080104407000c58482c80340045600780c501b040c1595841c94040020541080c100c480b0303015180c1641214502ea44184540b00f9000c100041d60070440340c0180000360390a030440c180440045001d0800080e9210b05050007507002c0303c8030894402c01015603101c1880c2103100d10111000d400a2164075404281400421056500b5400c030300b034814802d0000103040100180828141004030090308916552900704200f01c1d1341050500302e040c0c42880006c8040c01074500c04200d54000c0c1e02030300740600040fa600d81422000c65045405100b00c4800b1a52280b8042ca00030000fa80086900d000440c201401094060400c80714030a00503c80e48410715a03e001e0305101283d80c11210 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 638438102 1250 638436852 638436863
    0xa050913111605031c05040b060301091106070813080a02120106060e09092409240a0b03030d050a06150305090606130914031317191a1501090605070b13 67
    0x41285e020700c088000c2603942581780f40100e00c80c42c2a0034260026100180100d010364140400d2000107140042d418031048411240162103c2480c2454034440c040d00314541c5040041d801c1c0454101d40c00220b5032403440c0b0031191111802e02501d4290700303036a1544500000326160002402c1c0e9481d101850355031201c8108101c2d100c00d01e01c2c2c440019008544840e060303200c0150021300289104c207000502020b1850303110040c0305403c0c050120b0201d08014812900030f80e903200b0f4119035a50078022102d0040c40032200f48414246890403000a200da4461403419145101c2c0540f031513030080c06100d01c0b03810f5103000341c100c50b6102000d01c0100d480880451041d9560b036640700000a180c4000982154203210086484005410a107000c0a003540c00c43c01004020010a2206650010b90401e012450012001c00ba070035903d8051003200c80d50085200103104401003011218a03a02103540161099071000d90081d950311098400b803064a0b4003070002c9a1300c0f00014120b4612035013040f252032040c0d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 638439352 1250 638438102 638438107
    0x1060804030525050c0f1c060e03190e1234060e090709080d0f02070906060f02070e150409020312030c3f1003080a05091311160503 58
    0x204410180154580049000f1041225406000c000c010900d484d0b40c09880c14049541060002900700480c00740d1266203c41ba1040c1034204070064000d045108410012a1340301d0303900c0c030528413503458006000030005881e1103621141d841c20314001c181c0440846c1c041c000c03c0d60040000c0700c0c812030703103c1604150903240c59550350103407882c1c00701d1005051030381da502c0d0940362880400c401500040e251070200200c0441c2841000e01c040361410141e01c05044c102418801494142c1c10800181e205031402803405c0300c0040c18503007004440a003480258203070f81d01180c8074800104c0400d0709507084054240140100301c0386050581c030454005000804480681032000780c0800c0c1a402141c1480c00f068000c5025040040c80e11750b4290025512604450b04841e00b01000341c02c01c0b29200d440703400b91411804225403110024207032010b180c1103204580ea6079101c2c0c42c054010b90110380400d0003101c41000307882c0300700701c2441101c0d061115000003a02d080a2120030014040c0e40000580300c50004 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 638440602 1250 638439352 638439367
    0x170106060e0f0a051f0305010902030c03010506030712060303120f0c020709020f04080a031112030103050a030c030e030a061505091b090105040b0d0504030306050306070f32180117010608040305 85
    0x300c0070b5002e10700d4031003a4540783e00c4114842c011b05a42041c0d01070380e401401401403041038a0240144c070305640c0c0a5502c04d890303a403141421a03c1441001c045d0034803e18000020090580c844c80200600240304400e019101c580e064003001c4a205540503001a0808e4109200822080d00201180d1200502c03590625803120155410104e440c00304502084002c0c0c010304081f44180040d1000c030300c600310074a04641c51500c803140c07503480580008040240445032541058042c690360740c540000074003103540c400900d180c4135000b407911400320041001c0321080094203151031165148101c0c500b001e85180041b481e014840d082d0400e00e6100d041c40401d000103d100010740c809054854004600440c42c0e04103414094103c0e40203400160180d00a2000c01c000a5044941c040c6c02462501d4046a50402007082140c1110800707c071004483d8110015150302c004a1f021741000281c034850b0345902d07a14003006555501040001b5495401800010411507010303415099015002e42052454131a0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 638441852 1250 638440602 638440609
    0x9060513080f0c030c0108010609050105072915030a02030a14011409030405010801060c0f0b0901021606021911060403270b03040b070503011a030a0b03070609170106060e0f0a05 78
    0x1d01050030700d420340c01504070603054a8100f00f001e101740000c2c2170902c41d550400c000188120300a002d400d060010001e800010015040a03a4030080c610059840529040d0500d545900005a4401030003910030000e5280074680880c4031150154007e0013001c0074010360341d5442c1c010312150f800000301d5580e00c1c54103011411740700c0010310803120b0300042c2d0396480c14240050070440c4180c0000040110201504000504107050121003d0b00541d04021907900e003a00c49001e442000c2055400504007111035040080035000740c84a2020042501900000980d04a8041c00c4084040245901032000f14001c00d0103031001601c803558000c3c03881804403140500f0040c80159074084404034030000100300a000180c83c040d50080241d1800310b20f15450290a481280710b00e0b1310b520711814000020442c056030940c08080e99a9001d0196811030703035151340c0904000798074440d100500f0b104c104407074403016040c4160001d8030b9030f075114980a5a4028144a94840c0490301d482c0c1281950384045a80da9 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 638443102 1250 638441852 638441863
    0x90109120c031a01081b090711010f02041d0604020f03070818150a0513170a090918050f0109020604090b130f020c0712120f05071506030b090d0906051308 68
    0x10400a0703d00125490400300301c0c5007442240916140007080f0040c1941944d800141a4103e03c161038103a20b410200d111050042c0f1048401074142d074400200010840e8191045151002d00c0301d501c04159940c0701e01f40402e07882402da01524020381000003590712030090f105d0b650840114451442030a8241c40f01c1403911400c1c14101110702c80490811050765170f540503480e841047c03000c480210342001e54610008a4441d1080780040c0408a207060b14207129480310030007024229014800c2d03220081082c2d8081d241c0c100144c409005074002c0455844050090388452540501200d02d81807502c0d10340001020640c2c64650f00654851aa00394501d0310300901051000c0c041006a46100780315042d480c042c0141d00220b0040b130b20b100804040354260700c00801000b1181400c40e454101d40604941a1042c0c0c00018582c054800c20840c10400b81e6000e03900340d030700c1501c861100340c0700c038981c559503004540032200005038100c04c00c4c0100f9200d10082d1a6400a80d80e440301c0e03144d03e46e10343c5070914 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 638444352 1250 638443102 638443133
    0x403180312170a2003071218022407020613120302060a0605010e09010e0a0e12030402040b1e010e012105041203020712030c121e11090109120c03 64
    0x40e0750918014107070b54038601090b421000701d03903040007a140000952101084110540252220f001c000101440d02400b60051114010b42d0100310b500001e086041c039030021502c069008a40802d05e02c140c180613080c2e51440d500c001ea440c0740c10111140e0030031045074003410b240042402ca580d030004411415071030b80211188250068000741c0360001c8001c084400d141e0243d4100521030b6001451a2a888603007419150200300d9100b980d41d8081d00700c4080e080c1030701412800d1140d0b0301620350002c0c0b100040d501592085500380401030036081000710811503089181801011f4102101041d8082c140d03a603c1c1d4031060500c3c440d4180801f8200d0500d1a403e4a000d443c0d90312f60b410403040020348120003201b211281000c50822103507031a980d44c2c407449004900c00389a91034040305580c0303000704e007035000d15458414240a400d080d8400e0b06074040025680d4582e8901704040001428400700940d0250340d01a910159241d18003c0a842e0780312038040155a802c507859000700105d8030003290211079 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 638445602 1250 638444352 638444357
    0xa020406031406060603060f010315030f1a060102070f060305040201020a02151e07030215100302060409021206011e0e0a09050705040312020601081905151524030403180312 76
    0x3202942d08280b818802d004103100c0c404e0004204120301e40c0d840d0860610703090000c0c81c001504607000c20011840740300c1500301800c0058548022001c01039640144407001103445545105a103d1200599850150740540c64002d103c810062101d00c1c4a0341c08203903c03600510454007076075a1500410b1400d140301c20071900102c40012009400030041c03041d002e000c084165201e107000907948000351110002c04401c200840c0309000704403911107042e024000f0390f0f002490740307079100d0b905d04141000358485801e000100d5080c0c000520591b01a40380080e001d0716014218540c645050f05c211340036141080c4841e40320455040110f00200544203081c401c44854940c0c2d0f58a9045080803c18420700700304520855010380c0050001c0c04e00480d1080c4412112840d0040d00526407500d40d040c03942d00381e8020500e0105004116036128801c0342501885006d4903039481c11140f80d81c4119258125501c08007070090b040010a00182c46649254203407002c4002d001c0d9459280c0e6284a801401031071074100 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 638446852 1250 638445602 638445623
    0x10030f0f0f1b020c0d0b1305010e03130503030909161404080c0405180715050c0312010e012c070311030a0b01121e0b0102070f03141209210a02040603 66
    0x281e042d0075081c125600349650004040d04841d81001540740499100d00420411500380072652100320b000000881aa00c08002d200715104141013690340d4010320030116080903122800603c5003004005c4400d101000b5012a2480d6122103594406e45500c1022104002a44031803546103031464014101800e0b200300036103800302c02d0f601004180d03080a0000d8410340c080c9100100202c400003481e0040319602c4101c0f03620b4507280d80c0199081d0041607045c0f1000c0c00700242c1101d183c80000304143c180c2c1c005011310700090362180b89408180e081120303104464100c80d078021100d03002d41504c071540705035140380201d010365242ca444400b5402c10350f07000550310384421100041c1d42c4c00c50400d600aa115007000c102100010941101036203816085100e1a5902d188043e404c0c0d1082c8124009411909004052250369180c4001440351140c0d86e0504c2c1d010b800c86007040d2076114021180a4440180b02c42801c29500c0794401560100c0c0620380c46500c5264000b00c0161528040e800095020705691507 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 638448102 1250 638446852 638446871
    0xf030b01180e0a050c09060412111f1106160c020d06090b09011a0a090209150c0d0201180507150302040f060518010903150b030102091f0f080610030f0f0f 68
    0x5039000544017a400b0300b0107000000b065200d0405640848943d08519200c41ca0300d402d100d030030300103040d01d140c0d000402201105074500003074410785002d840f0741c3c0c0c8000710038084d46000c03038990348155080b00e1482d4080b082d50190354440c14400c4031140c0010542c4511455981d070710011030715840c0007151840c0c1c5c18400c00c00c4800c070030b10514804100090410035102c060fa4005207507040c0c640111040c2d90741c041224590354950760b420340203080e081103c0c16038032640064155a60300c50840c82c4801503007030509180c2a0a0401c80c181c00e4544c0c1f0400405180d0b0a00c3d80b81c4d80c2c28240303026401c04042d400d110000f01e446542207414010001525025a9407266400c0340b0709404d070342500541032000b11481000019045c3e07080b0520342c00414000141c2c0241900003e019206822603103900c6050780544260841440030300e000140b40d540c4030328504000010080d504100d00702c0d86c4035444145481510703c964000e400c40c1c3c1583c030306c0c0c9c0350004003903c1a1442c402111080315121410702c0e611490344 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 638449352 1250 638448102 638448121
    0x1a04060b0114160b180706120b0a03080714030705150106090501081006051303060e100e0f03030a1112070207060807020f03030414030403170c060105100f030b01180e 73
    0x10380541e050300b1800d8078050801064a03640c2c0421074000700a0070b81c1c0c0700014030042107064a455804042d2050307441c11595070500038401407054040b01c404502d0b003285108246400c3e005401144c3d403140c0654109030003511134030f90100c091a40d24035a03001c00c00c05680000ea05009111703c90285021080302d41d410030400820502c40c6070042c1d81440b03110310a019400700319000c00c4040703400c980740c600d0fa02d40c00e088880c9220083e61340020100c0c0d0404500151400740031130304291854440204200d0b581441a04642d104414600408160010004140c07240c005402000009061080d210302e440d60012480031130900403203c400068002030404e22405501103421a04071099200612032070506156040e101d11015000402c18600079801195410703091041d1002580c0008903006240c01c52000c0c4d0300242d00010f141816030003401c0000c1012319000100d03226038003c030350752110185401c0c0400e5008102da2403089060112501c0c440b9984042200c00d4030240081e072400f5040340c01c0c03c1482 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 638450602 1250 638449352 638449367
    0x15030906190506010203090f060c0706030e0f010c0c030f09170f100605030705010809070317190504150e0406150c05060610052b0207121d060f071a04060b01 69
    0x1c0084542c2400c003441210b0303900005540c5400802c0f544c44080340550000201503111b402141034440c0680600010b0b029010360060104041403000c2e1022907015030006400c8544c942c0910f00428107981d005400300703105088500040b411400c28081c91520751709a4080036032804200c42c1a94007103001c51a003210b00740006100241401da0234404a41000300094a4400a02075103040190f105d00160300d2080400c070840c02150003404c5601c84084a082c84000c41c0c1c803240c4030712908102d250941081621072002ca4048441998404690101940045480014844207540c0c020780b102c501007156400e4000d6036100810507141c00d400d00742d040c54000e0a0031001005075108146030076180c03250b143c1101c01c44078044800704400d80e05c0030742040044070b00111100e40d205001d00c041906010401000c01074041c1c41074984074607091005460412006445004016411003c284502d05140a15602502d000d03841070002c810303200e040015506010104039003d5601b6501d5030381c40203003940c20900 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 638451852 1250 638450602 638450641
    0xa0339080903030c0c030706140912120109090501090b0f0a110301030816021f0206042a09150b070c0f080607170709050613080601080703031d15030906 67
    0xc01494500e040e94410b40c4900000b0900c3c01c103d100005e04402c100018000c40c0c4115a0201d010868001c2d224a102000d210403a0540302c1445000065800d00400006071802c03151800240300003607007012940d8000d4a40d48a0844480d92988602c07030004040085062003225003000c0745034a4a0700151050075520700d072031103258000c4200014000701d0050382c1111190001c2c40c0ca08104018184080b52941c944118200c208050710010301303101c01d9001c11180e00a81c01000f0121402c0da103d87d008075071460500d25400071411000c0100103070226034201401c12070174200111862650341c0768220041e1f01c81d4a04079040340313001006104400815a28501404000004201a00d01000007030984031009103041c42080c1c00400040015200781c0520000e040046d0506d074655000c000750203c55209402044058015000082031a441c0051840704482d015a61240c1044071030444404024a9040060b00281803051640c6c44940c2c4d00c000b540111901c43c003d010301e01c0e10a521080111a665 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 638453102 1250 638451852 638451857
    0x1020d150f0b040e041707060c141908180d020a060e07030210031107120206151009270c020708100c0e06161509030e1507080a0339 58
    0x400600402454030305407070640d02c080c20101c076243c903a41031040d1401b2808030845001c45002441204121290f04070022498440d12050a00d824000c85a04a401a0042206000d1800985e244500e01c610811600840e05050b403d0029000030010350174048118101c5c0050f9010540078000c108451051419a08403903000d800d840382598002070900c070f151528401016151060420090103030402c072983c8030340c040c10039100552600c40c0651601001c80e0320040e41d000031444021a420041c603900306101a955440301d16600748150300504272050300000070329404500f00211414000c0c801c40d400c483c80e50b0010489a0314041c0c195142c0f0b4520075000311300600300180c1c5c06180d504415840c104400032110551030f28010040c000010004040240c07040030444d4941540f0703c0d2591080d42114025981c070168904200103004004200034180300404000b0059840420a204054808110203190109401034000300c0c2c440b0000c10744103051200049445003151644401401000b001c0260 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 638454352 1250 638453102 638453129
    0x30609010203040317150904151844031b090603060f0102011e0f0b090f060d0c1e140f0d0809030304050d050a020f01020a0c05040902060c01020d15 65
    0x83c1d50003010b4a1500341710104410100005c110790700300c158024003410b50090480d442d2458282000003070403da00c02c00c1050249040441e2071504892a50346c0b1105800c5a0228441400d00148800748903054032494070001c89810001181c0010550030040700c0018001d8944a04025001410810a004024440b8001004501c083c0c2d1161070035a0750028013143e4070400c80204100507805800510600b02144c0d282d5200c10318640da45038002d1482c0c80310710b4010090b41c80440140700b400101994611200080d1000040b0149044407007103040fa80b040504100150751042c40c000d1105031000701201d00c10003c0418001084000b42c54551840110b0700c1e8a80d0340104004501050584c51019102071000200d000c600d0710104100d40082202070405400c918043c20000d0700c885050904902c0391400401180d01c0d50310004991102a0300880c0e850000c44c03902040000425091034101d800401c18440207d15807005e1014100d00d2102040116801c0501d0b112030009004940040b41c41c1c0d00d44 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 638455602 1250 638454352 638454361
    0x602030421021b01030906020a110c01030e15100e130203010f0504030c06050a110705010e070b030f010e0601090306020d0e06060a0602030711060c0109050304030c090b0603190b030601080a02030609010203 90
    0x540f030074038056008400034681004000407400703072000038005171480340002442a04141c1c48618082ca0886d040c0c299101242c620004400303480725665418007551040c2d5086801e00383c0841c50541103420000c81802155640f407004000f0783c0304460f507800c00081c020f102c2040d81000e0007458842e600c1d99000304014a8940e5026102d0710310101c000e000c1c0c41e03680e0f001a4200c2c519030b102800300c0480d041b906450303070482c1c544280640003c058800c110700491200140c16103050081e02d0145082140188242e800d01c8201c00325403400421040c10813074004400000f00710548010310b10303d601c06001003101c040400e04c0c18505403003d0300a6001e4208140100101540170080d250301507401a00c042600012600003040ca000700394502020354600106101041000401401180e2084011a50140e5980328200444209103507540c2c101c401040001c1c0074500c480302920f410405c2a02c000f41c500b1580021901c3c2078000d070001d83d00d59200342102020b616041140c2c540c0103000c200250324510340b = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 638456852 1250 638455602 638455607
    0x3809390301090203070201200a1e20030906070309080c1212071b0f08190c03140109140706031d0706030902282117030a06030606030602030421 63
    0x140308082c030095010000c2000180300b0340208100084554030500040400a40e11001e5030100b802500818040d40e054080400350070803c0344003502036242e840b401412401d032104d420061001402c03071780c00104805005543c40b80041c00c0d400d40642d540480d81814401f646207844200c5582230300c607141054400c04100030000c0c100e88580340c001c080d192581d0803450003089086c0c20403440701c4200c1040340c0c0860240388480781141200e8415080314100d091a0f510704d051541143c1d006803803607907441e805001048202e80c090b220042030310000261042103407a2080c003400d240241d8001900211800c1010700ea2501032016059a028046076180c0c00700040d59035524003d00c5560b0502d0345480c61038056650b8202e10401000d001850111427507040070080c48108003a000310249800c0481800142104841c0c0790500d090384a8402c2c003a21906000d8610207170030007816807030b1054461401100058041c010740004621491001d078032f0782018038184004000100c0140c22040d920341e100c050f0507a = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 638458102 1250 638456852 638456857
    0x31b010b09061201090506010e0405060709080c09070504170d0801080c0901030f05010204031202070312080103020d111c0302030d0b19030308040305070c061e03380939 74
    0x4119210119480004400c9001d170a103a80050030500580b0000510044946000f41c4920b12032020359426a84042081d140040240a060825400907020719046c4c20400c038101d403c9040c030b06055051650743c424050400711202c0051110f508030541c1c28070707403e4105207402d004d00202c5c13002d015131941c6040400c044140500c0040d06c000550640001882001e504640103584c00c11003101c0100138801000c0e5480ca002d210441e80c030168511600c00292040d5002ca0589500a041609201e000d450300d07802c45401d06405075221001c0d406c80086450020b007401c0078188642c0146448100201c2403104440d4040a914002e4010051007029240340b911000252580b5090210250f11281011603090184c0c1600030f2151202c4070b00899450b40054603100d007680b01c02c0c0c04d90340200d0001070450542d020302118030704152181140d1001c0ca1041c00c8071110716044100000d2009504030001a120941520382100c000e0400c540280ea0003102c50624100c0701083d0802c40d14401c1050034a016403 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 638459352 1250 638458102 638458111
    0x41d12160303020f0f21060402090f060a030e0706090609050a080d0f0210060b090306060f060307030b12060106110f030c060c1809011532030402010908060702031b010b09 75
    0x990f0025200d1100c01400c01610100e405028405448074a407842083d403440c2c9001d1007800c4c0e8444d00c00046c0051900c1e000310303400140081c100706400c0e20f01701c00b440801c1e00300050308014103880c4e0741c071032100e12410807040c0004c044950350310320024a0501c02403d50855900500e001d00c1100c4010b0020410010303c44034255010316202001066011040f410504000e115150741800d0a400040c4010403030f02405002008805a41c095221801084a444890117134550001010300004100d54003c1c1e00c040d02034180030300707098425088501424140300c001d070030800c081142140704044000f01008076a50b40040b50300110303e02880c0c0c481d825500c41d03000f0620461660f001904440e1842400c403000300000300a085014a540c49051111900c0300310b21000340008c1025255295041c400c1c003801191514810300140704034001040303a407580d44018401c0e4184030b13070030034000f41d0310104012a6203d184142d025503182ca0302152682c441d49494105071100e6070401004041c4c5644126240350007 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 638460602 1250 638459352 638459357
    0x1902010527031903090b09010903170601090506030a02030406060f030302071503060902210c041211010e10020601210b06040c0311041404060b0a2c041d121603 70
    0x103100304aa0401c0c0340d403041e00f40805038110703c440790109040c1c25400c0b5490840c07251441030b91654418285908884034004090b0000c1c01c0081c0030401c01c0321110304a500b007178041c034000103040d0f196004143c041c0e00649540240d26400010042441507a00c0703628013400a80c520005503d2a5890080d6113101601486041d071103907580c080501ca010f0f40c8010b00900b1558000e5480c0c2c1c2108040c1d000181440301000e90605c00c2e40300007072040d02c50000301c030b01f40d402051540040c801ca54481d100000b404c060b00d1414080b503189550780729a200c90301d11500c0c0c44280d0040480d0740c14000c140c003041d0f0216031202841900c812030200029018000ea03540050240c80c0080c40810345c1070101c010b02002004d41c80c1c061400180441e80e4082409200100300040c0c2d0b052115564a03200c90076544903030f0488500103180e03808030b96050000c0007802e2103000240b8440a1700199003200144c21500200f402a1500c804045140000c200a0000308072103c00044071071b04101c01d00000020f002c1c442c003001802c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 638461852 1250 638460602 638460661
    0xf0301020901053405010207120e010f03020f04030c0b03090c1f0c0203071e0509060d02030a02010c0609051903030b0d0c170708250f0513090f02031219020105 70
    0x820302c03000650308414620307a1000d41c12448403803c21783c3c000c2d4014074065030802d4141c1c0d404c1c990039010f4200c070606c1c220180d460710710f40300d4180402c900075040140c480c500c0d09801c01c00040031561300c4240b60702502c40405860fa0320b0403c0f00000d441c014440710020702a224161150106410f409108210340300076080203004400c10f4400603042c00810340100b0401e50501d03000000c4034204003540c005880c01520504017070b440354020001d92034041d800c001d6055014042190041d4480d003c502c0906104e00404034070040980d40712420810a8503807842d0b5080c4601c44070340be0551601840e02a40415031b016141c03501035488081d01142c850007100034a03480f00b2250910b91400704a084007c04141040e078030703058140c000c208421001030703094828840d0f0130940410741425506d01c3c04103c0c0c0c0001c0070810541c4150702c40c0c2c0058182c08109440203103032030f403840300962400c1c06803020021101105660f1003541c18000030b19100c244c03440100b160b14080400004184803c1c108581081103946100c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 638463102 1250 638461852 638461897
    0x31a06031009060c0e0306100314070321091e14032407170907050d0212011806052a0f0c0d050301091b08040f0c05041103060f030102090105 62
    0x1d00c1c0c04508a00241002d240514001c180034181e40440a062030b15500c0c0d0140701034038020076540b00070541d0410583c914001c1c04100041a100c40c02c41001e8614058440c4c1664070b86070007070140148204c1402c203022591030700c00c69030f07404003850018040040d00600c0c0c1c4041d800c1c0410304694103000781c103d00c0445491500301a0382c20402440320b1071f250821030000070982c890305d0303100c403030290f8601b0003140c00d001442140308a5024070510a03c6d4400090129502e001d040080c0d2907c4903506a03080180b02110b41e0002d0000e000d0601601171b09034510300e0700a518542007045941c003c00702c6001d9a25040742c00701030011601c0404a5114518800391140125445003c051080d21010790981c40f4008011143da50881e010318100c50700d2903820448841d29048400c60340b0410780500b0002020031002400140d18415469041e038014601140069201e01c04141291801c142c9041e4251001c000c029851510f081d664100b800700740c000f9810100380030006005409410011012142901c3c1d210 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 638464352 1250 638463102 638463109
    0x62315040527030d110c0f010506011706180403020d020c0f06041e0902030709030302010c0903020d0209040507210c140f0d24050403031b0e04021308030a090503070f031a06 76
    0x151540f40070300004000e88141c035170011402d60b0002c0d05078030250083c2c800d040d44603001031140d588201810f0711180c004240c801181d0f81c2880e4000c1155600c000782c403115904a142781100c99104a00c41c0c1c008141c100583c103006440c00740b4400c480c40c071803d100245078030f894035007102340c608903156016081d4141c15100054090740e109900800c0800e8070110401c049658840ba1050880740a074008200c0c006808200b15220002ca010103500aa0300050020050a0200c11503501074012070548907520345444800214090050300d6000d50703070240603400103001c0d9078008a8010310038044201d000c2283c020110b94155603400e180391041d0200b041040c180710325940110720500030301003001740d20050203602a008110558040d00000e02d08603604020020301d1400d081c1c10580da8407541450b0103424200300103588000707149080e403030800100007484a01040500a07807a202c0d22000a840d0806081c0b42c50582035900140c003003184483d00f0004221400d00e404444014888608619660400070 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 638465602 1250 638464352 638464357
    0x515010f0f020a080a02010506151615090c08010b0a081f0c0507080406020d30110705070308041d0c070213020403020306100f080c130906231504052703 67
    0xc0e02904e000555129050b6040d440203110715401c45400c907284c50007030300d034844601031403015040c001c840300825404111901052100c5003003100d408658209140d481312295a000e030300401903070791110303180320241c50481c504402608406000b484524450201c00c405020718061480308035035600214890144175a081f604070b20b8210740d0b9a90b0b1585c0d50701c4001d40c3d07114450900c0b00090303080342c0b5600190b01072113007417001040b6000350b2480600402c11008010b00c041490394810190804c07134200010001e000c032034011801625110f454074940b290002d000d4082c0070b040741c040280b80040220040b2443d06440b10690140c6105d6607240d0790030340d980001d106907040698188161010444165011015401a46c0d6188035070710180d0342d1021075a40e02c1042000f80c9078000030101c4000c82ca0312031940200c1e0064001c01000c1207240c0d041654806054280001c540b10b6800358003000241d680c41231741c09001c00d00580d0100481d152040c81d982d100590b0344449d0020081441030700b10b818000b00103 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 638466852 1250 638465602 638465623
    0xb06040312050d0b060403050615010e0a08060402031c1d03030d0608010e0d021b060d0f0c050a020d081e1801020c0309040b0a2d080a0b06040515010f0f02 68
    0x303180d01c40c6420000203022500b00418822440341001625003044c00e1140913a070403a54040020f003502c1d2540e01901c0aa00e000d80d0035a0304102039204942c045540d41c185d424010040c80c0c3c098040da0804d4014141010074452041056140943e08800d05035484201c7ea4030841840d040d80091001c0c1c0d500080c21403080101c109001820040e012401600c1903000405161495003100c08178170103102c090b61152408504213100c4400c0030316038000ba003060001020007120310440020400c4000082204407040407030810001400421b40700c0b0000d0301080b4108500c40182401d100c1858186400220b0000c00900e0140704220000030810803400c0a03d80420503007804002d54482d040f9030403280c0e030b0b40c019105e00b511940c2000001d50351410301205440c240c032020b00c88048070360101400c012401442510030700d0081008000011030070030610030300480910404c0c02800b01d003801003c00040d114060b200b20400c1500640c1161280e80240c0f1504541541d400c2041005244140580c07c01c0784055 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 638468102 1250 638466852 638466863
    0x140607080a141215190803041e0f0602070f17030d020d140114040c1e111203040b042001020c101b1a01120f080306040f0f36060b060403 60
    0x1014031840313005418100c02031960a0b12000a00008107040005a021500c90203400d40c104020501200c0720300f44131082e81400002096420a81d82c0c141e4059102440e031103500160002d900503c0850052841003008190b103400c00c0c5007614004441644034403d880504200ca0350000d001d034104105500300070b1811000d051840e41560b550360300c280fa091811001144103518203440c59580d240501d499080c4c1000c1e4007060701c4910000e003010741d2900d40c2d08403502404c1c0b0840d140d20450070007070b40c010340c4244e216002c132055504182c6400522a00a50300300f4490414012000803142d90004101e011000c0444042e007480b900400240c840e484031595886000c0d80b1a9010381c18801091113104ca4254104800e90150f0ba85807030b051419644450000e0003000c02c7c800d002c020030040c402031600401c2c010b00c0010231282d51104e40044a00c3d18205842039074403404d694409070800c080b000368170101da85031580c803111091000900f05a810000510403555007075101e500d40c86041c2a03070040c66016 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 638469352 1250 638468102 638468137
    0x70611130509130f110d080a12110405011211040b0a0816030e03040612020f1c3608120907031214040b0a0c1506140607080a14 56
    0x6000e240d00d008403402482e0090b0300020100d0000d0748000303000043d0703e4000b9081c0e610040356564444800402000c0f4a901038a00308800700400d0080c801421024204c5c1c4a05000100210340d080690b0141707581e4020030042803000f0883ca2b42c00c4806489250180080050004501c0042e0b072083d028640120f11500000f0900c2001240c1202149000ba41c00e0b0395440c410440c20281201a01c08080400c40d03260010300c8204407050003103001543c01c030031070710015041c0001400d4007440c54005501e0100c0d021008500300c101c00e0014070417074901002c1098500000d92655644544244a0120f41c3e00c20320041d040c00c0741400b032803005907620100007041260641c00d2041140c1d035a000349020075640a502c501200d200c070390240c041c2c161100f04007114641810321f8412005456046000405e05100b08402075400144200301d00d54284601c0300e2000580c142800e03020071144004031400740c00356004210120226041905070b44505007280b42403403c01c60580c031107030710386c0c0184484140341d00b900 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 638470602 1250 638469352 638469367
    0x303010f060314072c18190c0516080705060406061706130305160b0109020c010605030f0304171908120603060708010e090a1415071106060402070611 66
    0x108034014080340c5003a601808079086000610400d150f040da40400032902510b920000c4907031103c03e0000503400418450a4050442c001c5070b4045224504000b0059503d010002031000701c440d1282003015100b806c02548a55140144c41c500c00c204103000320021500303049041001c440d0482e2506980001911880e00b09850202d002d03240a0107200001d440b05804040c50940003d24144030302281c0c500500040302039282551254055400c210009070010080404038481061032402007022281c0142c0d640001c055181c2103441a0700024880d8004464002603602c0010075603056400c54aa11440d44000380c60482c034101001b9008a4842407145092091224900140080032003210750700707565a85403c20540c031428221074150100c1c2c140c40050000744060640503a005030040d003210051401030b1a01d009241107400b00b0340702e035440700d01403170305501c5880f03500c03a0845201d08040c100e200000c1d140a032503580c002d00c081c1c020366010511406022050b081708080000c601c0714507907a07810 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 638471852 1250 638470602 638470619
    0x908040b070c0e0c18041803020f0d030e15180d050a0201112a1e1b01020a0510021c0f020c0d1e05030c120709060e09010e0703020304020d05030301 65
    0x10300000e689614035a02c1c000b90710649500a2440f5401c01c8041a1905c4031807907410040e40000602a81c00c5503035444448041d0b04142690180b07175019030010515180710701d001920300402103c080b0105801c080c4840d121000000302c8030006465510070346115582c505602c0d0f000014003c2014141c400d10f0150500320b60403030020095070015034002e0113509103650300c1003258820f03001e03803107400c00920654084500a00081003050010030050324400301c00840320030341840300d503150340c00d0a4110303000380855011b00e0325020000050178005458142070607140c03281c0b51207090025030389058000603004050480070000c3d91291650041c200481851a0741d204000d40141c03180440320300c540c0c0307680c030b00e0140903c500c54513000c1c1440b00300043c9030780900101c800c2d030030103442c5445501c4c06220140c030f0070650ba4041c40c072461142da91000b05c00d00e03106006001c24070390400b07280500805001400030f6682e503080c26500010034100580d5a44452000c03803622141400090701c280030220001c41d80d000c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 638473102 1250 638471852 638471857
    0x504030204050c0d051f0b0901080c07030c0503040902040503011a18070c1a07080a051b0d0b04021b1e07051519021e0714040c0c06090507060809030a021209040908040b 74
    0x103007101320410403187c031644505a00d10602000d01d0101d004d038800901480200341c001d10485209162880340c5040e59600c0d685941c00c16041100d8103038001c24140058102449815200cbe404d4440340500c103025040800d641e091500042028800342c40e001500840c0a0484000100c0d441034a2004051044440c2c840c000c609590400001c0c4400b004295004568000c80d4028104006180b0620300e001d50031445079800040c0c0f404066441e1003500c2e080c2c0d070760340c4090081c1801140354011500b000800090800c0d140c510550303981360b11040240b480302c0c2e002640e042071352000c1e1141c01c00010704d910414103070b001e2480e8020358004c0c060701405419901190702641d079003100c408400c0241d803000800d9221181d80c05601d5075601c55030303038205e010315054000d09441c2e4a58200074001702110384606003034400110301655190300c04d8004018140d0f0103400564003104905c0918144145148002d4030380e011507a042070403000102d80b10a02340e80c1ca910114444d903200f85100d58481c0c0c1c4c1d58400203241c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 638474352 1250 638473102 638473141
    0x30f080f0d050a1a030d120b030f030408010e12030a050709051c020a06020a03050f0a0c120e01020610230303090a08061009020c03122a13090b010504030204050c0d05 73
    0x10700f4040c032400840b914a0404e900c0c0c890040c00f80c8030000d03c60104880e81d0208801440d100c03500c552414540e901e05001c000940300e07284010b143d5560404000600b5180c0f022800c4000360b000110000240e00420190394004a42210100b03051321a008101c031380316115005603601030440d201a0804090000029030300310710031340b0220156079881005980303416080c00e001e004900b040208526504110b00244110700050815040c240d005859000c00306044407081004030754040030ba40750715038040011690281d02e20902008090814a41d01881c6140c41411f803114040c8410300d80340c903501401981e114400142c000b4907015510301400ba07641d00b040d11030b0b50000440a00200b4000218001c4603c004080801145426900005e8012844e070091a8910f0410000b9010b0100d8803698032608980c0b43c106051511038608641c046a14800c0354000d030b021926140020703002c0d0740c001c0182c030b003201d0b0121000541d0b955610700c40141131240060251015282400700700d4400107060031215031 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 638475602 1250 638474352 638474371
    0x3030601120906020d1a0a090b01051c1d07031509200a091e050f060609190803071101030507030618020703140301090c1202070f120c12091404090c030f080f0d05 71
    0x81e07900c230903107011201030b80c100700e0000b181006141195040c141c0d02c0c00b444548450000341c2c800f00c0144c2524142c0c4520300310811a04210820000d1080011070085502440102040000016507030035100c08080411042c10318805500e031a0607955442998000f002c29400c10b002002e100c110040c0060a80c2d20300c01841881c04021a1840c9510340c44140320342c0028142601c1c2800c00e800700102c41d0300c00d0345000014040c900010a50b01c10904c0585552403103203100210901007540090b0035070320014411010145011020007400d140180100c1d600541044016070325001c0342412120300301c28060843e80054000000101c1000640c0520340844c101d5031188080340740d820b5140140d1042e220054039502d03054080d500443c182c01c0009440d40d01c203040a01c0c0c20341c1241c1d139518021a4280701c080214000400070060404c4102c04500e40c041e04440c2002544200d41d40c0300840c2c00e840c04094480007000421204000444003110701d050b294031402501c0c0c1010780d40800c060f09048601418 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 638476852 1250 638475602 638475619
    0x4300c0f081603110a150203270915040908221a030402010f030b09070206060310020406270f0806060120030d05070905040e071703030601120906020d1a 67
    0x1d14020216840c0b400c4091a000c0500091a40c2c6039840700781141014031303600c50140040003540a0261101d402a222150085c607258001d002008001102c0d4944c0082c5210501070700702a41d80d034902400b030b80903a0b44270a80501140d01c00100b40141002100181100381c00190f184607040e1004041199042c80d8038102100da88a00d8260703103207034a1001c01443c0c041d0500100700158002c00c5003407140381c1c00345400618070308800c000503480c0e80240c81080c0036801540034440d06040a101020052009a200352314117450000005d11011055440c0398424000390720b04074201503001e00240c01030180029145105485840c59a144c0000f03a0300c90f40440c015415030100c141c4a41061002820322001450910740d0000109000d0a0010014810444000c401207510755551080d495203034138840052003458104072030705540341c4041c404540c03142d10074410401c10340ea00100072002c0161038040450f80c461203180810103406040707240846103050880c2124080300e10301c107411130300d40708455103007 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 638478102 1250 638476852 638476859
    0x8460c03060f03080904110415021b0109050405041a190b0a1202010c020109090204090b010e04020c060126010612050c04090c3302031210060504300c0f 67
    0x10201c074060310034208072020811041001c503100e00040c0c42c1c4418043c0c4041000c04401035a030002c4e07401504100310f031014075114181c669904011404003024080800480c0031032500000e043c5440311700c14148106d864400003001c00140d243d51b0324071030003031280280c5282031010303d518512000e00880302405240100040c1d2071f14042c1e901c40f0440340d0712050041e074071700c00d0f80044800b400e43e90401d90510064403400101c00e18244010310003084480e00005425499100042245000b00e80076846940140311f0b41d624042d0104130b1604481259044940190301c5024016070384040c0f050041ca2546030140024403450900c15800040380303d01c050f01c0780380002c0d008100888003c001c0180c03880340c4441381802055010001508411b0042c0c0c81545215862003084503000c1036802c00e000140c0000c41c010100e22100a80103400c0708055000c042024200a00205640a24400c0003240a0385c180003a51446006500240c490940c1107210400c1b180303800d00841e00700d403510866001e4400010f001 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 638479352 1250 638478102 638478107
    0xf1909020a0203032410112104060e04090809120a051606120e0c120c190e1012080f090409051617060c0c01020412030e0310050708460c 60
    0x13503046a0007042c050701074001020443e10101400821f01052013440a4003d099514100340d40030000710700c00c625621820440010100712071202c240c2d020f242828003001c0003c0e0100c0c02d44000003000d552020264880400c920b25014076040003400754000e0f525201480c031010740440040d50450f44940c0d81011442c030700003003100c01c07a000212482d00b050505030440d1501c40d6500300d604a0380002c4803c910802000204112201c0a21601c580b02e1504208070005483d460700380d0041c03030074042025440c60690b074134000c3c102e862070040484030009424802201040d06803066020302030010040c02c42c0e185002c1d42ea5802481541009610001c0d0000c1c7c007002c1d900c14411030b4108880035002319268040450000d411404034010155024440031270041104079446803c80d01a903120070008407a501070604140c800c589d0001c8903400e120400c102290851000c1d600b00c685488a9450228800c40015007504609080d0404000030007041c1b091010508201c2100750b420740d4100022128440e05 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 638480602 1250 638479352 638479411
    0x207060e0102060402010e27010e01150f0e0415030303091a060a260303090607110d0c0212010b09090102071a15150903010912020115050f1909020a020303 68
    0xe540181d106a002400551081d02224807114000d0500030381005041e422409002c10110f1040c0005440e80041040f04c482400c11030040c81d5041005002c56034695008202000d44030010042c0160100c80c0300158607980c3c4001c1c10280007070301b1600729070340b01c5c50000c02820b042c0205540000040c9524003105004400300b90180700001c210100315850220100d41c01c400007042c1d04c0746054140000030107580300b4401103205400c20f4002c4c164030300cbc20b0034001d403401291612074682d541c0030007056000550881d03da4400207030111100a502c1c41c18120b05405040701d4065250031001030024040c080c0c00540140c2003e40c4a10400c01d1006c20324152203540050445103844002e110000301d20b00f030704004100e444200403108420b46040c101d180428291170001004035202203401403d14042a07081c850102d05070140c80740061b00910703010004440f0b00303000e80c0c0c840c40f03141d5001c80220f08002d580d0f00d01e8010302e90580c00355255420100040d440b50022544003003c81c5104503408031207031004d00c2 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 638481852 1250 638480602 638480627
    0x103051e06010e0f0301140910020f0a0c1509051b030c0a03021c060c0512091b0f13062402030408280b0a06031b050303040308070c0e09060106020706 66
    0x9024032241c0c0c40d0001140c0001e00400030342c0c0c002559540361541510700b801501346010303c40084000c1410300c96103c0e0300d044040c03201c15a415206106030324200c0861030840b0312143c4c1c14a0031000c03024040c18444180b080c0c50088150313080c9800396138010007101059908002c040e40401010410444091540360310a8512040d031248004600340010715040b110307451040c2900d09480a090525034405040321202660100490300108200ca41d620704c0510b401d40c04400f10018005441e5541030080c001040e0038105440b401c0e40e0442440d594681040c0700c0c641d072900e12401d102050743c0344240409001c5e00e40740402040d001901340841140000b00329030450391420f0042c5010b4845020740d100807403e4100d000c5c18240c4294031000400c1d1441c0c00d05008160994000481603d589014000e84180a000441040a003042001a65808400c1e18103c03504084100c0e9280f8462400d10707403a1101e5004010b8401e03100c402d0081d20b0f407000a20303906807400c50302201c4002d601d0703610075280da818024 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 638483102 1250 638481852 638481901
    0x5040606020606060307180f09050a0b031c02160b0301171203180a230c030705010e12101508010f050408160f080a0c0501050133090b0d0605010305 65
    0x420f042c3c0c1002002560b200c100340c640440d0441c681590113114176603541c42007451103120881444a40041d01c281600012091800c210521140c00407035150302c09070400c4555940720b030030f240a040f030003445003100c0c040742d440d4090741d070035118048044503401c01e00900e14504483c0340300c5400c000b07000580c001c040041e071b2041401c541d01c0195203142c908d50485119020700035170f4031039070009681c10101300c0a12044002444900e103481103044c134103126144030038800da01a0740d0070042d5076004a50500c006009585180b8005a4090326600d00a20850748200701440c0808a908000502c003800003540c0c2c01000a104030001c065064040d10400d860150065800300a92107442c044003ca2a5007a8070580c00404244030b5030311350340d1701c54000700081404151800d0741b05041160030b1003400e01401005064040b41003160148101c81500d030314094100700311004664140e01d008a100700700901412a280369994499060b603800380081d03101b40d07400710b0b0602021400c4d00403035112105103601d890 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 638484352 1250 638483102 638483113
    0x60314040b2823090303040804170a060c03091401060b0405101b0f120807050a03020703020f151012050a0303020a18090f2f031314030a0f1b020d0c120c0f0504060602 73
    0x82d4240ac040c07a0ba44010800c51040c0101c0784001040d90188a40309059610b00041c5480b107405c0a20241070b19040400d0181d25002c802e0009a0105003500c080d00d806650440103410661001d8a40180165605800030034074004d50080100c0c514511203651300c1003a42c201e6811040e2810303100c100d03040d5415004201c2c148850034071f0910075405001418024030444030f25001c990616030070500005900901840048100f14020155400e80c90081541c0b00040348404e505d070f100c1603103c0d0154980101003617000901180458855806c050f50003115202c420b0034941c0d1005c81c5401445032201c010040da0408018644240e110114031a03007003d5a4004200e180d00c000d0381c0303e0640d200921101000c40a07040b01000b080c6104410358042c0c2c400030055075500745025000d0483c0b50f4801c0d0314010070680001c2d261244d030140d0440c803000c03641502d607051054a02d140905103208250031a10b0115003001d8840309010403240e1040c101c4000c0c84100e00040e48075024401600d00354000d410150344507 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 638485602 1250 638484352 638484359
    0xe01030b0403031d010603030908030a090b1602060a030213061e08040501020c010e0114060328110909010c11070b040b0309030403020301110301060314040b2823090303040804 77
    0x9668100d03442442490300103492446110581c1d00700d402444a05044c1e0340d46d030001d2042640100015018104440080d802c01e00304d0b100082503189180105545034201080090715a1104050351002070350003041203403148540c283c020000d4224105a0090702c41c515800100c031030250003103001031408244006410707900d00e00103a800c000040c2c803c40b1999420000055040420302c16054000030001c0041104c5980c0241e41f0b182c030740064101ca100e0f4010383c0c5c5801d04040701c19400760b9058400c40c01c3d5501c460690920742c000540300300425801040f603d0410482d84c4065021041009451300c68100e02100149800d56034041406807882c1c1910400042c403d01d03081d88042d40d4030030704800c200d903e400d40b00d80c0442d0a44808400c510b60410011005126064042c0a2008080c00128541d0320520741034440381403001c005040404403840c1e40030540100b142d151518012400446410321044a0042c0c51030036500f0b400380101c1c0c0403407200700812103100012040724011608031802d58149410b = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 638486852 1250 638485602 638485613
    0x20a0c0822170709060b040626070e1e1c0623010303080901020306030d0c08070b09060109060617150310110d0c0c050d140702120c030111040e0103 65
    0x10070440040071054640060007106a58040c007006003864940c0060b680688000951502c2075640040c07a0550404000740304203d41c40040d50201d40c042d00d0401208004001c800c441901070114103e48983c003501002a016045004808424019a000240424100c0840c00618250105182d00c5002d075036141580c808011900314a460081500003868081e55180c400c2449039400140e50b5201c108004005058210050690205100000b94a14a41400000c2e101c1e150a0303000c20501003840c56602c144500c0500755800140d02c000f5540c0c1605103804140c0c0c2ea0602489070106030b908022011810364800d00c0c18641d100c0344043c810768580c031003c01e01031130002600364142d014818022658083c2400d4003949400900c0701403e60394486400c0300f504165501c0480403800d02180f2440940022000510042100d416107080d001d032040702c0c08412801e20a850010758000940014900e29034008030b0b1059803184101d0080041003800c18203002540038500c10382d20401c0760317000100f0220740c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 638488102 1250 638486852 638486857
    0xf1c18021203040e0a090b1008030301030305030a1407120e0d080a0b0111030a030b19080d030b1c0309080706032a050708040e0603160807050f120d0203031504020a0c08 74
    0x1104102a0b0741029200c140c00162100216000725000d42c54040381c1080c002c01860098100100002c44200c50341842c203003170755a22040c44002d00304040000062411821a0700c90365409050002d489941c0c02c00000080c1003241d500420340c10a883e1030050781e07102c100042c540804d070019850380142c40e82d0750705012000b01540c0080d0380c1400174500c440c0c134450390280010725100d101900c0000b400142e0005125104501e484032000025030310780d0030b02c240c8100051014507840745150204442c0820f4012521950b200c00521030440b120311007503020507402100620a07903009008481d08140d4904080f0b06640c0540442051040d2030ac0c1000d071424180401e0b484d5044140c10301c0e0340361208941c1e81040541c0158091207004a1203004c2c0070071880e041c80f4005420709421b04000c00b5600b00010180c80e000a4800c080c031401a0000c00580c0d511800c22041c0070003000b50a460904207011400f0f5100d920443d40310007154071003108441a8541b910aa65459070396039140c13800c48178184e03a5401640e = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 638489208 1106 638488102 638488129
    0x30f060b0405070c1e02060a1716090605030406060f1401030b0f030d030c090e07030e0d021b010c0303180507050102010b0a36020f1c1802 61
    0x340e5000c24140c034419007200d20a00211a80791a4422185c11a58005e400c44404100030903816000301161324007070780320200c0c48500d0766442144040c01c1414500ba07008a08a110140b208038410000385034800e01c40c020019240d611850b5280c02134185034002010000c0b00c0c183d40002c4d5070b243c02040043e202c00d41d03840c41c09107a44400a2b80b1044202d6880041580d28a1184107951051110000815107a100004207040c6400006e000c0d244081070009507108034400c41101c24400140c84a984411400509160009400450b285070010509800309900da0007000305404154a00007215403007040180710542c6414006030a445440313044034401e10f4810010010041c4118005081c42041c4070490201359441c07000c03550312810313104aa004284081803503401ea916600050103220b140498549901000c180d441c000d5400d040d580f0502d2480443c0c030b00005044c54020310408 = true := by decide +kernel

theorem cover : BRFrame.Cov 638309352 638489208 := by
  have h0 := BRFrame.cov_init 638309352
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638309352 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638309352 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638309352 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638309352 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638309352 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638309352 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638309352 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638309352 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638309352 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638309352 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638309352 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638309352 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638309352 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638309352 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638309352 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638309352 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638309352 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638309352 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638309352 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638309352 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638309352 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638309352 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638309352 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638309352 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638309352 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638309352 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638309352 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638309352 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638309352 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638309352 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638309352 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638309352 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638309352 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638309352 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638309352 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638309352 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638309352 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638309352 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638309352 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638309352 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638309352 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638309352 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638309352 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638309352 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638309352 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638309352 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638309352 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638309352 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638309352 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638309352 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638309352 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638309352 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638309352 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638309352 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638309352 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638309352 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638309352 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638309352 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638309352 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638309352 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638309352 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638309352 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638309352 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638309352 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638309352 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638309352 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638309352 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638309352 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638309352 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638309352 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638309352 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638309352 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638309352 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638309352 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638309352 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638309352 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638309352 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638309352 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638309352 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638309352 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638309352 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638309352 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638309352 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638309352 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638309352 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638309352 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638309352 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638309352 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638309352 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638309352 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638309352 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638309352 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638309352 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638309352 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638309352 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638309352 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638309352 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638309352 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638309352 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638309352 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638309352 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638309352 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638309352 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638309352 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638309352 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638309352 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638309352 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638309352 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638309352 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638309352 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638309352 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638309352 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638309352 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638309352 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638309352 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638309352 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638309352 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638309352 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638309352 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638309352 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638309352 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638309352 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638309352 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638309352 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638309352 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638309352 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638309352 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638309352 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638309352 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638309352 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638309352 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638309352 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638309352 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638309352 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638309352 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638309352 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638309352 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638309352 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638309352 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638309352 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638309352 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638309352 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638309352 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638309352 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 638309352 ≤ n) (h2 : n < 638489208) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
