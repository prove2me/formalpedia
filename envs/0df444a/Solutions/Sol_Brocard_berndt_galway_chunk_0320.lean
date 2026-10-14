-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0320
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:11:36.207162+00:00
-- url     : https://prove2.me/submissions/1d3dc907-bddb-4b53-b482-9e90134291c2

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 57374104 ≤ n < 57553960 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 57375354 1250 57374104 57374123
    0x2a0c03060908120601032906090603160e060c0d05030403260a06150903110307080307110307060806030c0d080d0906091401090807080904092001020d140d1503060612 73
    0x1380782c011425240301418405c5410108403292110b6200b0b240b01c50340000000c0e10a03420188803000080f240d40003190044441105542e280d4070b0340744c3c8501d00c1100e0701011160b0a0404840f083d0103661140d8140342c40041c018000b002c1020b1500031134015920350410032050801da150f8407151940c1d40010780709082120b0418501080f00704840d084108034002650320342e110180b440c1c4484003580c020301e0245030940503241000c94042001d000414115000d220102c5080c1302c00f006041c50702c003959122504100114007801120b80e804916000d006004650140c00341c503060400060511421030718115507480c05094404105583d0890b0003240e010700010903480c452007070441d09840b4448802042c51004000c89000501804081d1a1483c4086d00016549460ba030711914180d907042c00c8020b450b00f442072441105c0d80d0403c10780050302d6080ca800d18400400d82c0e101e000900034070560064a68a406c81c040ba90070780103090100440d0031000c09d010300340d6101a91303620b0810110381070390031164 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 57376604 1250 57375354 57375361
    0x61f0c0203062d0a06030c030c14030d0f050d0f0606020703030201050f01080c060c010b030a081902070e07031d10050106080c0403080702010c0f1403090102010b012a0c0306090812 79
    0x41d05a80101d0b02d000380c48010080314055040d403c02e09000030128040310f41c0d110400f10208000442c884081c6220700c542240c1e16050640031300014500b85603480c465403280100080e210b52218003d62307c4026400c0980c0c0301c4580c0d4030440050004106180d03a01c9251107000142160700082c0074085030b000707400810042d150351044500a080034005c140240d400086051601d003499401400354040030320000403580b0f1080e00181c10180008004c1d0b4540e040031a0b0b0400340301012420303407080841800241001d074a8034451041c83d5000420100c10325503511480801c0018a00901d4031000342c220035200d1416013180302400820007802007400264404002816000119089606881c1c004c44c1e078604168032980119001c084010048501c030040442d41d900103210794842103074120340d20000d592561148070009086580180c244e0741003140011240100c450700d2020344030000d044044081c1c20105505001e102d40502e42e000508807454001d400e024003099401501c1c0094201e08251140c0c0c4 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 57377854 1250 57376604 57376621
    0x1051605061e01030b18030712050a0e01020d170604020d06090c0e0d111005160501060e090a0f060510030203060f06030c0907080f1b04080304051003060f0e061f0c020306 75
    0x203400f4080100740c4005c10000c0348001d840305030031341d1440c01038000700ca14100c2241e0307440340c4004000c14140b000c03400204003010900c2d0440c035000c1d8500400e100810071083c82800060500b0401158441c3c0780032144040f80864696070102d0301d13100d04445003403000c9540c42d50050b00030116003101100040c058000803850b4900100020541604084064400e000002c1000b030b1501d4041013420a01c10104055400b444061800343c1e40c00303002e040002203c6140600d402181c4400400000d0b041e01314107190400107099055404005801620008841d07554250460344848240c20296040c0310f03c1081242c882401e00e80c075807280c60190287e550401d9403506001c40b150007a90818081602000090756440c151400c0036405152910038034a200444a02c0089590040c0c00440795900001030500c11400c264000400d00310351480c0403c0030320f15051304c04d698080c860084030040c020317402c0071405560f500030312200210078000d407005007880f28510142900b000c00a04038003900030b6000040101 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 57379104 1250 57377854 57377911
    0xf05040b0a170901110406080601020a0c06120609050705160204020c03030112060b030307031d0f090c0c0115060207120303020f040b0a0f020a02011d03030705010908031b090a0506090105160506 85
    0x191040505d0341000e08045041e101910300522050444c41002c45000c00b02e210303c40004002c207080c2e00c03038140c01803a040c0001d06484c1650013031015a81008240022a94004200c805c90401c025240d59044032034400940030303100e002c03031540a511001c0004200f20601d175400070600c1d03108502c10051114404141500ca0248000181c0402c100381c2003100d0248405032540980040140151040d101090001e0441d01c8152005d444444010039440c0c0d480e80700b40b01f1544010400480041c0040c90158025916005801030710004140341414804050180c2c0640740d01f0401814010b45444c1c40303040d00d9186401c0b800707202c8006046c4030304948605001003060110307250180e42d0f543d1860200c00310035408038922440190103200800c41000410700a2040034074861040314503179607034100140101500c1d6040d043c41c503a040020058020300b9540d8104c1d0608a8405907000d40e1158106c80060700d16006420282e5894420080c15008015000c14041d105200403107504020a28490701000c00 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 57380354 1250 57379104 57379121
    0x71205060f0919060602100b0d0506060d03090e0702010911010f080604020c15100806011a180604080102070b0a05010f050d260a02060106120212070f05040b0a170901 73
    0x4202201607410107400c15840003507100e504a203243d0720381184000f40d80103c07051a480900180c00c4119031841d100b049029070b2001d4482200d03030106148403525402e0302d036000034044c1d520900c158038203101014000c000b904001d140c0d10903062000d28100c88046c0c041c0c070b000380c02143c1e4546071451504a540c001c0800c00c4004500d80c1d552038042d581c7c8800d00000350300c40240d903501c0e44101c16200c0c02240040000070b1041040e540d03900c100d28030301f0034020701e08007042c3c008000401da9405000fa4040740d8509903000440c0d00404dc00b103a404c1c84010481c2841035811810140d400007d00c0d006100820900341d000740210702041000d40c0e645e0820710002319840c05290b070f000c102d04e41001c012408503001080e070090508403080d040c0d0008001410356030300c44000c00015800800c010031078150007044a41528050844c00d41c03402094030791100c140b42e00180f200e4284542600069203862050b02540e02801c0a80b0a056442094a00190605c0101c0b00c07018510791200001504003441030103074102 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 57381604 1250 57380354 57380359
    0x12120609110307030b31140c0d090c03020a03060e0c0f030304031b050406080d1d01050d0e0a06020a0e0a0f080a080a0302120703090b0a05040c06050a0309150507120506 74
    0x10b40d22890300c00c60181c20304a04040d4020090f07007884515500103d01c0030b08581010318840341e590f2041a40c101a12550000c0c03845c592a00c10400003c1c0700d50b08202d61020101c03071400920390b9154505250b007658580c2010303420420040f40881005441c0d8851140703585440e04841400002d40100420300010000e6103806400c244000c01c00a10542080d4180003080410110703003c1e12030000c10115a66039018107001c2c1c2c0b244040005007900078440c0800c41b040c28510301045d20b000400640144902c0341240c076040d94980000d840c103281401107614859101c03805550743d0a218000810180e00231100510a0300c50200c0021441c50511340241200c20800140990f103501da1030340081074100c001c0840506400300100d01c440030520550921030303506a103000820400509210711407010090100d03a07441e103800180070100306000040f6080b984680352003a5600320b44c610440140000c0f50008000c0284000c04c020340040a0704418403808d06a80c03420703088080c04a0581c2680c0041d00c0721034 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 57382854 1250 57381604 57381607
    0x3040510150504150509130317040b13020418031806050316030e070305100615050c070504020a0203130e040215030106050405010e0a15020109170403031403131212060911 75
    0x40641040e4004d00440e40780c80d0365103903805a817140443d50b900790444441311126a04540c2008060b040340017504140b0846110180c24a4070b503407105c000380c4011f454036042c1d0f031401442c1811903840f6000005401d0040280e00280a01c40c5800f40140c00c801941c40d0109103041e001084561258003520f01c58409101201b203041e0b041c2606400400c920f07403800084d801101d030b02002181d010881c030000030008003400181c1c0d41c03400e8408100c44072040d41c0142002001c00c8807038621100014580c0903035004a9005907140d9030003800364510320481218039962510704000044602c400c545440c131a50013501d200c4d0b199407400b05502c0c500e20090081c00040b403410b210501c0319510542d143c07403903400060210700c06907885103242130710080c40e030324043cac0182c2d100c044150411030f26100b550220038034840010304190541e4bc0280842e00c44c10f00b40100110f02100143da4000e010714819000741d00000803080c501082a8010000d40758061541c030705070300744074001a4142a44c410500c0311091030250a = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 57384104 1250 57382854 57382859
    0xb010510080f06030109050304080f2a09070320030f070e010206010e0c040b0f0d0e01110928080f12120402010c0302150c0a1409010801060c15110304051015 69
    0x100b0400c0003c0d1845415645c0c60440b5400624104020310103041c0500042c00d83d150310b840c64524003000f403502c0c0034152a40e18a0010fa80e0315041d034040320315504a0304003403580d5440204400800310b98202c03140801000419445181044e0019401405404554086580c441c40180c0300413424262890040c1c1c00340d4010000204281c41c0305400078030000c9054985075840c0006001034005109417800300e800000d00d0814146244200003020030b40030001e121190b445400c10301c090096100140c0503800b209006c040141118299004e44420284141d40702c0d501c4580c010382c0c603c070044611189102c0e1035410060451607009880042e421501e6142c0d02c0c0d60f80c0e81c0110f800181007881101944104a071111500290780342c2103200340040640c075a15175100c0310004101e600408111280d07201c00b0045210f071643c1c80140641500e0042c1031085148281d41f070020490020742c15001d080524080d41c01c03040a00300001540140c0c0160102c0d40380703d070034003414012250b03000d01c00d0b208101c450108 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 57385354 1250 57384104 57384121
    0x603070806092a0903010b030a02151305030d090f0611030306010309030513030501051e040c0623070303050a05060301020901020c0108060a170a02090714030406090204020c01180b01051008 83
    0x2564400d400c000d000083e2003e00101d00c9142c202414466500b40b40418a1005400c092207400003a0004800600700c1c00010b8021400c81a481d88c05d4040c02040000d0301141c494004004400905019045400e05d041b0042c0081902c1400e0041e01b52021040100040700b500c20007c031061641080091403031900ca01e0300640040c048900c0071018800c0c140181e86000c20b010010384002c40c040c2001140d05d25040200c0700b0640707034080e02c00b100b05030314400388030100b100c01800c0c178240d1300c05040c1082c46103291880c080440c2c6039040980380c01e00e4000368920801d54141c01180c01882185811311081d01c03000105401d03070041030340c10380c016030000132204003544c8a42d5005406c540040c2a29100c03d032100d9102d44040091304059001d40d0054a0030011070500980040d07200c9502c1c94010007600c00d103035210f45c540c440500040d04041c0c0380c80c0081d0640d03503550304850700e2820b000002c110a010760340110a4924004001352017811105000050505001480701ca02d008107a446030140d036605081d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 57386604 1250 57385354 57385369
    0x60702040605090f0703061205030d05040c0e0a1509020720040204080708010e0d0e15030403031e0905070501030510030f08040803070f05010b0d11040914010f09030306050603070806 80
    0x14180d03801078459000280d65211400a01d000e100780440c002842e02d060040581520f0f502d034000741e018881551107402040c0040f040c0d4208407105480800c054549007400d074a41346082c0c00c1510103441540900c1b05454140d401002c1d6480d2058000e890951380780b4818089014400020707000c01c42d000a403140001d88003401030743d29807009000500b0f054030380000d9450314210b90051841607542d1041c29803005c200300810a40d5001e189401c0d0300107201c5c503000c5805115030181c62040340308040045002c00d8040e40208580e289062880b9111210002c0b4a0000e41a06a8141c0d140d004526001c2095480b03070185a1268054003d40101c50f480c42c1d03587d8503400c2c04183c050345d01d004244400b066010060000b407031280d0240c55002a0344000e400c24034211281c1c2c04015100d5404d104000001500d2a90f45401996040b01c000a0310000f07401c01042000c0b42d0301c1030500d10f519082d048607841050303502c0b024589000780c1d410480c3ca920340003400030301e01c4242c421002154100000800900c1c4c260f0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 57387854 1250 57386604 57386617
    0x5091b0a0c061a0405010e010f030308070507050d0e100201091106090109080f01020912010608100b060c010908030106020106170303180a0812060f03010902010804030e030c0d0b01030308010b0a0e06 87
    0x64201c0c41d4850703a480d5a012a8142803000d40a2150055814043c2c0b50500986000d4812550030035002e51401384801c0c180181480000c0034460403400140a540c0580183c40c07480c0c0e004402c0d69440101201c0082280c4808030700941b2039041500080d405620510941140036488862802e103a0009402c11445070000303001b0f00e040100c0c4240c04101c6410070320541800301c503071a00240e16800c1b01c41c10441c4924504c031030480c40782e02d0881d0410500f40c0010b00400100c1c1c02400003d507100c004000b2a207640308854807081c1d213600308100202003110b0301c0d0081d41210190750007041543d032544010314035000700030028591541301f030020505551100322108960002c803800c480c1c1d6412581e4800c18250480a56400702000110810403103040018440401c240210000c0010012075400605201c002804c0641040710080c0c40362104d4074100040b44403200300520f020818010b5141c1103106403024002180000c0307a04000082100060064036450905070711001003080042c008e11820340c0045 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 57389104 1250 57387854 57387857
    0x180c0c01021201060912050607080c09060703080703051303140306010504031b08010605100518030705041a18040206030106080406060e090f0705030d050d110706050c0703020705091b0a 81
    0x200009000a5024401811010034500100b20b240d07241c04405448a00b507a1720032007038001580b0480001490225006030300c2402030400340c0c40341c0c079482654411270203641040d582001c0000303210b0040c5600494020303c607140310380e42882a95565401401e08041080000300030441164008041e2045078014660051045c0740050070144d803038803200c40109001e5004440359690307000c1409403150a0007000094101902c80100c031100062000780030b445410307403c901c41034100005142503601407105200400e0010001c0c085201000240700ca1003c05264082c482c00000042d0382c01e02442c04140c40c0f20f290000d01c000d003140e2900609440c1c1030781c0200b08488440c2c0d151004141542d0b44109240900d0003040140200c7c5900e91a1510300026604031038401d51050b038065030301c503a0000440341c000f0042c0304040ba528100450300a514040c03503000a04c03c5c0d05200800c14074007000405021254065402c6030046075a6170181300341d01809072031021200116442490700501c003000240003c3e54103 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 57390354 1250 57389104 57389107
    0xf010c020316031a0c070309060f020109050105160801050d030504060804062003011e080c01050906070807030c0c09050106080406050403020f0a12030b012a030216090606120506180c 80
    0x100410520240c0580c20440303001003051121392103000300c41e1400741d2103501500c00c00e18001550710054003840d0b0b544640810000c10010070440c1d01d100790401c3c1c036403640c080700a014600f8103038064801d01c81c04020070b10005110900002d0185000c00f00c04044c55099200c1c9440c060500300d0071a00d0240042c01034503129200d502d030183c50745440c05015440040c02010540b41e504044a083c3c840c007940c0410810074070614004d100b1204003060090301c915003403e2080c0d82e050140003050281c041c0e10000303409104085441c00034540c0201954072441c0c403542c030004640303480d000c005c0100c44082c000d0a000819940000b4005451503000c180c101d8084d0040710324401480040318a031481c940c0003111708030032680c900c61249425005403070540c01d090a000000c0394600c52600400304400c080040121400e400c54402d050082c405c508074400000b04620382662244a440050042440b8440009d903059401c07200101e428451207004020041240681c888100500300c0b2240014110b94a070860 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 57391604 1250 57390354 57390373
    0x40f050f0a030507080a030e18010521010e010209100513030807020402120403030c02010f06052d03030309010c140304020f0d110607051014070203190e061204020405150f010c0203 79
    0xb000000014205d042c02003001039a02d10f8000c0c001c20182d100301d40034800d4012150356500da5000c800303040d11070070740b0001c0d01e641604207810050000a0003001465203030040e500d42d0040107400800f0bc0d0320302038824142039076080200701c0e401c0c445c108030342d41a210031500a01c002410030000b480100c1c0010700c0542070030072a1005a02c0c0309016603003140030075640c88842c404143c0a01030b4a840b890b210508201c0e10746044045030b0803840c0a28030300112180d4140c040818604407910380c141a001900300d03a200d01c0c285a000d4000e02c4014002c00114588165460241e2440d1086134403490b40034215403517500561092000b019400842201c2050707940c0300c0312030261540c0014151643c00b90300240104044a040102141c8680c030018001401080421003641e40000c00c55851150342c5aa070328803010306007021a4500c18000c40c1c294401800950b0444104015182034002c0d03008560401403515010010034a0980c09410103800404410704500250701998141d400c00d0b0000d01501ca0305003 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 57392854 1250 57391604 57391613
    0x605060406080a050f16050918070206010e0c0301050f010f03090602030a090b060f060703111204090e0607110712020a0e132603011205150f090d05040f050f0a03 71
    0x8016411100000b2060070401c100b1075030740e014954002c4c6401030511014140340c07000307019000008454030305126000603c0303605c0e51107a140c1b144a294404082c1001030815401c029254402881034541492141000c1070240ea1903100f140c0c12540001c1a01c50200900001995090f040d4038070300c000d00d5030700c00f00c000100304640000d610a0880f1000040e18013564a080c004d43c460281c200d41c05100c101e04c40b0022b686820045424541d018100359480040d1101e40c0d903d44401541c1e0030b480760300045400500b03446943c201c00d420340c0f20001904c00c95501c29408803540c5a011a508120f9032059108001030201c02c043c080925001034041103149071107282951140b24290780286010400f02081014810091a03000d880c01030700c0b0790380e2451164146050341c07501040c007511a0701280380b4108010001c080000d07a83e0504c0c45140400a03281103c00102c11800407141001240141402d00450a210382c003102d090700c404059000245083c0b40502c05010154800c254228420920200124 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 57394104 1250 57392854 57392857
    0x901140c0306031005040803040201030914030f13050306070207231c05011808090f01030902100305040c0b0702030303010b03100305120901090504050609130501021902010902031e060f040501060506 87
    0x846180000c181e60b400d00109261801290b600707150701c0e142c5031006210024805600704c90f001502407070007040b0314101382490418054003845490180c400090850081d80e615806400250a5540141881c503690400e26450314001c580780401a00b18400030700508000100400302c1c07000752445a00c0c0c00a080c804501103441203500080410b0a992000c010890240500b150501904d15000f645843c6540c41640305d00604010504c1850080354062580e4425072112080c80e070000c1c840007080842d80c3e03020300248029641034030050006100803a064520004581c11244d024005600d503030728103201054290005804056450041c0314000080f07001084408600c41c0c000003060390f00c008090016102000c1741d40301c81e0140b41058200700700d50f540d403418030745d1004d20840e08880b401103d00e8070741c0c0203206003100b810340b14440b0901403100603815409805014803d604542c0e10a990045003802d0390782c0c002c041c6200703a0282d4002910300b0b50321800c4640091282c000461141d840e500000d00a = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 57395354 1250 57394104 57394111
    0x390a12061a0a0303080f09030a0c110409061127010c0303020711120609070509010b0a0e0406090f0c08091603031b0602040608060907090501140703050403080403051c02010c0215090114 81
    0x9071351742040c0b152081c0034152080e00f0420440081d450040301d000b01900310f28881b4000381420350b82c4c8500c41141e40756500001c0100d80d205004020303028803c17148941e65008410024901000306c000d04103001c0d451800c0401e8601e058481040c031a0155504801940c070603002228003041000f41031608d40c58035801c0600d4098104040c10303e80c030b44900d10341d1524130141e000b030f0f210320200c100421100c0c59031400c88661001a2030000b800c0c3c402c0d040410003401c11035000e101110b142040d105680c01a980c4010030a402c5079890b201a030700c0d11904c4071f40e902240c2c240000f46040c412410000640600303c2000240c80d45400c455103840c1a486010407a00543d02c001c0110702604104001d40c41c003000c00990000150901c90411400d0400080c5a40404101d08202600000300c690516003e2800e0300c00942d481144155104c2e22481e006403642a820340038031414078050b5401050310300600070310200115076030046c02d2581e15102840222807001c3e1500b1455543c0c0c1c9901d84400c48446c141511 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 57396604 1250 57395354 57395357
    0x608030301030605061f0c060c21060501020d02011505060a111903080112051c02011e0c0207051509131e06080c01050a02060a0203060102390a12061a0a0303 69
    0x442e890a0b40501c04100083c0141310080006c1c803c0c00c1071020341110f60385550a030020f00010b4003040305103040d5030f00040c0aaa080c000310070b10340b080c60014030f04e8000c0d400340c079802e0b07081c0c5e140e034414010b0981c00d81d0400d03090080000b244c82400d010606002001d042000303040d1610201e00b005e00c9071850305026003840100e0b215809043c616003410341104040b8010008000822407001d007548400b6140e580e068406042c42480310381c0d00107064401d400c03401c40c032000ba654488420030034820344002003546000900240c0580d400008040c80c00003c4c400d080b14051804620b841396140c01c00c0003400042003003c2c00b141d991100030490000032285c000b00c4840781240056007505000e100e07031078074480d0820b1504015040284603403060340071501a4000c100e160340582c49469440c0181e040c403413480160005003030b80c404c907560030409c0c10000741c0c0c040411058015040741490f0074050003040300d00400b0312510b020880400041c8241d4400503c103000070341c008010a0712800000c2c1c44800e180d0042c2c0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 57397854 1250 57396604 57396611
    0x1120f080d02071a01143f12030105060d0509010213120b0f070207030615080f15070207030c060e01140a020a02182a040306020d020406170c04170106080303010306 72
    0x410013100a102c1e8040b240c034503814850a40c0b4101d07801209200c0040d066000f00c0411080414008042403825a290412400184241c071007016051400201d2044503915129840300070809100100440f4140c031400343c401c03440c100785e15804002500c1d0140007400751b903608005490701c002d06480280c029040d501c42c0020403003d81d0030481040003024044450000807041030000342d40d000900d0104030fa900070004100d60900300e040e2004c40d911503020284a000303400c100c0d005564046149850046d0503038188090743c0740c0b40c8049944500754080207042207070203031041c800307640102480d0303000003814541032020101e496295000c58005103a0070b40036a03c4540300308114900300001c5407211520030300401141c0b17003240c8034000781e00c441109c0131540718502624945060300c280c00ca40c09160842e4082d0360342c0103003c01003002036200381704500006000d243c91203014480351100b2030250040a10050400b41400004c46105880d6409407500390b60f1200009030b26901480918003c600440000 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 57399104 1250 57397854 57397867
    0x8010c0c03023906040510030504030813030503072d02010c090e0f060103020f0c01140f0a02130501081003050a060522030203041e12050c040606020106050901120f080d02 75
    0x3a00e010240fa4400103e400e2203000fa90103501d44803800283d0b85030420761030f0140d14816011410610550b0403003078100d40030102c07100d02c068054202c68001e0f07200395030b110002e903071b18050410b0f050560100280015000c102203452076200382d0060f04d107a034a0308881c42c003a02060f2081054251007101903c050b0b511001001602c50300110703164006c1c0f0890040c02e28510f002d4641c08a1410010100c1e4181540480c914a11050020554690f1301aa20080094242c02c04c2c42074003554044625141c01002032000030000b030014001e03034124070350041000e800e950909005584104c4000d0000c0b00d4646000d6002011400801000c0111030003004001010708152310781004002d6580000b5182c22050602840000d81c0081100c0813118030480c0c0320b10702410081204104461680001c0c98649292a24000d014010880140e1a00200c5003004fc09542d082c0a0382a14128030a407035106039003000400440c4c141c141c0c08660103100711802a0407500329a6039501e40d403c01b0b0002c02d445a40030406 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 57400354 1250 57399104 57399107
    0xa050a2f01050604020c03040e04081c05011406070203060412020c040204140f0105130303210c03020909060f0a05010c06020d020a0203070510090c0b090f1302090316080604030507050708010c0c03 86
    0x60b590071010648043d840d00288200c09a6240305601c9104290b003600c0001030103000807601074403d54803035014010395040081546002800c006e0103090100702e2080c0b03884540745000000c9814141c0c1c00340c0504225078890700e54882d1800c140942c002903020b01c901d08041a0b44520040029201d00e0264181c0201200f0038080d0007101c4010a034103120040284002c840c5803240c84504813a030503d0b041c405102d8841459001d00141c5d400e030300e505410840e01018094042d0003070282c1000070748803c080c65880780201f040c011503043e565508041d103d1000e002a52065030413101b801c1c0607010151410b1a200c00001c1280c0c8000c80610060b080490f00c00100034041c4070b13524103070b12360071001c0c08401c00d103880c2c0b601c0002c024403401c2e05805000821440c1c5440b0500c0d4404103600080c0402240110b00610a020b58403040d0960b1090059107925454101e180841100b99101c80004041e81c0d0748544e000d440c503500003a011741311032240f03050025582000340501c114101c07441ea1a440c0c0c0c4030740c6180 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 57401604 1250 57400354 57400361
    0x1502010e1b0102061b070507031212090b0c0703140c0a0b070c0803070c05101104050103060e0f040303020702060403060e030703090806151011030d0516020703080a050a2f01 76
    0xc1c21008035a1034800408140c0e4002038484d0000f10466071401d144000034040d0803180b29904000f80507000300d1800209201115120980020082d100d04000f00343d14102a0100d0712404801012002c15401003810480340c3c0000e444424800d0402c9445051410461401034110b001445482c4c1c1c00420910200141622015084181740c00c044010502030358a90b4114000140b0b20820410009550011b0010800c1030f801c100007081000c0101c0c11041d005814264414003601e800700303050078800120350810a03403081c421003000c01d52015540302e6590481c040d500c100b03010303684030000f4007001c8049612440740d18000e20601004503515170a0340f0300170300082c02ca94042d0109400a100b000100b00b854140800301180860340d00014014100701692183c0c01d441c0341003860321001c6224060325031107034003007802030f00b20100d245102c03802c0e01e030120794922590000500301c00c01031146e07400c4c050207940a0314540c440d17814003000c50340d000c13078500c04000c0980c5040380703e41021844500715540b0a11 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 57402854 1250 57401604 57401623
    0x207200603090304121e0c05040b0f01090311060702060d0b101704020918010204080604020f120d030209041b020102120105040501050f13060905100e010f050d0803060a1502010e 78
    0x11422400c502c1c007105060340342d000340d01c03450042c0b14654090000f0172030b5078505514950101200000122050b01b809003084180d4060b16003c0c9142200d03050040c0340c1003881c0d00f030300e500507541e6450260455540729052500000200d8200c40c05009240041c1c0d255405085480cac0c841c400003030b000032098100440110080703502014424941103071040c50701d48002107688180c040d207038800d143d1501b030701d01c84105000a14001e840d52000c1004030700c0d0f00c030104506004600072160360a869000c1810440110b29030b04019030760303511600300d02040324041d0b00640b070503100040c40040c407061001180307443d02c1d600360b11410040c1d50003d0302c050414000098140503110607a000c000035030400b00856400885038a40c5485501e001c02484104841600103401030609010203000320704081d1000b007140182400350b502c590039601c0c0041415281d948150b012142c000b0b085e0002926070780c95420740c9034005024107401040d03866001c20421480d080204042c07043e6070002664440072440d0fa070400e01c071803 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 57404104 1250 57402854 57402859
    0x100507030e0a0302090a05061206130c0801050708160306080a060902041a030c0609030a050a0b1905060102120a050c010603031d0117060402090d05060403050406030b06030415110409020720 83
    0x51400f8005a04c3c0c2e400e00703590004540300c0c0002d1680303c0500150000c4031010a000092241404001e0342d02407180a041d0582d00c12090090019100e170185400d95408541c9040050a614000f4070722030550804138069044508000407030703a40b200e0609007441d022010942c4d901c0e450f40313050001c500b007510404c54075510307070000c1180b11403154002070b44610a619100344210b50100e4a0b01c00d42e68184160f580459209040b0b661951107850911100300003110035902030700e100c10303002000390034501920b8070a0005a02410100058954003070049c0c1209106000300f240900089401c280300340301c0da50103540640c603403003207500c243c40c2c46c4054180f14510450401c050550304107040200308600c10f400600c100c90240e110204100030690034580c05001034400d105044c2440180754200006000b48c80c126078044c00042c140f0000d0100c2c1d884203441c010320800900c0c0038240c9003002580006c140914003e82c603450a076462101c001a608020416a4012488203a030f4110f910350b00001c1c1800c1c1c81c103 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 57405354 1250 57404104 57404119
    0x5090c07032f030d0b011103180907031e09050f010605010e0d1704061101050609250e060403080d0b0307050a0306150b2d0f0d0b0f100507030e 63
    0x5541c02048044560141c9191401c0ca00d1022020522100741072210090740341100c0e00c50360034520a8019002e10305201d03000c0740207240725280c0800c000c41203960174441040120090082107051000c030300001030591080680d00d0028450140248039002100134608502107004452810f00500f08606813020741441da241c0700e401c10490341c01c44140b050b40c1904903051b8041c1e0040b13043c2032100c10f207682125150400300150100306560803a0000c51030110081c000c10807a640c01d003c1c08000542500e405440813191038803d451400b10b503c5903225040c035071800149585042c000b09802d50400d40003250f6240c0042070746181c0010720321070031840c01c42c21001030021915000201707028800501016103801d45561004540c21020000070008260314600959559200c0c00040032250803c2403184045a840b001c3c41200418402a83c2c4004000060f01c1d10704070040300309800a10140200d141c12450940c0407100980e10100607903c40701e060b85075181d85420700e1070000d01004503030851900c603980 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 57406604 1250 57405354 57405367
    0x1403070e100b09040204030f08250b010b07020a03050106120615050603011206090b040305070203010c0201091205220602010608070602010c0e010c020d0f0c0f0e040503030708071205010303020102030105090c 91
    0xa040c1146822640100b00103a66401e4440c0864040d114a0700054444144140c07588104909030300285140940c040c5480c0d418401e043d1500c0048201c445d0190403044010018040e004880004014403880140800d801c156260b40301420740e82154030004101c560313420070400f0310045000d11241015440100c41150703080030f0009074540018042c042900b1036100031030080000f203a01090446801016082042c078003468004c2003540424001c0303000f9401c2c00845226140140110030900c0e500048400900c105400101c48a030829410380030718008213404001c042c44008140000340100f41e00100d10b860420303d61904c5e00d280fa0380321030116890115420840340d80a1081100880246089500c52466000117000b0109580015028442c0300314010104101d40d400d12003100c54441150984d150396001600701c7c803000301e401400b141c02c104006010380c0e100d6212a5442401800e000382090003102e034200840c1c400342c1048000d0f079400001031010303240003441c0c0740d840701000900624062 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 57407854 1250 57406604 57406621
    0x9010b010306150f09080609011b030b0310050603070f1211010f050d020304141606030507030c0e040f06080303040c05041b0f030c11010905010b04060f0503060103080a020c0a1403070e 81
    0x40d03c80710b218200440030b041c81c11460710070380c0980002d1101074200c0e00381d81003550009000b0f21490070170011000f40b68000082c018024000c1701c0001200078013a100103c4004070303803800341c0001894030b541405800030200d81d80410014030707400750401c030020b420620445d2500b20341140b840110181401825065070035074a07804012210908200040941c03641c8640c64807020100d41340311030400030300490b1100011581d06511101c01c1b9803050b40c06001a0700c541500b03908658481d41118001103405413605104d04282d04980340022180ca0001046940c4110701420754001b514125004034020004109514007801100282040b080c08145c5007103139001c0207020308032031007540401c1c941c60740c0780d0450250081049150040e074220003444a0003892400b83d00070a5120001c500c2a0314064010640c003800e142d02e54113850029000308116402c40c0c80c0e00245402404c507450440c4039509501c4115203179108920f005240c50400401600241c0d0201400c1400640011202101c41e00c03c025482 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 57409104 1250 57407854 57407879
    0x605041104032604051f02070f0b09010c0f06061d0604022503030b03031b011a282c07080c03130305070c030516060c080409110702090c0309010b010306 67
    0x5012a5150421940d5050f01c01d01850155900180c0d0042c0c45030360b001c40c101000e402250f1a900f5a41c203469500351900c00403800141c441c01741c42c00300d0700103000076299940a41c00d0109c3d214010300301c980034140d00f66510020b0b00c1490b00045066910882c1e0020b001101d041e0171a00001c0072a029810031000d01010b4000004400130111176000b0114174006050081d8016508560040c054a42d82c04050400c8000c104850342d503284158a40380c807130400420414050040b140006012000340e03000001c5919054956041d011620501c0310b500080380d55400760751081c26405814010000303040b0407412000c1503001454030042c0200d510030880d01003020000c403907025100c1c020f18031000e1002d08040781c0703902481800900b0081c2048020043c498002000c024851034801070200182c0c4032202120130140c00c0c0d01c010400c42041c04144004495034004200c0ba14984c030f030040c104140c50b00002e1600c80d0648002c0406207002052042201c42801040200036007801c05205640ca03000c22066034 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 57410354 1250 57409104 57409133
    0xf0c03060f0a0207020306090309240d02031008010603120f18030204020a051b210c070303030f0b0402070c140105040f050907140d05070e09071e03020c0a0303060504110403 76
    0x7005220005031482e841a8140c4020640250071106145030040000e540d035441408500e1290000d2482441002c058a02050303640c90400e070740605025400707038a800030390000307404121600e038050000b1030b150409206010046000c1c0e407410001464486000d0448000042814100035003d180c480448200140c050201d07503066070f0060340d410354600300729075602428600d541d65a0309012408901c100000f841f4a2111840c103800d41c9142c03c0c6880c4000e00c1c0315400d12070686400c041410004607002e070788041801805441c001c50400c20b10000181240c0c8034440031100b4880403042171110404a803180d1f0440002802e240349402d050400300840b00302d40d0b206a0f40f04020003400a8400c030303c210003800708030210301d200c1c81d201d0300c007006503c01130310044402c2ca0002d404424070810a181185000f0701440307103500c4072440b840800c045043c101009590a50038183c08000c510f10480080041c240d00c580a944c001070020b0902c4200b1040d01c0e09202100007504061100340b020807100c8100150 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 57411604 1250 57410354 57410371
    0x1090b01021902060409140a0c0207060c060c140c16080c030a0605061c0c06020c010e0604031e080a0e13150b0a03110a05040303030e01090302070b0904020c030d020a020f0c0306 78
    0x2050360b944002155846683c000404050804210a2082e200b92410302d0048003420014041c0100140040f07990302c403d0701c559000100380782c20020125884d40c0c08040f03000d41078a4840e100c0480032107030203150b0340124103100d0f540d803041800e001460503045440c800f0304000c50107001c0c2080c1d550000fa41c1c645078040e0161400d039507840818041d5070b40145400307407820648600c002c220000d0030207003412802c40c032543d0050300800059205a610a005072080b03800004e10381c030b00381415902ca14540c070b440514014040c80c281c43c1d092000c510761201030700d0307100402e60310a0f920030305d0401800301d06030b0010210000c140c2440d0031f40c216284800b22b60000c0c0c510003080240c8a03082d03489c086001e48841d4a10440707070f0300d00040320300100d40d0240c02481aa4000d807028070007840310624460880300501e00c0130740140c001003c1800140341e044000c1c9400c40f00100090b041180743c07140541194081005010715581c0001c1b2909000d4042c41420a840c1090020b081c030046202c3c042074075094010031380d06 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 57412854 1250 57411604 57411643
    0x302010807210903030b03060f040c03170c060406050105280e270a11011719020c0709150b07050d0f050c010507120e03040614030406240303030501090b0102 69
    0x2040310220346808401c000b00100d0600c4400b01c1810058014543c10944500038055080014216000b045010740102e90011100d01c9451031625001d00d68444a1200448401d04010807011a0010806107000740e02610001429502d842c04000403d140485142c080504155440c030001d0030050301c1000b100d040c0c1d907010545607105a217a900c084010007410b14044d40a84500c0300010300002c4d43c0303115034420000e0800f200d00c2c5800540317a800b45400d40d842070600c10800034502901d460710740881d61030a44009410400c07607510032410a00c0503004820501e1b51616810804810424028000d110500c85245002030b1512501d40302c80e5440744400c244050301700c0c891b02951249080301c2d40446c1510080005007000000201003d00030003000380864101a040d544200700481180d08882d510785500142140c4918100010b030801070096400c250348a008054454081d50028541e0b03800402c45211641103181c003404980c0d040e00550300c65445c1400003034899800040c1c0130b445600816030107 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 57414104 1250 57412854 57412877
    0x9070f0515210901020a02060f04020d170d02210f0f07180504020c030901020c010212090913060603050d1103040f0b0310150201091502090907080c21040203060a060302010807 77
    0x41e6000031541156200da403881c03c00c442d00e1019070281c150b9065550035a0b0281c1c5920104440240060764046c2d8441da18091600c00947e40c0001d0455004009402e907040a11504001c1d0032a0130444140440c103002102c018060501000000cbd4040d0618001440500702001250900318006155809211842d1000031090a40c00d109800502000380295950b003186a981510303034010121a9000d48121410015958008140843c40b412100c518030304040d940c908200c15204007404907281381000790005404606240180c002940c041c00041c0400402603400501000c5800000c0e1038a400902040c82500c1145401008855184161a071603440d0300984507485482c6902249560321a00b001c0c42e51650103421001d1080d000313880c11200e01c128203400105911680c0110f07980003400d000050480f0b40100300964200343c01000c4035080040c4030f038007501c0d5160842000118407018908101c2140341c200180c0743c0c0f058104800b030055610310390000c2c00000016003288180a03420044 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 57415354 1250 57414104 57414127
    0x15070f060902060708091c2a03051203091005040c090c02030d05041101090b0c0616020f07090603020a0b0a020a080d02130e04020901170606040f0b130509070f0515 72
    0x8200d41d50700142050340d00e0b81c003440e210801e940315215460040800300b40c0107200100346e4042464194004480c40381c402c0035650050101800b805400c81c01200010020020400400040c1c244803480c03c401070756410900c100070f16042c4205d40c485e142600700030800001070b14200040c403c4030203c24002c02e01c0454404240e0440c028031801440d0031746000100401d000b02e0502c010ba4200e000e0721341c3c416031910b40344101541d02c5803e4000b4065801200812180103108009180c40030180c41039a00b103018406013141001c0c3c1e664401034015485103020f200750f18280210000400785092241e150044090b0301a4442d081c0010162521502190303804404031145c0407102c3c205481451800f9603925038811a02c3c010094400364054a20301e80041203241c07001c410802901002801800140d07030b50800c10001d0050403581807407054480c841c215448e100c6031030041d40c1d0040900007103040d241c0b84003060310308403c66012403450b0012080800c1035498070001c0c520000b10090301c055498009006 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 57416604 1250 57415354 57415361
    0x30f070e0a061805060a1703040e07020703020a06020708010b01030216020108041b09050a050708040203060c07050a06050901051602010b060f1b0a120e010f0906110f03030c090103060515070f06 85
    0x4510b0b20640304540b860b200603c0d650040d4814901110690f05054581d01c1641d00074410079032864581c1d00412051069801d41a60180d000c0c140c2d00c121222507881c2d60108050000340d900c200c0140e4071501c001e1102000078040c4801c50b08003071a0450814280d8042403031100c80807000a818884464041802c0c06810944030340100407020541c82c04550354a036800c010101160740421491070103010442c068400c5613164000c0740c00500910700358030f0b01c1d28518026031001108072182d1060b001e110001a8050144e14801c031b0107107000045c185000d05a40b40400f9100d4403400440e4500341170240190b685100780d80f4420104942d40e5141c2c5204030014941445031109401c1a01c10f140c00d0408110048030174091304007841e0381d4075072505003100040d207902001c00200c0d0007180d401d00f024415244604180725000062030221055461171030b52242c00d41e4030544c2c441146040018103d003d950f09070240c3d02c001d200640b14840b12604020310409240280d040080c8049002ca12201c10312090740c0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 57417854 1250 57416604 57416609
    0x312030609060609051504050a2309041a0f090712020103021c02130b0307120c020a0c06120606090806070522090209040c170c0c01140c0304060605030f070e0a06 71
    0x10000c0001c543c5651014041d00d60034402c9a116005240300308440e5400312044e078080307800c060f080000d124140440000c050002c0c02c00300d01010050350b1740d0000b40c1d840f5465140124020f040003500303500b120b841c140007014000d0099600f12014003e0101e2018002807003011610a802c02000031b510601c01200030348210020149820755442101007004410350040158000d400c0601c456140e550300200690b0204490010200e2224002611120190b0304000c0e0200c25a2054400201c2c0507500c8440c03803909070308020001951103075040701c1482d4070311070a0050b081c641002c0c4400340c41c3c054119614100200000200800400c01a054070762503035060159840003030740075410300c1c1c455941c007000b07412141c0964451410305100d0320209e8000c100c903412942580156491550325680c45a149038400ba191040c0c07590b0f240d1a00c41c5401110850a024400816215580303042608100055800c0350b00400d11a4002c0850b0000303803040000c200d000c03102024030012040c1d58409081c0010009076 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 57419104 1250 57417854 57417869
    0xa0e1501112b0809070b0a03020a09050303030f040201110a0b0606090312040b0309120304080702010c020f060c100e010501210302010b060f09030d021612050109050d0809060c0a0903120306 83
    0x54807503440a810842c0c02d0380966603596a980c25a070750154515501c0300d451090308800e003010070404a85520039002000c0900311f80c1806915a81d446e00868510f07031048807004134918000c020f00c021507900c400c02000c032101180c01001084603940b0390700c2c060000a0055807140c4400540250f01d0345090120360710000c0040c0e0030584841e81c41c0301031074140d401114043d06500440e0750f0020660000801e5a018541000445042103010380c015284081d0761710dc01d036400340c1c6030100c4140300d81c1d03400b0040c0b1068066401034400000040815026150504c04041e4180d0400005104085000b40703081c00c9030401e200c0203c039188403410107a00400360034900f181c004900007184491200c0d0300005100a4406030100c49010710104000c90b186c0000741c0c9980e14000d40c00200b04003078040c50701c00a16607401070000058110307460b6031f0765142108810000000c101510300700980d8403424002603502c18940781c4c00038681070942c10014891041e90200510031182d900002240074400d500180c080d1800 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 57420354 1250 57419104 57419143
    0x4171002071a060a0b04060e01031401060207060e0306040803070f090302030105010b04030210030c0e040b030123010f090c0e4c0908070504020901210501050a0e150111 74
    0x780c1040c0c40200103110b000000000c001001c40c50a04040e001501141c212402550400381008000c940c0c249030030690314109900e032489400c40d002800003650003820503400400c680c51400c40c010344002c1200c10128401d2f0000b808110102d8a000b040f25403001003480d06411810004070151006410b80c3c00194266103030000100c4d02ca00000300400580307000715445030100001c10b42c110159100907402e1800a80085640039842c04c107034110340c6c980c5200600115030f040c8800d4030080300c06025040c1105441181c80108040180b0545030702c00780017005000c3c001500b100001802c00304211072410300031030004805004880c4116104403546643c02440313107051207848403403545c0b4800b000380f103003100c03104c4e0454020f094007418442d800c031092a0040c2c00500e2030042080001d400003403056040c80007244201c030003030f081c2c41c00c4030502c854941d40000e4954140010f104402c501e0b0380215411400d89014406880c1010840141c0304074246464104036050100103030910341469a001c3c1c94010 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 57421604 1250 57420354 57420367
    0x20c030c061204170c010c110105060a03290a06050a0503030c0d050f1b0a02010801050315010902030a0212010b0d0f09110d0201030f0e03070501150e01030b090a020a0b07021003020f04171002 84
    0x6412090381447c03140e440b145d003010b404140c5802c0300d40c103035034841d4030042c20b0504000103440d5030341c21005068000683c1d030143e00801b007401c103592401c07110401095600c0d0028446443c003100035101410b000e400031130914001203911a81d4211114683d403c1c0600490124070242844045610529142e0f081d9464444a800c03220340c1c0c5c0e1248030b4100d02060b21900081007605000861000440500e84007101591900d48004001e600141408405940811402d021050340041d03050080c0b12011641d81d9407040d29410008a65040c2c040d25951750500720500301107445e010301001100e000b11140c0c00c00f00c1280c40140d000300030140701170b01c240d81080361101080b1804006031584a0090303000307000440d02e00c80300c4070609003140607030304d101c024070001400845d10300d040741544140010f0031100c0c81c5d591900010a000c0080d4002c507103d12001030004d01710f003090910300010083c00d041c25400d0144000416a642c042d44c040d844070b9042c01803603058801e100300881110048110000c540c0c400 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 57422854 1250 57421604 57421627
    0x120a020f0f040608390c0c030f0d0801060e0d020105130807121a01080613051203010e0103110a0311040903020a0609060e06220f02060d0f060501020c030c06120417 72
    0x6040303440729940d80c49081082e180c03d1355120950b200c010611010b40e51501d0380420030500d41c0201d00740032007c0c4501074482c411900d040080541c0d40d480107000702294041030320300606a80058001400304004042d8000454460441008000d542400c0003a10f800300803880c503c0d41210ba6108001d141305220300003d8050341d1100301d001540c0101c00785640c0c020080e9070a418960207105501242e4007400000e0b40700c254640c0042c45c032522034801d95800010326501c0c0d00c9190401c2e0026580c600502004000704186070b081c0148004040d580040d02c0707851604c4e03440700d1891581c0d00e1801a915410420101407081c8925602030780e114008028000031400c1c0700d0000c180303041d9641854401d80c800701d82d48401000c40b001483c042c080071113034046a541e4820309401c0c600e00080360003420034480303249000300780e00540d2149044540000740c964909000280b40264841545000e03801164150b40d80b510303000101d5054a0b0b446883c1c11103900c881c9400c04003103800380c140a1200740e021440f0035242 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 57424104 1250 57422854 57422867
    0x1120507050c011d1504080f04080d030b100c0b0711010e010605030705011d0f12010504030809160501050304080901140406030606030c08010e0414100609150902120a020f0f0406 78
    0x4560762002000448a2608243c0301d46132507190344071169000c490581100c0c18030307085c0c840d48540f040c0d030a6400c1064200884945400a4000c0003e58000080706010964184604140420202c0d068004110081c402800200c103030180548003030f4404000030700250248207440c100c50400002080079207d8040c800d80200301c40c3c040c55200707025003480000c0640c41106415407940e5480480b000703c1510000300030440341e00c0d03014590051034000c10310707602c4482885a18400d90080e11080202c1ca40500f045007013224800c02001c010311071610030f000590b40f00091fa948aa44401502d59800c503d000590704450305030040d042070400041c01040325a0b040d0014030441d0a5928180308041e4040015103a0200034058421043d5041000a0114404428103c081c030b00c00300503500b68413464540402a55596002010000e45841c2c02691802c1d042c80204020143d4410840c103100e20a60300d80c4824001420340681d144d00468210b8030f50009504a904103540c0061050b03461fa41e990300549507 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 57425354 1250 57424104 57424117
    0x2042705100e0105010b040b1e04030f111e0918030406050a0f09120204020a091802070b06030303070905010c080c0102120105040b031b131509061a160308060112050705 74
    0x1442c2c1040b0440746185014002c050680d60103840240c2400e0030017141c08016084a00b02d50440f00031510b084422028620003080a14055900407101c110582003011070202c403064003500a04518500c1c00d60301e100345116030880c04084441900d81d4590f01e04880011a035828145401d0000050000e821500440240700701803241e00c2e0001481540302c07050303c06c60000c0c07040900400a40e400c04005140a40c003c003211280e90414020a13615000d40070820202c42d41c441003901da00181c07000501190101c0140d0041007100210310318078252030000d00c040300c1881174906100d110302d1885c080084030070684038025041c00003103440314070700b0b10000c042600a03c6514040c500e846030280700c600340401d05101d06682e40d00e03821004000241441030511540500040c40c076610400803240400a528000c010060404049422424103002002d8269440801480e0840420001c1c0032008941d0001e5481074046c1400c4585039a5240181c81d0309140c4c040301d0200900e800c0c100480da039040b5010f40074 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 57426604 1250 57425354 57425383
    0x5190801050f190c050d05041a0a06080f0705060906030912120703060b0a021b06090d05010902010e0d0c090f0e0d020109030206060102070f180612050a02010810030f02042705 77
    0xc50841040380703d81114010140c100c0020030402102103155290b40000c3e030020303c01e0a0f60040074510004025801500351103c02c105512040304203c44d40041100e1a510b0f0004405041c6092800c00020b00520807014200c6c080c080220015480f21030512102d140c1c10b400589041d034441440d000008001d00880b1401c0c080383ca0310710085030f650144016680384844d1030b0028002091030841c0a00502d284403070540d40300104100320b29503612005a04000c0038411000030802001d41d01c005040711103c291791a00070362210030240042103100b0b0720703842280c0d41403400040a6812500d642d01900451a540d800361140340075a00109605501003260700d402039003922403d40b00c1c1001241c40d030301c00744903882656232080014407008002594240e00b10300c00d80000034a240d501c60030014810403080007620135802800c8103000795600200700c01d62142d00340c40e000d03017140e0071580d8983c0c144a000c90061302440c2d80341102e030b4404642c0c0c44900c8020000115100208569282c190b0b91520710b0b5150030f0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 57427854 1250 57426604 57426631
    0x10207020d030c0611040602030a030b0a080a03170f0403020a03030e010212040813080c03070504050903040f0b030106021603020112021b03030a0209040b1f110703060c0509041409060105190801050f 87
    0x1d0700e407030f2003101b030310305a405580c050751605100e0403088018140300481c480d0307c107021043c00100c5903403c0004454251203903c030390000e1903ca000c900e9580f4001448030850300004810030000035030200d88000320b0350345400c0c0003800c141c180d00258024010300841c6668801d242081c0300601113980003a0441d00b60344003c409030282c07501d808540741c12640030520b805a020780804c7c00030b4503254200c6684a000041201d040c255151024806144a83e00c04801c4400020040c000643d040c06011101820948108002807540c3d0008080b6511021b0020170349601145920760800c2202c14840d46c500c10000701d80e22802c14010b00d00080d8441c2440c0341c46281341a48606940c100014080400304038130f0100b07203480390703040d8081d00d4003806401d041225001e0207001100094041c446e00300c2d00e2200c0c0c0d13072340c40d2030701d00c02010b020031182170b5900a100754030380c90100264082c00003190b83c1901e4040c0c4001411350003200304d07400c05c0b0103182c005590b554244020009447c111007034513071142d0030198022 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 57429104 1250 57427854 57427871
    0x1503070501300b031603080d0903031118030601060e01080708060103151512140105060304030507120c0b060303071112030408150421080a0504140a050604030216050a120203010207020d030c06 84
    0x100d45640751b440000c101800a020703548020056a20003010507000c0c0c1408200c100400d0101c0e150b80c1d00075408515011303901007030030350a0305082024601600b0030b03007000c4824a8000300007038046040284008100101100011807603413194010121318252110500c2c91280c440e500c0d4038828200c0101c4000040046510220384000e90040c142001311500c50500180d09120034042168030041041d010711508011030800101c070380c0c3c0806c7c80008140e5403100800741c82e00d4013038400b80d0040d20281c4030354414454140460070808030f4041c0c28204840901c903208003a000c00b4194059684180c01038040c41440c045e03840f44000e06948264410000b0080900e1010340000070b041001030b0020024001e40005030400070254011b03034103d40140c03003005100780c003c020389140ca010a4421542d03074001105000405404000d4138907030303100c0c090500141e2800c0c1008a04000100d20a980052031017400d0322044d505d080d41200c0605401038008001c2085030f0030040c00024034200100d81d414070b00b0102c3e = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 57430354 1250 57429104 57429133
    0x30c11010207020d080a170a021801030c021c1b1103070807180c0e0d120f02030406020a030e1206091608060403120e0c03070801141503070501300b03 66
    0x2c0320426076000f001e001100c48651565030b015044410354109101d80c0013040185032142e00711031403207002120005a46c802083c01c890001440e40c1c5001410b0500700107c801c3d07a1a0081030019000f10200007098010b500608203c8411044460442043d0060110903083c4104013024190b0170409408850460303654405d011b5880c0b840b4401d0800403075880540ca202080f181d000943c000c1600d1418103c2d080c40c5c00c0000f120701444480071501900794842840342c4c19042083c45841050500295080c1894410065201c81580c50014108880b664090702aa81e42c2110140c0341c1d0840030842d1014541544e519544c1c034101c21030040c11052018001940d1074002440070310856044c3d881d603840340030500070700000e01100160342205c0c0c0118158201680c50400800b8024041c0300d0011815141c00c440380f0000e003030045d0210345403a440760b00d1030400c0e4800140500c02c4600a20303002000401725100c005407030942c07030f040d00210b00311104646182125900040f40c00f800840075580c492541010 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 57431604 1250 57430354 57430357
    0x8010510150807110d0c02040b0108010b040902070f050106080c011e09060c0f200a0b09060403080903070e13140f06070509040605090117010c0503070c060902040b0d03030c110102 79
    0x180070030103010110961080d0700c5400265044040c41c141421000070540d0900d0800c0341005818000502e906412401d5180c41d00695001c1035003801c054805504025600001d44a1405046001600010344000b0085d03c281e1085803150050000c008440c0c88144007034132050441035060001e440c4070b100e411120341c0301946000c031007150744030003040c107240550985001c0480030055408000001c0c1d000d020070340390040301001100b6900ca8040c001c900074104036241e0f4003034000b0b96124106011080d01d5071aa80c00b01c07415aa002141191642c80c80800a4541042c2da00b000d807905120321700740502c0f10f44012a551195200ba00000902480c0f0984aa515089010140200d80c450400b00301d60900a00c02003512010203400421101d80701c070b000c02e0120340207900840c0140001080c00307405450a108808a88100d4600b861031400c00c5030300107184654a68020b003201e03a607802c0010442d59a0380c009011040050601c1000410a0170701900610380519a50041380a0030441880e5050610 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 57432854 1250 57431604 57431609
    0xa0e0f060915130803040311060109090b010302060708041203030e060f090a030e01020106080f07140105030403020a060209030309150307081605070f050f010e1e03041d0613021308010510 82
    0x608090041c1525a1241e80010305001d815400b018a0302000c1a21131000354807076406512031003442112408200e2420324140c1c0170240040c602961038001070703455150141101d07011a40c1a498140a04148045200381d0780444242804100300f8003c02d50540c01036400b40304e41078141c07040d90391401c041460b0f0210486065245402404080c03002a001d544800d00800701880006041510340345031615152860b00020116800710300b0804c500c10344400011403544003868101d04506085d540030b952486044801820f0070380201d1070410315102041944c00c11071004100d964024a9000c01030410382c42555075400041122001030030351507002003494111079003942c542d4a070030700c19290490b0003d918501194240141c2202e81c00c0314600b402250404441c0d1000f5000c640c1c0c3e200340c2c410180c548151075281c103800601040141ca01c200351142040320704242c3c00320075030362440000b41c16489d04124554100d440465000d0200780990b41040c2614a080c00800c01920b54003130200c9154090b1 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 57434104 1250 57432854 57432871
    0x90b0906070302010b030106080c19030c0e13050d0305041103010606020316020604031407061805010e150909010e0105040c0c0203190c030f150b0d020f0105090d02090a0e0f06 77
    0x400441849041400050004034042e200004680856500180c00d40340c090f40b090000b0350142986120030716003015481c070720000f9007409554192540d96100e6800301c15110b801603070040301e03000460128829000c40c50030355100090300e0580c000480003400605003950280c803085079600d152000e41c02d0500c50802aa4000e80095041c41000840d00c070b82280820300880e08060b06000c000000b0300f07940b0207a181000601c0240c000d440c10121300502c5000340180201d02113007840d604008690b0401042c01c10100107a0f0345802807031206216100c1441a07110382504041c0f15000010700d031115110060582d4400c4a007840711082d0791000b22000c1c7c4622101035450f41084011111150b031065400340c48900c6048001116680c0c0d44a04641e542102000da9500580c0ca9034518410800e12883c03500f04000c44855029000740d4010801c0004840703440d50600900164151151369103120a1400a0f40101102c51914007001080c018100f500103c025a10405081003801100410540c0c0f20361030301d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 57435354 1250 57434104 57434107
    0x5060102030a210908120702190b010b030c07050d0306050109080706080c031302090a050a0f09030503071215030c080106050609180c0d020f121006090b09030f070314060601090b 78
    0x8429481c0100801020f180740714559500100700025900405481d03602d80c0d131030724841945402c190190503c403440e6006400c2e803078075a0003080011021303003440f4191420740284d161265103007000300700a445992000f80140c824011000e40c2580e06402030380a41d0340030390f01c1119031651003410540e00c40b0a80140d03004110910001444004400b01565000303039420b036000c0c501e6155801007500a041911280102600c4604208503044c40340681030500601c400100104c01c501c0c0c90007002400050706d400104a4400c410420101349604603082404c00028400c1c0c0d41e80d502e10b07040c41c03402da091003a0050f550030708400045526105064402081002d0151405c030100c1d034881680400004215400341c8405110207020284941b010b0310540788400c10450303885a107001c0140494400403d02c007410485813400f0301c041a4040306c082e04840c1d060300d0241d02d41c004000061b062420301c45450360a03214040000007032020b5244240c05850002d4261030f0340d603c2d8800119101c144900510794003100 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 57436604 1250 57435354 57435377
    0x10020105010830132417090106080118060e03040803070f031103030106030e160501050d0b0a05060703030501061106060f060d091502090102010b04050402030a020d140a120305060102030a 82
    0x2c82c50340790500ea05980c040780d810b01920700078540f03d420400c0c2141000800c01c4050000d944000f007036542c13040070b0f8130402c003c0f0264054010802d0101c0e0030310b054144a110046801c11009400c004043e100340802070200c0401541e906816608808040e5000c500b40000d0320308002021023100c0507210a000a103207000b02d03d4555060110b80e4850032010040c580750080c001c180d0900145010380032650340414000074203941a89882100c1c004031911f5401c16800308510b0ba080303012103034105044640440e40f100c80c0d000142269005910003a001039002480e0020141d2503403005041e10400c3c0c66042140c280b801d480d40d510314048514582008031400100360524015000d80070704003405402054090b600d43e28070a440250f00c40e154202c40c0c0206940c1d4143da028002c1a40015080e1002c001c90f20b41500000d40e24480c00c0c40c040c2c0208000c0f01c048050041d0480c0d070701250307407041c0215442c00c80c0501c0c02022140c061016100024509004500300e50f1021045454400c2c259590342c00700d05 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 57437854 1250 57436604 57436633
    0x190e15011e020c030c19030b06150c0304030210112109030102030414060106090605040620010e0a0b010b12010e0a060506030405030a0905060c030a080a060815010e06090c070b0910050a050402100201050108 90
    0x4c3c001751000d4ac2c8052103001c0034816045080041542074201c2001c1d5442d0b92440c41403000000800f40c1600a208071000500041c00340015090000b8041003030b01500035034602070601c40c40c0300300d01d240794255000000f00001d202d03011100044201a06045130001e0f03a03509011940848c850107005d000a808000400075603200702c598200f41941f14407040c03906a003884485084442c9050009416080500c83d0801c1c062010101401011903080880c9040300e1282c80c055003d00501902c8041c41b82e440c040f41e00094150710600103048060041c0e0360300d0516050a680d83d40080c1a2030000941d0800b01103902d003040000d451000c90014011802e020319101d0903240300c88002c01103c100b55540e900081c05550400c100c50550300600e030300d50b0a07035040140501c41130000401c414000d10844050221081484044541e62a0070481800741c85c1c440030f05080c10700d285007800070b420302e00304010303c201f164550344500e0203140f0131151890f000c0c500c01c4060b4246c0e0000d00c02c5040c01c1d0050b44500e041039 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 57439104 1250 57437854 57437873
    0x90d0906050711040501030b0601090602210c0f01021209011b0f0e01020c1c0b01090e070b130e040c060f03090803060103181709190e15011e020c030c1903 68
    0xa44030b20042d100c0000780f0008202100c100741d109030313102c0c408030040c040903503004031351480a4070a51001d4540320030b00c1c5000c84080700006404501c05600014070071605030b070603c02401c01405140003556210703107080e806240e82005850b81321b6554685030030340c1102030102d416504804a01e841d81140c40c0d5150100313230746d003081c40c01999040d4040d172000c00c00d07070342c0e29110700c0400ad0b110032502244030700b081e06102028100503017122074051301c0c02e601035100010000c4d10104462910352010350341d50b24101d00801c0718080b039200381601c91405c030501080025518121068038001d5880d01c200901888048083d01c284003c0036001800030404108254442d80018003081030722402d082c2216003039542c0f245008090603481c03c04060101b075240d0140ba100c450074030204040080d000320141488181844400302501a81038000340c044c002045034084c1c2070041d01c100740c5801c41e4052400300000691a5038125070700718481d0180e052030a00c00d02e04140f02c0f20080302d15814420801d82941e0b1641c40f071 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 57440354 1250 57439104 57439117
    0x603100e010e0105010806070f0306080307060c1e1205070f1e0504030209040602030907080f0303010902030a06080a03020d0306060302040803070b0903070b01061701060807020c04050705090a031109090d090605 92
    0x2036548070060001d05407001d01034117000340048802801d40380342c520301c000c241c5580f002c2d03210105810103400300506000003040d2100c0703940086e1700181c045009407040e941c440c06c2c506492409145c1807003003501c40c1d40140340f106151600b40c030203112b1907841401c00c9a5a51110140c0c00104004485801f82c2408898190f200750310f1500704186400e4880e000514207a400700c0d022682960000208401c40a040c01901d000300480c4005120030360003910b44640307a00050003205900f540c0800000d01e00091038118000825003142036425070034241c00d0082d182c1554181e071001103402c3c501d000940f14464400c80b01140e104a004e50304041e16580c45880d0218086c04107501c5120038440c1502003024002c119000b016075171900d5105074980f85020052580580c00841840703a6501008143c45d0045020140702030304450000345551011805d41d001c1c05044000354004088071008010040030b0f51804072104c0d002c540a502d00d9039841203c82c2d407040d0302c0c50a440003940c540005c105090150010300070 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 57441604 1250 57440354 57440381
    0xd0b0907240c2a03060b030f0c1c030c080d02120606040503030a03090c03080f0307030e01020918060a03050303150406140f0613120c15020f060112080f030112020a06030203060310 79
    0x744610f08543c0201500b0a580065032042c1e55020b01d80c8080c40c04100320034141103240003820103c2e1500000840300d10000e506405c02d0b6503042c0034902094400c5d4030811040ba445200d06465198110345140250004ee450390300100500001c600f46142c0482074034111940240114038294038000203d0141c411020110756064103203c01100044602003e82808a0f11040041e180c5c90310210040a50309031420213080741c0d104002c2c01c4034a80300c00a405449040f0300400c48000d8a407500400c0c2a18055840a01640804414412816041a5245000e50080320f00b400708680740c03851a0414845940465409001e00120380403a05029015000032000c08040440c403560703440744850710004003603003100d0485580b18244955500303d0346000f00c100c4503100501c80b868071840c0c62540e480042c0580e142e141c074520200d108000000044031a01280500b0098507940d545c550036090b071800c03900491040000070070100c0c00c18864400c0ea032092500900400410744046c0702640100f0190b0901030 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 57442854 1250 57441604 57441653
    0x12060f0a150f09020a080f01180209061603120e06060901060f0c0c08060609150d030503150604030b01060e060f040b030c070203011a04110a0c0209060d0b0907240c 72
    0x70306900c40800c2d4100070b100008026031340b00d80100000b0a0140c009090134500f00c407500050142c6485240d03420741350710340d01c040141e96854400c0056254000d03140e01c94504101c004a07a0100350784140c00031051400070900340700d00190036801036140d21007102ca036a0030a0403803004000c1584140c0200080c070180341418145000c481d141c01c0f1a10030707650412151540030b04c0a003c100d0501c0c210780355010702850303489800c0300c040380001a0000c64115014040000c04000700300c21132403e41d4045152480208550790342c0c1c0e036a01d42861005801d00c507090124002a80f41c84441c10f0800448200c50801102c4610309820030030706801c1900042c0038100044418003074840140c40074860100002d0310f2034041d80d0032040180810099461000d41034031000d40038000b175000d503600012080300d40d036030480d400110340d601c1c4004680001e03241c00020b441d2801d4801409003420000c00c1510954070b43c94144100c1703d00c6181c03240401c01046140c3c2c8001600240c0b044041001c08a140c4500c1a406140340c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 57444104 1250 57442854 57442859
    0x2030a09141b10180605030708010b04051e01090f080705040c02010506010507060c140c100507030b0a033c0302060a05040c0e06011101020a12150602060f0a1401060e12060f0a15 78
    0x30320b00d50304c1d54005502142c800402e008101d41c200450f1801423007011f200518280c24172001c40d2030910704a040045001c1d090040d1107070f6a0040212101400f440b0980010702640c4018041d9240150301c82d00f030141d403400d91845442441809918414907068551034580400c035a200e000800d2440d0350706040115100c17004d5000800440100046040c41c00105800d05a08189030210760000c2d0a0005142c90301d04d880c0d16940320035480208030398000c0c204d2106604c00d1a1464019403400d46001c800809520b00710300e52401d4840c50010481c002d41c2162059540d00c0b00200846106503070252015510800c10480d94103000e49040d400301d0f061501440c041d00807009682a40c114868000100c1d11001044c40c060036280b080482c145800080400c916251140180d12400003414460080b02104001103841d802074104071865840141c00c0d504c0d540e581c84008082c034030003541480c402c10109501640344500000c42c0740c0070742c802c201158410b840d00e080f00710040011941e508500070562000 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 57445354 1250 57444104 57444137
    0x804111003090b061941121615110a05030406020d0e15030a020c0607020601081504080d02071a070206071202030f010509060f150909010614090f0604030602030a09141b10 75
    0x5002000c030300c0c1c9980c81e494004000400901f800803100d1101541e0041066684034911020407030115100400c4247d0070341c10055048071400e626101c9400c052054510080030407000100500461700300d0f40c00d403a8107000c80201160300c1c042d040912075224400c0b15245800f2500c94000b5500080b2901006140507050440c2e00e0800b90b0454220703001d41c2101c001007000403400d1110320a0210341c034100007640d1a05030380e8420316006a1f80f980b80d006038042902e2003007003904000c014005c1c111031811280c900d40484d00950310035040301c2c0c0f0070001c0da061380c40342400c0c1554000e0364010407100c0800c81407a8203040c14441c0100009098a80c00040d42030154040e807544030f4022110103175140e0590b501c00040080c00010001a8080e2003006809402d03000103078001020354035400c0c001c41c0c1c1c2040030340360880000c1003405250409017481d4800420310481c81c2c1168000250f00348150351044100010380da2a94650851200d950341070781085191a2032807400d00e1000c11380519504240140c0b4520400 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 57446604 1250 57445354 57445439
    0xf09050904150506060a08010e0c1c0b01120b060d0f060f0f03060e07030512030a022107030e1606030203040501110408061e0c04060804111003090b0619 67
    0xd00703441035002d5007102c11000d00180034a607803051054440e986003075101030000304a01d805124024017044c0440121741c2d0344aa160494009a92014200005010400068008100b000501804542d0340d1071500c06040f002d01400c851a280144194100140c040705040504244401066226901c96011859560051554014080d40c2d030b54282c0d0380e42140340110480b0804148651240c0c800b00080000800000d0310b046480c0702c4111150320394070742c240840b010307001740f12003a95010f182c24450140c040c42e0341c0107248118041d944c24030940c0070080c0b10984826080d18070358070401d000c402c00c1c400107000303400460b0494410800020610205800240c20303401c80d800045068014006110800305208500c50324207942c00d02d06111810b00541ea8042c03441507104a40074042113400250a0040e500313880424820080c0c0840a010a9000014014412404101c038035034131200216859081040a032640100ca02119942a50a007201450458480030081010f005132a0703502e40c00c0d0348081d0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 57447854 1250 57446604 57446611
    0xb191d0d03150b0406120b0409030c030e01110303220605040807030809060f010909030c02100206071106010f060e0604080d08041203020c122a0708070807060f0f090509 74
    0x8014180310392500e1801000c0c0c64020030b2034240c4240100081c0309400c8501c040303508441050a040d4503070550030072018080c0c0120207601d42d000d4500001d1034240350300021102110b6110f60748846040c68240010755900e03010050503500c5510500c0041c00254440b8004802040c14041202080d040e540e03030b100594038121001c075654070010442004050b082007044d0b4000e000c84010b4440c41c41c0503680b08401c03160520a1249203034517660604103050285c0c2d0701010340e81e00903200207084000c1000c081e659400036119a00000d007046a002000c200124880d41600d01103110801c955241840448103070180d1910554484d004210000751000d080001005a03d00c0c0d45540d280788ca480e0418450201c14807481d442818010044007031080c00210340828840f45000c0c02c59180d4001040810f5584600e01e0141c10050b6140d070740841c00c80000440d1001c440401e0100c4280c00e89540389030761912820b00c16800490500001800c1d0280a0201032020380039910340110440d41d01c0f0b002407400b80054 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 57449104 1250 57447854 57447911
    0x7030f031d0f0c040b15070201050d020f0a09180905211b0f0d140702150408010906050603250b0d020f0406031d0102210a0603060c050a020705030a0b19 67
    0x2010004242d013410b0040892401c0300f00c500c100c0844001c880e1805074498950002d041046c00034005152a41c95415507040407152896070b6140c000c010780c0608852040d02400169448100342c451040d00d10740207410140e548140913005050751321020f20b40070034170100c600300d81c1c0e10140002014103510700603212090050000912400c0303c800300b4207040030b07034044d114000c00c049802035120403039180e0219000c05a0656540c89000840c0640b04040e0040750005205942000d07a1072080c1301c02500003030f0186104a041d60340c20b01001070030719900028409000002c0c500b02c00304024440d0309401810214000401c050700c3d1101c0b11540604640c0303e508140c010030b558041140403020704200e84441d3b560990021403074511030000c105c100300c4044014103800300e60000012800c0da42c42d089100155449441440440800c83c0b010f841500100c0b8400e006104504001070a0f1800107020502d860300a5802d004e50b480d141070000030900c81c0039441d440252904054141e2000c403c80001d0a00301d02c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 57450354 1250 57449104 57449113
    0xf0d0509150109060e2202120c011b0c0509071701030803190506061801020102090301050a02040302090708040210030b120708010609060e391c0605010507030f031d0f 73
    0x307610751604188103800c120354a0b0b1070810140114060250516004070f842501d04105000643c0c42c0c042c1c0384228203000b50484240080310702e9107000081c00101150098a410354140400f10414990f036940b91000380a030610808100014102203814641040c644d250030301204003020301c0620750410a0f4000c4481d100e000003045010340220391000341b4883c0070032092110f404c5c07074400514103002d100340749250713080c0c44503455042ea8000d5040300c4a810000d0028031041c600040d06400079081444240ccc01940c0e84400601518860241a80300d503500410302d480710031400108400501e030b50160b641d00401d80a40d52103040004100d20b0b4005c181c0b02c0008a40d040c1024070300002c1c0c804a5020362481c035070140c01d01c80c00484030032030460246d40c40749201401d100711015440804450360583c0186020000701c51480b02c01a01c19102210450101070004955800045859114040018000800e0101001400b42c42038200b54403c9103040669441d050313051803c9418160310700c10112040c3d02 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 57451604 1250 57450354 57450373
    0x20303040201030507030b03070e0705120f01050a080d050322060e0609010b0d0b160504050a12030e01050a0c170903120c1903050d0e01230402090f0c07020103020f0d0509 75
    0xf80740c051039900c58002e150921040c0101404039607642014000c2c402107540160000d15024420304c242c60f80103030380300807881103401c2c24a803120240303000703014541c080c00403650003003800c80b000240c1c00060341460351401d141d60b403182d00e000d100900c00c9540c00000c03074000389500041940d500846200600f1140a80128289012240e0071100025011030041100c03111190210300c1c1c008440fa401043e1110b1031100282c103170412501d03072050350007255000340109000b03d8003c1e2100021141188a44c13124012180704000540f883e02448582c000094110b4071100c001908100d007191444107540403032411303c008080001e003400c0d4001c41c4072410f00d00104071014040300402c244007810303040f01c019600070b0038281c6000b40540f2885000210071600d840d4901d28101c2e09512a4400d001c0c1200d0103d201494400004044401981c00703910541140b00418400701c84815818051600740d24050b14002080e401540a500a4250400c01d000e06003d2804414418091144954469409002002c1 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 57452854 1250 57451604 57451607
    0xb0306011205090a03110a0204110a030c02030f07020d06060905151306050d080307020a1506030b06040507050904090201090f1d07080402090601270b0a031109150702180403020303040201 82
    0x5000140d0400007500b03220a00454000100e29100245e0701460200201001402c83e0380c42c0038003c07400290001c0c50315540842d9102000090601084169010b2004011844089035a401480d40389140c11604001c00030041c986100450099403042038042001641c502e080c1c41258001c5410708400f420468114110703160040700d0001c14041034070f08110403800c0c880400c2400e41d019000603e0480004086401e1b0b60003001180314069006115864038000441c0c05405460203100c21038150000b607001c41d2242c84e15000e11441000d155440724207083d21801040080c001540040e07042c0200d0010203c1c56041070b07230452010f0700501c2a40c20541c89020900e0300900401461502002000800d00006940c0e1240c403e0300140c0918101185005101d0354100c500c248652180a0140294002450060140c09400316107502c0c0c8003002401656144009103100c1c041e055540540d922080c20034404400c00940201c500182601d143ca11750360034220340d207400070340f0b0030b40169101200300000c56 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 57454104 1250 57452854 57452867
    0x110a09050103090803010b030405070312030209010e030607080a1a030f010c02120304030801031704050d030e03060106020c0a15050c1002030103060c09051c032a1106040e010909020105040902040b030601 89
    0x20325080c03070100301d90300305a15000c14602040c003c004000f44004040303810b1090070880310b00030f540c005240368240c01d190840074009501c00b44109020a000242e0104a4640442c840d846090319445910156948400740401081000c0b5500101e80c000290300313059403000c200c0315000240175000043c80b081e2100000c1d10f0896501c10040010404008010000782d100441070b0441e41d00c50a911021041c0c900502c075035004079001150882c1c9000442e2003815800342d002000114107400341c51150340c0b034100c120303100c000303880c40f01e5082040345034100b02d01000c0780d462a444502c9803400c0e90510314114465030515665010841d00990084018000d00030b1612802c00801c50600700300c2d6505140c54046050a056910107445015404901b0401c1c140105145981c090580e5060f481c88030707032070000508403601d225060310340780b40440c0564140d040407030894054601501d84540540c3c0303084603142c064882c03244201c0c100901400002034120799030000d03201411480884603140c1c0f03003410005008 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 57455354 1250 57454104 57454109
    0xf030c0e161407060f09060b0f010305280605032b0305010302010906050c0c06030903040303120b0108061509041407030c0f050a05070204020f0406050408100608060f1306110a09 78
    0x10391181501c0c0301146800c494040d00c00104110490344030086420648010820400b00705142428071209004004203a8420884001c04613184040461940011802c4420444441004035210f03040040464801e0340c42c01004021040042001511080401d0600c030b40d00c141c2c01c01003004d42003070090742c0000c000c204046e0300c0b851400300250362440c0c000a1a42c4043e20588080c4200080e4002c0c40040074000c0c41d9030b4241c003415481d80c1e42001300c1056500e900901c025800142000200b42c44001103026100b80201c05944829150b2104000c1107210303c101e04c04902c400e40108403212068031140a142400501c10300c00451914202c50b001d000e444100c0d40c841c0410950380300310507d0a80140036181036500c0ca1405584038465803001c98001d00c1080b0683c22485008600040c801d68484014415140b000083d20300300d840069061094405a003c0c4951941091000a14a604040030306074010655942c82c1240106500d45c84c080301c413103036040c4140c1040040c4c1606c200ea000000c1900 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 57456604 1250 57455354 57455371
    0x11070807110108010e130f110d11030111040b0909180604060b2704060f0f06030b040302010606050708030a0b060d09050606010e010f050d09170a02010603060501050f06070303090c0f030c0e 83
    0x2101d1900b260000280c05c01050014040151f0f12030000520010302c41e00c02e00800003820f08484c0c10140d00706215080810103515201c1c4d0b003048045842c068001060382c080b01d1203003422904110b6860200080f60034014000107242c406040030751010f0b40c0070440a805139001702800180400c940c0140141c00e02030211890247c554441103040c0b03085010490307540700780c000c3c000007400b010841d410005002e0f040301d084441c1d82040401f0080c440181c1585003e40d00ca41c00070040e0350740c1d4090917a01e9004e0303414054442502400041d01c1c54505030482c0d600a80020031030342c90031a15003001e0302110314030f203010b4030303268040e00801c0f030070f560801c0000384004001d0a080c81c0013503414500600310f00c206030140364481d494030000b404000598101403003820741055020388030101c03080002d0080c071032440151070450501000051605000104402001010b00a2483c00303089890a5001c0c0c5402a41100e41800c08040004c0c0100c4101207400514418011400c070b440c6404211a547e1380c1c0a0450f20 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 57457854 1250 57456604 57456629
    0x60a050f06090114011d031203010f090b06041205010914030d051807060e0607020a0617010504201806040b090f0901150804030201230103050d090305060a1107080711010801 76
    0x203022201c0c00100022813007443c1a841e00007002400c030450540000e28180c05110b0301100c0a19808100041c5060701c1ca107111084240e42d44000305010390314044900c0303801840801c07062181c1d038140c8000c044018000c03000410800080e9a800a80c0b40c4001000c017180e03040031500404e030441d035005040d006032001c01013003824010b400c0c06035100c0080f84035940070700c44010040c09090711410260789100390018a0352899a950f02405050200800510156081c800c0c00105161601d0b2044a12400c104034922540c0580040001c007141e2100301140d117141d1002140c440385560b01c3e0300070001f403c1c10040203500c8440c40c400307020240061028a42c400c0c0040001846480c96580784402101f00501e000055a112810281d004195106982040c4440300250701c0d05a440030586904880c46003040300d000b15117101d41100c548000340030091460b004240410513040060300611228901141d045107026050b03a500c40b03481d8400c580c2102d40941d401d0f0002000c1d82c020414a0041c0004680e09 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 57459104 1250 57457854 57457859
    0x1306030b0f04062411030a0302030603070609120b13050703030e0a0e0417071e030206010311030d080a020307030f021204061407020a0f150e151501020c0f010e03060a050f060901 78
    0x89030007943d002d003d05560101e59801140710348a8581461704034404020389658860581004020b0b40c03080b076405000b1700c9500c1d40000d20521a02619003140c180001c07100d4900c0543d03585012040f00a040802503a56058042e400703e00207207c070304011071103501e51690b1080160148a18041c0300c0e400745483e040c1040402c40840c01c0c030444070001504c1c8041e400d0f40d40e01980b030b0200018036002024407502c0300503000102095000512281a203000c0c1e030101d40c264144108160751080ca03418000001480d120100d0a0b07a440c68003d90b070444101d060104980c403daa401d07000b240c0000c1304141d802e002400510040c02028807920000c1d001d4220006182c0ca00440046d64070035400100401c04040c808220b0144452a081c20900455407503082c003054040c88665aaa8001a07032101d501e1004c42010410b08114901007101c0c1803010303000751842c1031064080003504040c1101d282d041c401c0407490007030643d0b4240087e0f84220b0b801040000c003410100d010400007840109124010304141005 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 57460354 1250 57459104 57459119
    0x307090e070c06182001210b0117130303050603120705010203100803070308070c0c090501061d060310030312060b0a0c1106090604170f0607050c061005090c0705031306030b0f0406 79
    0x17076a00c01c6a44c210340c001103240d20012107205105409100707618480d020a01001c050b5604541c48942c026030301da540c10989554041a014025182c41c09d4503e500c01c01c2c0000280203412207035020000038282c982d25a4148000c031a542d02010b07048030282d40c0001001b50880e1100c04140142421000a5080c03101c01d0f68040d2189034003a001e9801e21101d610351200300a42a4480c40103040701e50401c0c81196542c1a0142400106078081c100004101070b440220341044819a441000a844181c43c1c844c075540f41940c1074401101002d0a0a460b0300740403805034075a10050003001400c1d038400c0c900c0d004d5410075003015011442081d11402c420407124046548020642d0300340da0f40030a142031241580802d0a01c2d0101581c1d104055004130820040031030b0301b0074041c1154904d94002d861459481881402050302d950144590055520700840c4000b01e541c000b4005c00c912490803a07182c5200c20307003e905134405a901c0b5400094a400e14040c46e810907074a0140c4046099800380300d49420a0f11 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 57461604 1250 57460354 57460373
    0x110610061107031533060f1e0c0b0c1306080a090506090304061d0a031202030c2e050603100c0c020405010b1206090405030703050307090e070c0618 65
    0xa14030801140c1c0d0000c50040c04103120b441d00075584007006114000c0903040d5034005d012000d503282c0c00c840c070381d1150590055421842284103407400309903640d43d0303051500070785904e081d14541c1070070001040503010141e168000214200803a503190641c160740b4510340060401401050100c24000c248100d52449414a20322002e645003810401116a1600c9140d001040d4444000d03006118141c1071003815031020008000f941c0140c2c1e01e0003451a8407100e03510802c0881d0304402d4001501c103030300b04041400c08103d80707802101071054a2030300120a2940307141c41200c00154010f154800c0ca141100c144c1662203106016001505025914103080020b444080040c60701c0e400d6501c44004190051050303180c0580c566000703104200558540d00006115000b4001011446084101299092400c1450184a164480004c41c41c1c240190717811900d0341c0021f0980000c0c811052001f20780c1400e080f003014802e40903503a401c0407480c0f4a050510554400c90a412102c004090104020400411 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 57462854 1250 57461604 57461609
    0x60105030f0d03110d23010504020901020606040b0a050d03030606021504050606220e1c0e0901120204020d09050c04060603111e09120a060e0c0108150a0302040e0c01110610 76
    0x4001901c445a2446001e0a01c524000c0151003450141e034003000c201440da808071824603d204c3c00141f6a01d50f030a00080b48280740e00e150241c1c0c4500000341107454130390007035070704848083c0c252180d8550f510041040d0350204801180841d0f1995028040c03554100030342d03d040c44001c01030070342605103074650079154100907244070b0040d031034030200050030141d001a1990340281080e080144d9999048041d07101c045d0b2016910000075540d40003c0558490080100150401050076006034a46000c140d545140d010049030419020302401510300407912541050301c2c094000b8043e9144488100320403180181c0200e002d1514058446c0c0114440800b5562000240c1c41c103581005140da00d640098001c201d98a41e20050700c00c40000b107088017244e4411032620442c07050003014806040b9684480e02c02d8207860024000710009a1008520740700560175070340141880c6081d54070707a0003050a843d6400c5d54505282d00c429440c103819640142c000307440c440820081e0180782003680300d0302c08409180c03 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 57464104 1250 57462854 57462857
    0x1050f010f030b1003140105030a1101110f012c120301060e01020109050a0c030308160c060b061201170f03040305060406021e071b0915060809010f110705060105030f0d 74
    0x304503110006010f54401c80d21190300a00a21958031451401000b90a085100580c002d081c240002217508001580458103588410645041b140d440011aa0461010701140141c40303044001c0b404190207107e5180124400c0c0c01c4042036582200100c900d964240784610762590042d1a40c04840c00500b0649054130807500d00280c40140c1500102c1c09080c480310081e005000b4000c4183c02c200624000f9000c603840b0f900c86204550b074200c002178481640c801850007192912403003c0001b4450303800f80c0e8888000811040c203002d1115810017011800341c00c520324031001d416901429500030088403110702c403048000e51505007165500c0d6250036010b0b02c000c2c510707034000c00c030742010000c0c4809008601031880d4030140c607240c00d03003400d00c5444800c482101c0801e040f504c000c0303000075460054441d034030300112008001a00d4144104d8917460300a0800005540c0c1d070005c03d403800c0c11805062404860034080710744070b10860030404c6c01c1800c1a4013881c480c0e070142c0040c0d80c25400101e208284520f55 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 57465354 1250 57464104 57464117
    0x30d0804060507050f03090c01030b0a03050a020d0c03120f0216180902030f03030a020702040c0903020f0d08040b1c05222d0b0906160903060209040603020a06110c010801050f01 78
    0x30f4620075103ea00441c50f0559040e0004010420440b5002412070420202640c05121800000c4140f040410440c00054566040b240c000c1000d030410b10000c50b6034500c070b480f2401d400c954903207070440550392080254001503c407900d200300e0360360304204203941c60005421183c3d0300c1c0c1c600041d6196004102c0400e0300c0c0c3c11307181c8200700e095503000c0c00441800b810703400c1629664a4107040c0e00c0000c1d444010100e02c542e161449082c80107208a441005896016000d040300003038600401c2200040c0d080c04403004613041001080130413076240500710910950b000000801803501300d550503180b00a100c0d0008a030390080c0c0b002034a507960050207001c0c0d007103110103000501480c2d5001258502c00700002600ca4076524503800c01800d010b0701c0340326103c500c2c103a440b80d40b02c8180000a003d00a5402000620110000e101040c3c0d140d0050612900017840003c42d2580c0340d022602c0000c00e41d00c540b0103c0c40f40440162459014045c0c0c00c1a8603091800b44442d43c100320005020155840303c0a042020 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 57466604 1250 57465354 57465361
    0x20322080304060f1b02010804030e04090c08030405031005060a0312030b1509030f07030209060625031e020601050a18090c03060605010e030309060d18060c0f030b030d08040605 78
    0x402414001610400040d00e54a5031140c0001d800900b030200e118001440b04074000a00c0700102c42103000c400d40c16514000503840c1d603281218084032043d42c0c1a40666605541400100c030700358010000d00e594800b6589607071421042600704922074401c1c08000c1e040504120f0321343c3d98405030b8020740740c3c825040031003035a480070304074000c000d00412281c02102c508604145094600c0c044c000b040300c101c040301e0241000c0942141c071403001e880000d41102060780030a11526100015244200001d065040c0b0021319092170055500c0a4200340d020030016010340d18042d44018162034008080e0005051951601001c9100036185202d10310751810424500c0b00035207041d42103100d89030380002c60303403144a03128180003000301420721449010403076620700c110a609010090700e07074414004104c641000320300e2034114050710010305452041d41a030454440020030360310400071b06680f075a0750017404c5010302c4000b40c11903c10701d1415100750311001004000c21781c040007081d0b002c0e6120f4000304040d01d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 57467854 1250 57466604 57466657
    0x606021b09062e0503040c170a0206030912030c03060301150806010b0f0d020c07090612030509060a02010902060d05090106170607031d100b03010c110706050309030d060602010506010905100203 85
    0x80c0f0300080404800c92901c1000341007944180954050780c003810510b0798440d981c0d00d0760b440b1011550f18500070381d0081d2000901503d08100a946e21002000c1612031498502e0091001540111040a446c40002c4180805818248605106005412a245e04050800365040d90700c00c41441020554080040c01c8906100340c1c8040d1010000700181c00e540751750803c41c01c103072140d600d40100d54501d403174a1400030314529907a4008403055010f0b241e02d49040d803d1070900010303902c1000c0c40400d5648408064006840e04070040583c0305042c0b4000645040c070004460035200340c2e074000402c0a000701e0320903075160404961503400030000c0c10001035106121380144030b80e103000c580d02d00d454040c14094413019101900b00805520044000f00107440c9800001d90f9200c0c18141da020043d840034034103000c2140108010341d00500c5c01c404a03400c0c515000c00010035106241c001c1d00c0184d4440d0244101540c104200b00c02912040701c0c0b04c0300350f54129000a60364054201002e07415040b090100b04001c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 57469104 1250 57467854 57467899
    0xa110607020117091c021c0302041a210f0f070306180903020705061908090703031e020705041a03060912090114040e01030c1a1312110901090606021b0906 68
    0xc15004056940c202080b41011f03480d80780303034220000000f0f5600c8100744154031078400c83e01501c044c000f440f0301240b4031800b07290440e0803080c581868500041845002c00d903542442c14407440400ba901c40c03042ca800b8103e42800c1d00064414000e041c01e1400c00c0c0450220204025010160b000c40001c018086040803450009540d100350380111001075103e8034122004941d685188942e1982e0319240c441070318250765104a40b00240c00126410408031014580c88601084619a407048846554640d03000030200c40503ca041000c0b8101042c030f440c0c0c075050078080e103548004001c001e4581d000003181d5402c180d10030402100d0410080b0b001400300c800d120819180503044040a410441da100c2c030705201c1d106d2a43c00762050301d0400c01031403400320080c5801c5550011111445104261038070b10350103686c14220310100c40c00310f00e01c0040e0542d51210b80c445802081c0c00400404e0711450140041d0801c9225043c0130310941d0b9040201c4000c0d10341a18240d00b1500580d07040d1a020005912a44174 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 57470354 1250 57469104 57469123
    0x302070f060606020d02010e0c06030f07170c0405010f0c0c140a03050105090102030405010b0a15080a090203010c0801060807050c062a030117070909050c040b010509040e0a11060702011709 83
    0x81c00d2070000007140890b40098601c0702d031102c54000708035a82106048664518520707c02c60b0b80300340f0400000740380c003040840b155001601420456a0b18200c084400c1d181401210545d80b0240045401c200569001d5512080244582428007004005031254180c0701001e010300d01f0a49011600002d9940300e40490000950708040200080e081143d08503010750300030340d0182c60079030903c00089100d240418404088420403c00c400b59003407985000e81d8280802490801000e1b41c030f0440c0740150301e0a0050001409a44c1c0c0c0314101581018409040c0c000c028080c2d0301000130a1203a03c005c910005010f07038010101c0c1a000007243ca07034102d40c41002c110540700c50503c0c8404000000c080352650480e5001c0c02010050751070703003602c0321205d0044074071104000e0300e59444000b02d4009414a540000031042d4103241c614074200400c8003007001d5600e00d003801101380e4464a40d002c1405a0b40041400000b82290303128540703005a000244964401c5d005403610022113000700b020703904100408640f = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 57471604 1250 57470354 57470363
    0x2403090c1203080f0105010e03280c0e0a05010605090102070b0903190b160215060103050601111c0908030a0507080f1303060605030c0910060e061308010e0f03030702030405010302070f 81
    0x100841280b900800c4020155520301200c400c20002281940c021440050440340180080c4244000c200900b0100d241c0c0c040031100c1da0600d52088030200b25150b0b20003020788062000c00f0228182049540200c0348141c0c00402000700c20300080c2410b0ba800324801040b20b0000403400c3c0c88050080010b4100081c020b03400740d03402184800e401c20080448192446040000404201c203000e0400690300c40b0f1800d03c0f40011046401c0010704150b0013644066000281031500c03058103490014142c2c41c10070315007085c03007500300da040a80301c2039580851403001134510b1300051410f100c4c0041000d0441d00035020001d240d0200410692810150801650344081c0c1c544103006615a89003001b030010881d41c01040c0c0039008011403c0302a041c01c0c085c55010f40510b101c00c003107480c17030440c0c211241060b24181d641d0040e010040248026600300704140030b03003c002e00005d1001100c0116a01d0102084112a859001882044059030b0044151011510282005071741c0d03082a141408501042010003003 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 57472854 1250 57471604 57471629
    0x6050301050a090c1202090a11070b09030912120a080c2110060305160302091305180c0d030e09060402090909010c0e0f0a05060d02090a03080c01062403090c 69
    0x20460a02d4120340601e50203044d080b0902912030080313074045104218040c0d0800b0641d00890f403100400c4d07100700c01c207241001b885030400d002581d401a00ae038086e22203405550011420b11924079103030100e9540c440881004010b1071101012941d0140524084002484294800201c0c2040304404840c040c0c04900300c4c0380d41c2c1407450100e4078441c000540d01305840070150705c00868664080e01c1014043e00800f1101c206143c6a0801240a580b061303000c40d40090f5805080b400d10030076801854080c20440c40c07070501d440c0002800328070b000f00b884142071003004650b00e55400310303402c681100d41c0031074142d0712510070743e8900e00454080e00c031780c840c0340e50404e41c518100084040c06510401da105070070760720540c0382050b507000c2000741e141c1121020b40c408000c0c81d0402551a0880042a200e5006240541403803e46400640c0c50b4100764001d8845a8000500e00358100b02849424003802075021140401540b00b45d0345181000884804010f241e1360341420400d2000d22080c40000307106448a42 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 57474104 1250 57472854 57472861
    0x210f0206040209090f0a120f031a0f031617120a08011403120304030215010609080c040b0a050402040b0403050d08012102130f20030103030e1c050a0f030e0901050a12060605030105 79
    0xc0381c03140c00c1542c05000072300c040c1d00000315030f1190094080c0c104001e0341c01010807490108100030455510946549072241444019800d8075941001c03000f0208120700400c0c40c41528002401c2141d41185a5a22a01044848100303500441418151500c105d14a0480c01108001c48c3c9090640c254070070f907040c1d010007000101980003072400d50b0003030040800601e9990701c2d00c0641c0c04044500030362005410021041d0841d04141d48a8031851000070081402c1655400c00314040b81d0040d01b0206004000040602c03c0c802c04000c0c10071104030f689407048107507150111515040c030206c1c12041613080c0340c806120544d60313802507551111802040c100050145c024044004002c800881e00d00c801c0c00d0300441c007488442c00c054a04070b9800d0b0300c4074441e26440008000d81c0c034480000e1808180740f0031058001055040245203d000d22400e6241e000303107003a09016044e00a0391000a1084000a0040c05141c4817607010004955070b221002e46410411f01e00700300a0502c0e5082141c06600c1c10301007 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 57475354 1250 57474104 57474113
    0x3021e04060314071e030908040e07090e06090105010809012901020c030307050d050702010207081c03050105060a0c02151204050303040c0812030408091507210f0206040209090f0a 79
    0x40c0226000703070702c0403c031070b00c10b4500c0003d1140044412901140d0041c03a14041d201410300880e4240045203000910f440d0580d803000c406400c542c000c0d8411004038020015100e4000c65902c02500591031900d0203890300c0390015071030240500807a410046440082506440250450240049086071454146c0c1180800d18111415130603140d0051040700c80c00382c01424048100c0f030b05c060304600900b050010030b4100342d9982d840700808038110720403c040044d580c003061250304503a248800807400c1c0401921801400d403401a000103110360380801409150759000821404400d60603550080c1d54034a130800c255a5002e0080101080d4036040e040004000004c001175202e01c0c0306943c0744d03000d6030b103551800d90f8508800700d441015080c10804940840c00403400b400803d81c00030310b0300c0c0340c21341c142000380402d0f00708000881e0031005646081003144c06c031040d6801c80c50400d1400340030020400000079901d140180019018164000206600c40801c0c01100051404901100c920f071106250 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 57476604 1250 57475354 57475357
    0x60903161a1501020d1412040c03080309010524030d0f09170606090717040308040f240c05031504020c0a06020307110f01050f010510030b1302091e15030703021e 71
    0x40c0c40d0041c01007415600c111402116501c000f11006d030381603410440d05401603407408102800a4508a102213000400100648005c40c4150740c03090004c285414a43e06c5c5610180800b410807001c90000310702000d154170006200c00b03100159207000ca85400321101d06035642d80c0036800c040d0000ca070710446911041000034500e80106410754800b070403a50350a200f00e6000360005c0c000083d4204000c0403c011030301c1103040c00c0d0802e00a070100090340d1150390b0303091405442c3d00a0400d210102100d031000c8899144192045d07800710342052482c515010414042000d5002441c61041c2e07070204180c6013011080040d40005a031020701150b4905020101400700201e080354203000740305009000d1401d10040c000c40f40107440d0b8400c141203507402c11080110304001001c2031000c165407114922403645e581c0040019100881d02c00507940c80031181400702e81d017400c0c1425440b940203d0380c10400e1303444034402914038103241000c0a880c1c1d1113040b0200d01912484040c81c51100020101e1030302000d1480 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 57477854 1250 57476604 57476641
    0x40f0e070f030b040f05030d0906060303020c04050403080a23010b070c150801170a0b1006090915030f030203160303020310051c140f060108010606030e060903161a 72
    0x24112030400750745640e030301140420303400020710320106000400c00180258242d000c0051080307040c1d81c1814902d039001c800300c1d203808905640c01507d0b80810014190144040d01413440180c0741030140789060380b000b0b44440c0029001c80000790b0380d4041012034410025a54246481c201500f00140d42d55202801187e00f00040564100c0c1d00f003440041d000b0030340c1429030710340348850b11140040d03803801c800307440c92844e01080d8240302d004110f0910001401d003070701940b0034850600148ae4840c101000148058516001411010300d01803501d40c50070070200452080741e61144100d90090814034040b4154040e14215869042d1075110b210105900342c0c014511a010340e10008180b103a5410800911035815400d4104042241001c2004900764241c5981041c4a00781280d26441c00c5d100b400d458124240c1c0300351080e0f517548805010f19989401901c0e0700c81200401401d01e804c1c0024402c1d22441844480c0003601d28101d400300800c1400710b10580f403003012003050b00861a01c1c3d19045041203080 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 57479104 1250 57477854 57477881
    0x3070f0c05190e0403030c0509030604030f030c020705011b020a0305030a0804020f04021204031808070303051206010305090d180512030d14070c0f06020f0309070e0108070501140a0905040f 83
    0x240b040010040140c0c0d0004590b089a8000999140c60b1001d50090000310103c50402c070080010200c2503c0401000d4002e83c03080e9940399020041c640018200c5032070006150440d00720881c1000030782c1c3d102c0c3c04c1014204105011043c1001c6a1001882180c0c00c0d500017810b50001003055202190090000c901c194001e0720400980c100807003c00042b88550b078892104d00380d0380e1000c42c01080c031421040c0e800c03c1e81d05c04196001c64441e00814580242640200d002900001c0c14003c80e241d10320307415810170320a0a0521113130800ca1811034030380401c040084100303c040210760f0b0b400142c00d06100b000302405420000e600d402c2038540c0b501c0e54840003401c074503030307091046807140044040b02042c822241940e8550f601d81169590107007c1003000415241d65409021244180c040000207502621300c1c880104400f0b86001c09112014005900221154008000401c426604601c0000c1040341000300c1c1903859a4011058540c03604642050b0303081440c110340700381d610120340e100d000d050500 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 57480354 1250 57479104 57479119
    0x1b0b06120f06100603060308040e1906080109030e12030f070309030204060b030412020f0606100c05010515030706020303150108090f0a06022226030d0e06070e040903090e060303070f0c05 82
    0x213030741007501581c840b440000e05415040004100040843c400c590300081040d04420b00c14203c0000c4005454440c0c100ba07550380d540f42c0d40001016000001040603070f0042d107030703003420307000c00416281c80e80180f42d09915004030002c0d19208044c0320781020b40144d03500030000c01c8a04d4031052061500d400880d0215104189404441c001d140005410014000d48900500031950f41d08140040d520040e0400804d00c000b5103480c030300151082c05900d100e1340c45145088650944d040400d454102907501034000c0d5001001401000d00e603030070039080000c00a0030a03617065141e150f003c900d00070780b00d141d03c4000d0060b0350300310f0100f00103900200a2291a00140c48042c0d0300800500e550b0140c0e803283c24850030702060002d100d48400103030f08400085420aa9052443c1c071002d9006503180e14004050715000001040150350304071031141400082a6000c0107a00c144d6500642034074180d001d0b824821100800059903540c1c01c10846170082d031b20000802c0000c2640c40d1808203090180030785440b4104 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 57481604 1250 57480354 57480359
    0x80106051e0d03050c0307050106080307120c0809150d0f0507081501350103060b01030606050f0702040b03010e030a0c020306060306043903030503060a05011b0b06120f0610 76
    0x101d01a20681881d00406041080348556016a00f560150004107000c0c0000d1000c8000f1400030b20a41d00180400b60103140e9413452460814890a0880302110038030031b02c1030b694000302c1c1000b01515001c800544c0c421002600e07880441103240580344a00231030905260200c80328501680196019100a4542040075155084c00321502d219204d50140000c0b80502c254144004000d00c0701e0542000001051740f6141c0713161070000482d803d0b0020b07603540d511050300b8082941e051156800030941071804d281071911118101c9814811030b040a0710898941205840c035907420f6001c005882030f120104d90b640d400c8501c000d1b11102246500341e110b401650000340d040d0401003043ca00c10342e880f0f0f100511f20f9030038030681615507071810580c0b442120042001542000081440d0021354041c2d100c1588034030b0442d0030000505a03d800a90411010b64238803100d020346c100c2042ca04561100380302d219641e802c00894090070a180e1200214420000f131400c1003500800c00c2c0380620140d20b1040000394 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 57482854 1250 57481604 57481639
    0x20402040315024b0405040905030403050f0106050d20060307030608070e0912160219030b07020a0c05010e0f0d0f0312020a0e040504050f060903131d04060c050d050108010605 77
    0xd82010180d003081071101501c1c0c8200025101c0940f08480302c4ea00c4c1d038142a105c00228007100c0750044100e40b46d510004050041c05010042c5441040c1c00c14004c0c08000c1c10035000c10b0758803810700c0c0000c094101d030790f5442442003820140503115800140900303440c0e00d0107900c01005042c02c1e2240c0307030b02c0d07008134000800c0d0b6503120a00144602d00c0c07400205407170003a410710a40d043e401500071032450080240e44d100180d894811b07030020411340040d002407003400c1d400d10b1503000b90081d0078a000d40d0320840b4030310b0004180d0101d0404507902401d107520505004000700c0c149607007124205500140704c100b4a1304020000b0f507143c0c807a034000d43d9400584605540340f20220300c28504890301050141c6694420303442c064000da90700a01c9001500da9451168040919008059494030460742000c1070b185520046091038900801d04982103802c403013070b00101c02030180800b80c4003030026900c803054030b0748460043d000c441d04503e449104008542c0c0d074480f01703802002070b802030910403646070301c281e00300d034 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 57484104 1250 57482854 57482917
    0x5071e08011214030d09050d030e0a0c05011d0406181b05030606070201030e0f0606010e060a05030109020a03090804060e0901090207021804021c240e100902040204031502 75
    0xa41c0c08216440c0021199103544103040901101c40d083d6100401c89603403010400d00469041c140303d00c00030410829020800b0301a0342d903011031001d80b43d04c201c8554001c102c1c904110801c455080c202000c5a00310500038035113161034030413002d030020709110700010403010300c2c00504001050f42d4020007250760b106c41b0208151120801d1070001490600c00700f4180d2030240c0091420358414140000d00701c682011342814814403c542c2d9485130052020071941d0350304013212135242c1804450651907c40c034680c002e0003500040c050f60040d60317400b01d90351203014000d501c000d15064201176580e131920340d1107400504040642d5500da0141c00441d00014107007401b80241e40c0c02c998011b000c203040c1c80c4216022003110b00001c2c0180d9000c1c1060411801d80701110111142c007a01800884440445000c0030b503884040690284100074035245101c5220b45000c01c46140c00701c0c0c0500080b46403034443c00060040d0250fa0000b6142c01c14280d200c41140849500801d010440b0644441c5465190281c9242c01c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 57485354 1250 57484104 57484109
    0x6090807060f03021213060e0d050a0302070501061208071202010203010b04050904020109050909010905060f0402031e03040509070305010e07020d020d1b08030708010315050907260105071e0801 85
    0x15a00c5040d081c03004601400340300310600124030780141032000c50342c1002c0c2440e400341c0710b001c44c4c80050404101030080c240039004c02e4124207130091902d43c5035030900514a2240f01081d004065011a03003404000013074114400518901300120410b214a05094015501000c803c41e0000300d0140301507100b03801070081c1d074100e0342042012401c0501d04001e100d85030780000c1049040100d43c22020a10390750714a0064001ca686c1d1b40002426600c030718045243c00c002422007000c01980380b0400006036000503c0300124400b4408111003034062041c203901c0d501594001503481140102002800350381075003c0e0381200c0c1055a404041c1c3c4403c80b060361101006040c0c2c0300180c1180007803080c03903400341c140240401240701c1040b02d00041d031786030b003d5150016108000080c444400401c03d001c0e2078031140ca89008414400c000600302650380690340c00580c400c00c1c0c1c00c010320210b11410502e80c00d075811003184214009100e18580700c100242845110903c070b1040030310b90700100d00320620904500e0305 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 57486604 1250 57485354 57485369
    0x10e10120b0601030e100510060f050304020901030f031b0623040507140303090303040312020c0a1d0604090212011506020a08040b090f03030406230f0a210c050705070609 75
    0x752038403414011005403c3c0411040903c1c4961514070700540300910440c0e01ca00000381001002c075060040c004e1099090403021000c02c4014000e200159441e00700b014110307a03019862084800c070758075042d0742c045032550b0305c4010041d41c80380751014890941c106001c4107882c41d400f92000320110034120400c09041d20050610ba1010400307208400c101c820424840c0c1c1c0003000c0341d040410f00400285154003c0d001101e0400f4920741c44289c40b40c0401c0302914052084865401c410b0501c084410501107225200d0802d0b6418004940103441d2a4401d00c02d1f150050501030b00b14201c03081c900c0c00382c014040320000c03550022400040132031000c0f900c0c4550692000695150615049001d06240c01009585510910451403484681c2d010401000141015100c00d0b8140301c403c03a4441030500e203600100c600c1d40c001c028400d000f611715000c80c1c4e1400007e0814060010341c0c607441840500286044001140c6084281549e00380c200024002c9035104104075103103d6101da1080350340c656948540e80 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 57487854 1250 57486604 57486623
    0xf1303020a02042403030915050418050a0f0203040b100605090616020a0f03050609060a020909041e15020c10060e060105070302010e07060809010b030105010e13020315010e1012 78
    0x801403800790401004900f107a144c2c0381c0c007070a41c02d8855a00d901a5072049000c140490743c00c202314840c0710300b8802405c0709410210309041c45c0c40305540c44401314980c009040c1340c0c2d40000818400c0264800364000311018800c640f00e240030724020000b03c4040d20b07030401c03014078608001400351140e0106d604980c0017900d59424920f81c9060b100c150200d9140c1240e02002490380424440807012205004600400051500d8105500c507182800301c09810340050301c0c01004070b0089510f03054a035907002a408628400340c00b4035900c040005101c05940108a116400440c3c22b81035200d030088c22603d00b00800b0b0b100002e50f03030000b40049032944e00c10203072244a001c000a101c1d602407030190603010300a0002041300c0c1d211039801800c1648075041280468100b0f018009858001d00c01c2403107801040c1c00811155050462009d031451008140000541e04500d00d10115182806444040c3c10015040b100c2940c4804501203d5003040b100c42d01c41080420b0001981400c03000000007181e0811001c1 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 57489104 1250 57487854 57487873
    0x50405090c010e19080f0303010302010801080723010c0218070219020f010e03030d020706060e1602120307020a0b090601050f190b03060409020d050703031103040608011403010e070605030f130302 86
    0x2180f02c0f500c0344402035403200d501e40c0018117464240285896691800003540d0b0769815840090042c00d410f03003141c412680b1a02c3c041c0f09241c440c0c2c50825808400240000c900740782640101c400180781e01009406c002c0303c0b216080d14844860b0190b000b50403c0e000d540c8014134582421465102866002e54400166045003085501030b0040f0421b068018003620319020321006120180c1c0d0100400301c50140e6103810400c554125041410b80100110400c114003400b2541c00941c0c40c03100441d0070002c80000401706010314000c0040c1910103600c00c058088600e0300742201600c400e024440c450240d81036001d41460340c600808044d11070304064020549142c01c0041085442d0801821143c1103070303031104a84d0241c0c0d241034401e05054410380050400500b1840c0c0201907648020130403410f54001e0106004650300000300a040d00c015001b4001080310070310001c1d000d011750345183e075407500501c040030480c207074040021885a4142c40503040390b40c89210300b4600c4a5079403040900141c00c84e0070603 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 57490354 1250 57489104 57489109
    0x30f0a080904020f0304050a0b0c09062b0e01050a050105010908060a050a091502071104020910050c03040e071107050f060403080c010615170f0603030313031404030c050405090c010e 80
    0x1d01491400580700500f030180f95800c0b4443e6030710984096606610642e5650200051170f4000d0b40d101c0c1a03402114144541100814083d0090381ca4000c01ca003100103090041b880d11060350071040880b200203001220440240500038041624291071550910b000414954014216001140c120b11700600c1203903201d0050400805019054411441d190302040020605406091b1540109c3d514016540c183c90f14182c40070705c0c00628014041c2c0d00501a0300501d654222500783c0c1c01d101818203954910300000718a05522440d0001c460540c40c6c401844401c41d400004580104c0420381290145510782082020444100305074540c41380041000b48001820380e070181500840601c0003152681e01c0c0c3c0750014686200f0322112000035500d00c48002c021f4080a01c940e0030211a00d0403a40d1410032001003500ea12004001d1034800c4454441d000805205403403210100041856280d00c441e12490009082e440a1203218812804c0401145020001168202d8200016125a210411054103 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 57491604 1250 57490354 57490357
    0x6080f030a080c1b0321060a05210f0a05070f09020c120a031b2f0a02010f0c0b041101080f060306010306150803070602030901110f162a03030905030f0a08 68
    0x1068000840240094604658208042c06104103082d014401e080c5610111504100300142514448c12040b1410841c0307480d24040b48481da159000c00841103c40e0380305440c070300031000c44030400c1c2d841031100a10a0010100c1c0507810385080020040120781c0e05e46140c1c00341e015403084003286070403421011400326030500041540550605000c03d45260034919042c0c125101464440802e5030f800040318894045000d0b00d4617100c6040c461740c0c40100d0315013910340e2030f103104600030b06100f011001088000e00982100c880c4551000e00782c0d9941c94113181403824044410211408580c010010480740541ca0360b800b4401c40c400b030018220f50f032a60300c6e0340c005450341d91200031102860ba10003280901d07050004189290251742c0160b07507802d000c0300c210b0840d8195620000342c04070034020032000d005032400b15041c070404030b12414040c00311030070210311242003400c49000d1031141c0d4000c40d65003002921802c084074000e450b4409440d584409144d00c403103544510f842d140d04020003480020782c2c80e40 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 57492854 1250 57491604 57491617
    0xa080f0304140a03050114060901050102010903050d020304020411040305010c0201180308070c060f14010305120702010f030b030102090d05060405160612051009110c0606010f141e030a06080f030a080c 88
    0x1000340792040d90342d841700ea08446500e551162180d425030104003080c240010350500404007071000308100c80654800a2803800350540520b01c2d1178002000c0340540da16500030541165081c400103a80c0d607524900300d030081c21030100c00005035003040c01c800c018132590b44c3d80350725040e01178950807004d0741d0f008002c8620451a8404035925071380c4000e070a0300d906c041d02c209010000343c10300c05122541141403852900800400c100d5029900300702c0d010050742d02844512900c1c880d41000310f0341040390000071340640030364014079401070381b0840d140050101c00224140110b0041050300c2003440a0b840d030b903001c04031034045ca4001c140d1084403184591a1540465170280c03041c3c03a584c1c80e0741d840340b11100c10b86a41ca100405820740c04104020402020700040da04a03009007403030541503207a45d4000d07113000307204403810580c800c011400c403000d901d5000d503c12142c2e1404110b50781e00c0c43c2c10342d410002071115014602d5035100303e45400d9200e845c0081101c01c61081520f4814595a03119010183e03039000d0b0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 57494104 1250 57492854 57492859
    0xa03090602030112050708010218150408060a021209070321030608010e0601152a0602090306040804090b030a0503030609130b01030305180619120b0a0906050a080f030414 75
    0x9614010106440d032000d58083e00c0342d24114008030043d801e00d10f14240013500042031a03441007011140078083c1c003400c2110303540241d0390300400c84085401d100103401558040562400740340c003003000340103240c0e00a281d50700c1d81c15003000958454660240d80c0300b46c01d0100a0241000e4150b0b1010310400014040c0d594a007460041401629a2529400d4481074151500141d00020042c000b40c40130070400b00651042e07103060440d00d164045045034004291058443c058100d440c5202400b19540445a405170042c04491560404d0b01d0501c8456003e0f11917107080603c0c0c651003000340d1401141e54421141c02400940c210349540041040c0c1001c05040d0301d41d00841502c2c00030014130185036590085000361903107903c0c0c5d00c02e03100c1880c6034542c0c200c850303104010070000c100007250454681c99481c03000e8546013024540d85a43e04004105500d4551307400740e400000050040841d800c058269001541c03128072165803031000355610130134030040c540243c100b80020b10608070b5103800c0c1040751000 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 57495354 1250 57494104 57494111
    0x3070302040b19120201140c0703020603060a080f061807060e040216050a03030b040b010e01021c0207090e0c0406140109030f021f0201020306010e03060606071106070203071509090b090a020a03 85
    0x14500140c607810f450303004081c48104440704e4801c3d0360304001c200201505c1d060082d8541080c050480c0c0d2205007501000348245404004205952909110a4040c0807007004807140601001241a5101803c07101280e80001144d103010300448040389280440305c1c1034442c82003040000c420000650403010740c080b40038241e1340c186004140308001201015000361000215203084805000958003e00151814046c0e01da10000e442c0e64001802294540306001c0103030411b0140b0b204070700b4403906510400005003803040081890a0100d006c4400c04800c40302006034590740c0980703109001d620022640811009401040400c00c090720a11180b4401032188189524800003010400002d0302101d00503903001c4100002540c200c8600c01c0501402c500034811890004005409882075200040881c00c00e40c00c240c035a0348444055900ca02d5004054030788280d200d0001106814445404500041c81c044000486801d1441130072103802010709030340010b0341e8212100d0040c0d4000b03040003007015903 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 57496604 1250 57495354 57495379
    0x31c1104091431021f08012103080f07020c030d0e121c0f03060b03040606030506101a0a031401060305040b130c06081911090a050402131202030f0105100501030f0b03070302040b 78
    0xc40f030082c8100c54006d813551520f07035052001c00101d174400b0251244483d80b000c00c411012130b420462950b440f10781300c00e00131040d80e54200201d0a24081c0c3d1601c40d018801c00c010117961a8000d1100441c80c001a65100491500440c038036960b88003038045078110003801d507610340850b842a02c240c450558079040c0440e44a41e9040151400c0e031003100c051768060742d500d030180100b04003070020a41140b60803017082c44e03142c2080c10a01452100d4103030711000c15000170380c401c400d40c06a00b0023201d04c2c015100c8501c0e00e6035101405005002c2c02c0b00d0840f41482c80c040011940c040d40c411042650303421003058400710f401e2030300558402801030851002100481400403d0581d00d005040c105000103c00030784521041040c405110000e422080c42240180709440490b03c41d244454120f442040b1519050462030000c41e051400d9000b40d01440d50a00d02000741d035a01c0318048104840342a6002c118461700c0c1c080500407105201d070001d5050704850801c10251410f9042180c0900c8000e003058041c04 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 57497854 1250 57496604 57496639
    0x3060105040e090105060a0909030905060d0902090c0a080601080708040b04140303040c050f010203040b0913090210020105041e0305030f28050103050105100305031c110409143102 79
    0x28030449203000e0a85d11681000b0050500003183c50040c49008001d0141d007002d80d8015003400034902607580104008140c0000450341ca8000b00b40d41c503005403c0c840d4604003200c0040c0d06500034a80380001c100008041851940709080540c0715402d0f80d5034003141501d80c1c0e0380340700d1032001c00b820640e4110850805418000c82c244000d60203603200300400b80c011841c1c08240b00d80070030f039181e01da030541d002400204441c203050021100292000c03a00940310180440c1e04000800d503091020b50449182d0400d040540d80561140d4050b0740682c0d904441c40380381d4011100350710030403030300100000c00c1030001c00c01800d840c2220541050309141c0c007100914100285040140780a0a402522519440100300b8004203105141c1c0021010181035080c03070868031010327503901c21559045900380c0801c0d00c000200c0c0007503005007a40b2024044959456030b403800603a001d0041451801c0340b10b0048408588580b5038001c1201d001515401d0b481a0011309068084204a1203a42680c00010b400040c40118 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 57499104 1250 57497854 57497879
    0x10e04060203130c08060a050a0b0d020d0203071d1902190302210a0204060810050607030507031407060f050a0902030c010f0507050f0105010602070f0e06090a0b12011a0303041a0306010504 83
    0x405c0750000078000fa1907d041c0348010758002500e603440d03191901000180c5911072101000c0d0094040c0c4044980c03d40750b1020030314011884d44440071501c100405241704d40358030140c8074000c40070665100351140c40d500303100c03040303114500300010300c41d8450500318903d034001c0e0058944810b00180340e0f0100c896030080b80c0c4403001c0484100d011a640020284010707a0414032180d04404240c40c101d940604110104110b44202e18024051040c04134210040602c10040580203840b01c081d030030b8031440240391440161480c001c620503024101400182d0390340311442000c0b0805e400400800c00c5540c03510054540d44001c080c84802c10070104403101c02324804011444082444000004166150140090034031000360406c809403401190300f0001d900c02141c5581e080081100c1c4c14169486042c45034009001c4c1505236074102181e02645507103008198007010040e40c0c00f00c03500d5148400401019201d100d940154502c1d6519440c0f100020110000074507030010303048c1000740c07402c1e4880c1241101c1 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 57500354 1250 57499104 57499109
    0xf0a0302010e011d300a0c0b060d0308010306020a0e06070803070801080f0709050c160c0303020c0a0f1203020c031501030302120f1b01020412030203031b03010e04060203130c 77
    0x150391504246060300d4424032506105201a11480101112240305141c48001601040c00f0050846080300d000c25541e40d40002c1c0e503284d85070240d50b18105480c2c094090345001d403080d100f009040000522714100300f207030601290b5140d45c8940300c507030941d175a4a009402003840e200400c5803149804410340c4a5500618103135014080e401d841c2d01d0000e000a1440074140c06c140f000d83c000c40902c2211b040c0005442d0b0a844251001090641e5501084840303400b860040c41c20006a1490150511a9000103801503a000c0d41c240d80c040004401481410005885a09074040200104109440010803c4003406100e48190f41001c06003600181c0b4001d0340c200d0340c11111200c00010000c26404105078500150340300d802a0901c0c01c0c508542030b05001d4080c4c5c002c040080d50b08104607500013076044402500745105021038512031414001d42c0c9030021070340e2020f04004210011520440c450603039040750046181e0040540d91995642e0181d00041e160200a40030b10908400103195000008007 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 57501604 1250 57500354 57500357
    0x1140435010606080f0108030a05030f04020f06161106030105010e1302070b040b010609050306070f0c03090803040902090f1507030c110603071706010f231b0601030312060b03060d02030f0a03 84
    0x1e1360605454140303000c407040e8801c1c401c6901c10415401d00d00e0700023098941c4400146149522a9a54008505001302a40350740c0d9100c1c45c00608213400006103500c2001080c0150f6002590484406c180060744c4000c2c000c3c140481c2c40d20716080351902d808041801526080400541042c00030303178a040304000306480885540c24040c0c01400419071003a5000014042207000f0041810580005406914495200d42c100035190860b403041c9030041481d10000c0951004070703590340d42c0e1a02c00000075000f046086104240e14270010a030b81c40c10790b04141d100c2182004080c60302502e03613800d90316005400c000f180c05145410380b80c140303a03a40c400a1445003503181c6403299110004182107884c420000c02242c1808402500c2c075404a5210150b200320040f4494002c2521042805900080c0128100c000c03a103110b2080c441c2e0b16a0010076054121ba00c030391540f20780102a40034070000c1c2d030101d0040000ca070005000080c1c292030726441e1541a01e0026081c4d501080f2000c03c0e460504010060680 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 57502854 1250 57501604 57501617
    0x60703090e09030304150203040f0b0c0d0e0303010f060e1c060609060603021206012a050c09090a0b070f090302040f2a1b050c100e01140435010606 65
    0x4400722503400c40399400407008000d03520b5840c02d0750f24141181c01e18030606140c3c4d640480020100280c60f00ca21644907049888564103103040100e960b1035521404440540c42d044c442e1385a0151000400d6034140c40d4010701c03901d50241843d0046035070070398055100d54410048000a10443d55900c46100403500400c2d000c41c030a41809005011f85445900c91010144108042604110a9818a43c00200074078120f00031480072040c0304900302d142e21840b0344650004c1d080000304031000441003030b83c01060b99506841e0381c40c074204948510002802400310b003e010300142c5001d204004036042d000381d9003001e900c03054890700405c04a038103603421210b039a50303102004408100000c80da044008c004a0303a0410700541100d00403d003251043d940ba10160300d07280b00704100a428801610998800f6125014042d00404014101711808220301c1c0802c050281e10601407080c623080700c050f94564098920320030204a40340b80c04400700102003e044070a40a0354611030421300403080203003a240d4400 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 57504104 1250 57502854 57502859
    0x1002010b19030b0c0306030c1012060801020c0c09072703080d0c11030a020307300f080709061403060414010b0702150306010234030303020307030b0919020f040506070309 75
    0x3d41c441c240240c401c0c1038040d0207101300106139500150b50311045c5425541e000c40d48025030015140300100000d190310083c208203022541410550141661402c800c04070765004007084e06201004d0702c265058400100510308038400065281800f00e07034103044d01207417104540e807034491807c51740000000c03090107900c500c20212250741c0300d0070444120001c04065482c02d85000d0b406550f9100c2c402c00240070410140c50400160003510710120002c0103803001045801c1940d0008244503102491040811408004207031440d20034212041691403039110341201c00000013030700c034064000400070307984640c80c0d41d00f41c09680d0002d501507000b88003501c4069150683d41c070422000da000012035102c0d0100074010080351380e0b03000030302450141d0307031644810041d010300308216048041a100c0c0e801c0c80c40400c1c400810580e169000b14440c4102d0b550800c861018039040180d8041b042e60420059190f100c41022480030b942d0040c0070107032110a415162580d185c010485e0f581001400350080f5003e034508 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 57505354 1250 57504104 57504113
    0x20a030b0108070806060a12090804030501050712060308091e0d11120a150e0f1903091d06010e01031401030506010e100f150e041404050c0a0b091002010b1903 70
    0x81c2c2e500044107050000c510325049010a43e103018084d0400108440813018258011099016044d8181c00980c52681c075134032403d0007406070606494180000301c030801d0002081e003c9100303040590b40d00200e203a00d401c1c690810820361080c81d00079485408611000185c55075030f43c1c2c0d42c6c80b02c0c1d07602c01c10b03000400512110400c5640c128100b0b9609454000c5024040080d00144003242c061501e4000080c80100303c0c6000c0346000516444d01c9840d11401c5158013200d021072280002442c03107561001c107500c1d255404920003000c0d86800c1240303400c594020412545c0aa0340c007040189040c50005990f8048030b101c002c10b0907003070340140c13280c2e040348005114400602c5100c683c0314004100c5156440d251000101c000903062003150201a4803500c0c0300b5400388661400032070014010b105004e011504481181807c109443c1100c451154040c603200c03a051001c1245c0031920603000e014241050309060106030f2200c03802c01e130215503131081800f01356602c40a005083e42000c00294005c542903140 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 57506604 1250 57505354 57505367
    0x30c0b031e1e090d0507020d110a0305010e0c040207030807030b060c0a08070501051f031401060b030a0507020106060e03070b090301020705010c08070f080c0403080a030b030f0f1006030c17070306020a030b01 91
    0x26820180c0c00c044500c54043d17402204039045558180c41c04554039025042502e485002510742d6a8000910b181c000244101500506c3c100000752007500e51500c0d101c0100b004030700c60600001d010480e00c20000d20218003e502041c84088046d08003850641700075040ca0a0400d01c05003101c13802e102003020780a01c00300b4840d0340d9101c03402000f2801b1081c0c0e01c1ca07030034021883c544001001c440c030074148240051000e4202d40c00404001124646a0404090ba030000d40811240400150710b40a40042d4241c42a41e09000200001d400f62010f43e042c912014075581c0054a0780383c0540d000c001d1100090b20034402d950030b51009560340f01c0141030181006020034601c0c040c1c9020000c180c024841d451802c401150304480c2d104c0a00c590b1000b40c14020b8009c0c20040c00201e500d401951002110080301181012500d0711800c1510f89040c02c00356400125010b03800042d01d40040c200051044030004080c3c000101051422900c00c65580e903a0b42040e0b911241029000035102c0c4880c10403940c0010 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 57507854 1250 57506604 57506611
    0xf0902070c14030316030509031506030f12030105010c0302070302030a0c061403060105030a0b01030e0714030d0201021c020708040306020d0b040f0504110f0103060509100f050a030c0b031e1e 84
    0x303810b212207191030b00065903e0040e0fa13075460017a600420804100350044080340d4003220007030161071071000e03510b0090316140e400300c03210781c045c1c066114040c0f9411808a08801081c0e101c010040c10769081800450b004402d00348101c05500c40c02c140800583e03000c20030700d480c882c4180000f00003d030500178009c02010881d404034038845002c2c021710040303030303000b0064030344c0000c0014001408103c0900101e0181c407640341240c0c26030107035020104500340303c42243e45007814164212085c055081000f28200e100d114070301001c240381c1d1800c0300b4080c110b6070014586c0038002c100a0b0b04050322070319050201d038011494055610343c1c0f03025101040c00c00e400345801e031650001d410001454243c5070102e6000c2d0000b085441003100a05040c0316a010b82c0c080c1020306005000b4000914040024804141441c0110250713840746840c00202480c00d1040101aa60320a501c00d0240d0700e041c01f80001608003410004212040c52040b03003544e01c0b9410b070070344140c2c82401c10619414840d00302540344180075 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 57509104 1250 57507854 57507869
    0xc080f091906080c0703090308070308180a02030a08070201091505030603160501020a060f2309010e0a0503040605030901020f0a020c040b030712020603090f1501090e03030106090b0901090f0902070c 87
    0x100701003044640100f00030f544900703440d0240e5902d104a20b41203441d603482d900000d0050300045510000e00d603005040600c02c4444e4010044d8400c10703201103071780e19422800002d615a01a15401001035000030290031843c2c418101040610340349d646058803e80300c407020b240005d001000f0420f003803070104200e003401a50b80040214503800c15000035140c442981019001544540e00003080b4034466210007120f0620141241c2e031041c86103101c1d4100003050724120503035070030000384100c44240400d1080060750b1180003180303010720f0030308140d40d60340000b00080e005560034416992030307110b1100104100810380d40980681490101000100c603041c0c0d000c103020382e00443c0d040c05104103400c910880d0580480d203450f125a141c0840341d01d0300303000e2004500140990403030242c0b81450a40450705980c0c07070510030b105150700300025941d02e0009109602c001804070740300300202260301c0018040d0710410f01d000c12101e500c030380500184c00d10b02e5011702c25240d800600d04090160343d0290a0107088070 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 57510354 1250 57509104 57509149
    0x216050108100504090218161e05030f040305040807030f05012a0315030c0605070512030c0f030405160f0807050f0a0605030c0706111c1404060b010c080f09 69
    0x10b4400c0681601550040e14060303070b9100d03002c500b50354030709480e40c0103140300304400481842c0541e211240b4a08607003042c004182c1508000b1400781036490400803013241c80c0e0b145811546d0ba414106512030000e40141e081c03180801003c00c0d05d08040c015003028600804901905000b1441c0441c00c443c045404000d452000c58032000600480840091400700c0a00d27010a1103400d01107106003d00c100d030720040083c035030213400080b0b079608400541761080c016020344034030492002c0c2d9000d44e0310086070001c1600d4400c020620314042c81c0030203580c02c6806030040750b000407030084a20028040a802140c2c0440c070303041c2c040194600402c0980040e1509403036201090469502103094103d1030f0148209101c00440029080e44496003928445a08008203000030700310404606028ad00050400c440c40c10380055044407030300c031130080c4008158000c107201700075a02d984801008125005051341080100282100452001000380c5020104107503440d0780c400208c820410007080b0406489400c2c040c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 57511604 1250 57510354 57510361
    0x601140f0d030509150d0f06120803040b0a020c01020a020606030d02011802120c060711010f05120a050a180b0f13020105040b090105091005070506010905010b04030201030207051006060216050108 86
    0x449841c0300c80c1c4540d250500c161500356400004d0052216000e14508544004c03422072600416500807480802110350700708429505d400b18860007144062000d802c03818208040b40004040183c040e900c122f82d010300504049030904103e084e03911260070500160b00010074000726150900c0a800b0b4100180000c000b03880300600000c8208030752a1001c2d104000c840150715851800b4002c00c0750041c801402e15540c4c0c00d4a2800008001c007090340540026465140d800c1114050f400300e900c80310266049158039521200c0e03120107404c0003414042101d032644203069039041d81c00c40100381c0511078020ba03041d0307241014504003a001d0060055403490481820b02c00940d0b006002c840c15a81d100017905c0d981c0c3d14000046c5e036070740710f1010955000410100c0e0705010560050250800c1882801542d0f07060340d941c1c5484003500d01c280140400803508100c100010f6001350f0080049510810a5481441c508020401101e1301ea602c01d00140e0001040d0f011500290100c641c09842c0908080e109800d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 57512854 1250 57511604 57511609
    0x1080d0e040509120903030c0d02060f07080c0f0d09080f04050315040819180303080a050708090304150c020603250c0b01151806020f07170a060b010903060603050601140f 75
    0x103185584404d05041d000074080c1a5480034001c035010900d4600c201d030358030394114000941da11001c441a83c458000c1d1400b2a00e00ba114001d90b900450841105a00304132010780c13030485a40c000c50302c101d141c0da0b48441c1c810000790303041c0c00351550244107100a03485070300e0a800d240c107100301c070030710541c2c5c400d119010400000d80300004e40c1c10445408118220203105081c0a9880c600c600100119031315400c103000040551166100740300e48207140c0c05014584a21005807010301c41602c2420050b08103000601200b44003c0e6400d02513015440c0c007111460545c0c0101e45294410785809020129a54043c7d65103601061868001c410a140446e418a00e64079210781c4010103000c2c04421070140c2d00a180700754800d051464203581c5500c14207041a0b6110006035660500c43c0e0102e8082c02024000604c038980900c1c1007041c881c0381e0001e0411141c05035610402000d07081861811304c2102e10010020650340d105003001386114070010080b40d4140400100117004042d001845103068a034500d02030b4 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 57514104 1250 57512854 57512863
    0x60f090503030f030606040b040306050402120a0506070305190504050d0305010506130510050702060d06030c06090806040803090a0c0803040302041515031e020c010605150a0f11070e01080d0e040509 87
    0x3c1e00d05140c40d00e90321200d001440512807a440b082402e9004600402230140f40d612090146100701ca140b030041400040003500c0322500f1001810680210001a181c2c9000384c0240d0b80c440510900005040c02d5801d80f201121015502076034280d01c11000d4120480e01445441e01410007114201e0404904222000f120311490107410b000f076842206101d0858066815104c0301c070750003080c0503107420119030114010301440c403050722003040281c00020518001d44044080e20350b500003500703080d078580e207945d25103502c06842c0b84861312884a000f070100d0030003108a00901000800756645620f180100010381d01d07210700424981641715000c01480d000580c0c88020307001035040209424600101e00b900711103521000440090002850000c9180f06510040598000319a0400001c8200c000e21085019000d02d40022400ea20072031100707140119004043c640d00d1200b21454640c46000700506d1017800e03800a80140d102003070480c141034100c2c0d105216104180c0e0100681d1402900e0113984 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 57515354 1250 57514104 57514117
    0xb09070e010b180103020d02071a010b0a020a060b031608030c0c01020102040f0303030504060902060f04030203120310031b0305010204060306080f010b01020619060510020607120504020312161209060f09050303 92
    0xe083c5501004046034040c1d0181c4070f640d840794000315150b4019050001c071041990906d4600c180e142030010400680000030342d004480c880d4001c1141e140d150751044014034107000c1c0701d40d2521800c180d442400c022a00b0030b80c06018a10041d54507241403105140c5480e103200c040e00d055900506c01800428441440f1000712a0145030104e26a295070510000034074601c00301940141000594031034400045005000f1170f4420380c2100c8410030307103219026280c0001d42e1000c8805455440c01c00115060024050000034640315001400380c5ea41d55450880e07112f03038807c0000c25250311041004082c01d004d008a4412000000d014424006000035241c0c0b03c002c20074402c04016030207541c2041c0d42075010401822014240d80303180ca400d602d000c2d6a840d001c845185c00200460b400d0312015203a030103002e009581c060001e04160700101d504008075000032140611000100380494003040f1080100902004661034070380b05542407000080a4102c2e0625020174810903030400c016949000044904 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 57516604 1250 57515354 57515377
    0x3030f080703021b010e160f27092d050d18080717060705070b0114011403160905030a0302060609070e090103050c0414060f01080907080a0b09070e010b 67
    0x465a60341d103000c0d40240920081800b11070f00d00811400044d205610441e01801d0705411070302450411044c00118026034001e409440c0c03070400d001c00480c03c80c500756102007910806407410620b90303040d0440072244180020340d200b840e001600603071010715210400e580c682c030b0002240d403c500340c7c480c275a031030680e06603d4041248000c04d56080ca02080110b001400d022070607201c1303165442104405107443c40d40001842e0150f400840c0b0218080c3c3c04480308241c0c0440800c58980c03070b00c510204110103084449051100381c000303014031191314000552046094200400c4901101c0f00000d09207034154100b01d000e0390200d82d07510003284d00003450603401041101c00c401e040c3e96604086400b8030b118031744075410440e940008020040c000c10b0040b2500c509035810130041c540140c0c1401400300568009411411109905219512540c074295100001d80100c9520350341d5507112924006407400305403605051042400148c034024060000104030000302c000c81d41d41020500000780c451b5294145 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 57517854 1250 57516604 57516617
    0x110a1203050a200d08090c0102030a0c08030a0609090f120e0d020d11030a030f0e030309060a08041115071a0103030e0d0507030c0923040b071419030b01020d0903030f 73
    0x4050f40c90b10354181c2d03d41c0c040f6109640c40d0708a1070f00040c2180e00203a44848141c00b80301000c54880d4030000030703690f2656031903464010000c032544400040e40c0c40649503441040e00ca035000300e5004228014100401d1090a031880341d031160707050040e016509108540108008610fa912140c1d03103c3c02c00840b900d0f01152010001019840c00304c80000d01700252075054040d05805009042d08000303005442591a00c0c1c0c840f03010794002c00c00d900c07486a5141c055001e88180100219280305201403079000340305440700c4900380c030200006a4580f01a509485584500041b404100000d09901c0f00c800c20070030140005550650360040e20f106c06c1202d00c0d5000307010704000001446003c000e02801103810202254a098891400c1e90180940c62132803e001e00340384a042885910482c1b82070b210b50b03000411088251152981260030544050070071100d02405c1c030010a444900c44002018500d040d1000260520550006824814001e01041c20300c800c03000c04201081d08440c60301c090410074603021 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 57519104 1250 57517854 57517877
    0xc090126010e1605030706020705010f08060402160c06030b0604050901060e1906020a2307091e0509060f09150109090303020d05070903140d1209030c020904110a1203050a 75
    0x500400b41d00c001d0403518450b541e07000010449a802c9101600d4054054501d816200d100c00d90b5203070380b24801c580c00503c15001c1c40c2c03115842080e80c1504900014005071610180480740666038500d02000d41c1c66044c014420040560948200c0d010480d050f1126410a89803000190179918144903803024045010980e04d019515a404100e2443c0c0d012403051805031030b00c0000b940c0e134680200407101520110350300e080700c0d03041e4400c00034400c106000902c0c00d00e04200c1c0100280086040300380d006c4111055010322202c01d4001c1610170903440c002412640360030a0701c02280c400160200741b071038102c207403440d0566611155007415107440c020041505001440e04070003c0c4a02491010f6172458003051203400740d803242c0c0381c0007200d00600843c4461241ca0540c5034a92210410301408118014051002032001b9001034842c03600071b04020610040940100c3d82c502811141103503802c0007540201002e1a00c140240c000e00400990b411010082d550051f1141c41074901d1030f0184080d81050303 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 57520354 1250 57519104 57519179
    0xd030807020105101a07060908040308040e01050f0f10051b010b100c02060d05060105091005030a0b1c0b04051501060504060f020c06041404110d0212011401080115050c06180c0901 79
    0x9800f0032a44027800554842c1c1d0f909004101f41c2013409440b058401507400021039240c030310803021007102c0090a12803c15000700c10401c040e021172a41009106040c07018014280d00c030001584201100381c0041901c1300c0c80d0040200c40788442804000740071030405140701503143c4400313541c0003041c200c030005038988a450060340c250142d2404154031002a40c0c1000c00706034000c01850044000010601c4042180c5c8104140506109108101401d60700078240200c0d400000c9a60403d0040c0d0545000521920f40540000000d0b00503201260000400b0000ca03a4806094040d402052014100071044640002c03107074402c0d40300d407007982041d8489521282c2e503180d10a580346506042c0c031642d074440b04401c5074007039082030b140303110712000e990000134684418040e40d82243da8140d490b4425a8200070641520785556010b131410040300303104000501908104080c0a210760500c00c21b0030701080344000e0b00c0c210103002e010f070089191500402002441c054200080031000c1c00090140030344014 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 57521604 1250 57520354 57520361
    0x5031b040f0f0e0609090d0309060b030d0906110303091e030c0105010e07030e0f0705040216050610090608010218060a0203070206270a21110d030807020105101a0706 73
    0xd0484800540307001403100d00301e440c64001c40e08400f011400c150755200800070109012078500c0c445070080007000c0542c911943c41540c1c0725104960015241124801080c58110503070811004582d401e42c5c140003064000301d500c0002d0085200a51840ca461100240c071001c280b0001800010702c00c0310072603c0f0740d040c82581e4141d810a00200459030b592055460b0a50060b1000000320b450a0f00ca542465404170300074079000e0011004281c15484c00003844000c0d07001c8008400800845003400b8000b039410310941d40100343d07500018540c02c0c1002d4000c41180c3c641d50107681c15030701c1080041c446001d107080c2c80d50b0794541200ea013a119907068600303034203610590600940c081030018007020605d8045144000303070f8040000e09030348004d084050064034a0f00e40101c0c0c54500036840c00d10000032102000700b11280c458582c0421350460b860218140d005003503011000306000340204004207909102d91f0340d211080e0310940ea0041e140c6140041d4009450b10070609512000a01005000c101d82 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 57522854 1250 57521604 57521609
    0x20409020a1806060e0105040305032505030f07020112020301150c020a09020d0227090c070c0308041d160e1201110f0d050702070302060d05071e050703110d05031b04 73
    0x40000600c11050b000700c2000303040c0c0e4003840300800c1d04110710000d01c1d44070b04145c80c15039078400011850580742ea81515040990307640300e50045080c44000000052080c07014200004440340300507142e114034800074100b4074250380318030075051040c80100603080130045120070075269800c0c00d000054040c0045100d0511517001845164000528440700301d825600404590a0f11480703001c1c0c8443c440312400340090f140d1416030380850003c001c501d0640d413010041031014400e25524041641d40d554034105500603a00c001c08584103001c901c0e107126248002650f00c03081160404940c88035903403011f00202c601040d03840c00f03404e1103c41076440103025030109049443c0302e040740340c0f2060302000080c11075110002d100c006a041c000425519400002c4207001d072030340105828100701400710110010034000305600100b056a80b070007040c8401020200d507000309181d482580c1c486950801501c4030b40c0b40b5040803c190301c0319988200d0103500c00c056079044010300d5444025100b09201d80030700b034003458 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 57524104 1250 57522854 57522869
    0x60902070f24050907050f06040f050112090b010603020406081008030a030209011709030408150601020a030c03170c190809030306040902031e0d090603200904060b210906070c020409020a 82
    0x905104084400140c04421100101c500603074040da164182302d520f009520071301c41510418030050000b50b010301d60715a00c0c0500c10800041400c502d0310b03100f84446080c0d01c940e0110780d0008051080a03840181141d012840c62210104640b07451402030ba00d10902203080e0405034041403000e4603a10074018810018400c550203001400c104c641c2c15100d80c000e00c030340715041c0b00c2c4450514028581540291140c0f01c160090004c04010b924291100d8156035012000c02c9107048402001001190800d4080d002040069403200800481801e41342c058101344030500000e502000300c0400000100c031f5100800f540d010405030002d02c0443d02d440381402142c8040303004600f540300f90720400035a40500502e160b9401011558600c0b06500b02c4d400f01440030380d225500c0c000c0e4104017a084000701907c140c05800091031540e01d4107041c125030040f078400084c50f030459800d207041038081e582e4140c01c0100000903111500b040c0340050422840034030001d01440d1103008020542da9400004401001d80 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 57525354 1250 57524104 57524111
    0x21b01050d06030b15040c020f15060111100b0406050d0203031611060d020a080604060b070b09030c010c030204081605210a0f05010b0102010501150903030e0a0902070c09060902070f24 81
    0x401c441031700c041c0f078100e2602403443e01c004910302910020b515484004070f0406441c0300d100503100d840c50260b00614040c14030500c40010b0011042c10407000305070602404000442105400c06c000685040760b2000740707c0c40c1c5a03444400540d90100c121103003100a4802e8860310309261038400c10714000070802581c4030101203489103117540f080c0c00504a1000c0e41c1e4400c0015560001080308690a501419002030f030f080c085030000460307980c0415081000f440c102d070b00340024503d00500f582e646103000c1000a8010030200701c621000c00004428842d0f100c8200c1e203080c101000315040c543c00d401829908880020714200d00300e000d00c070f40c03800c1c6600904039440e184c0542c142503000c4d000805d0075500540c1f0345000000e000c450310141480100b60f42e924030b0411031564078111944011040708580c01000e010740024441d00d00e00c0200880ca210b13241c11004140303403002c03c1c0225400c981c00140103500402a02c0c0004001e8002d041444d50320030001800c0c1403c0000c407141a6010126403000c10f4075 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 57526604 1250 57525354 57525361
    0x6090608041104141504050c030402040f14091e0102090906011209020603010308032205060703020703031409060f010803070804050402210a051006021f05063c01021b01050d06030b 79
    0x201140d1051170364400f20162071a0640900c01241c00c11154030701d00200c14400b260041c50300340c10602c480351100c1c101180d0040030710148105500d003603903604d030103911503803c00355548074900300640030424460086040981d084c020030001080144460b04000103010301030890b407495442142d450780c0203404240c41e5a124900908181e2090380c030080b0b065443e46514603c00407010040402c2980b00000e4400d50322500c0c000da01a4008200813018580c442c2c0d1001c8031840c10850081c80b40350303001c00502d11410b120a040f03103c00d0040e0800d05442c0c00c20800700f0040344450044a0482c3d07000e450060f61010b1917000c82090082c0890200c804107611424031144100c1d94114030b01642c6614980900303140e85110599891382004c101e0441f0000781201b4085100641e401654400c9010300084000a040551000160060003010320582165402203101c00007091103194449800e000608040c90003000500300c00120000460401c42c0005a00c8403d44d542c1c0c011000031a845003d6605504 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 57527854 1250 57526604 57526631
    0x50a0512032827061808120306010f08070c0b0a1b03060e0a020403021305070306080f06010806010501080403022517060115030501030b0703050604020702060a0305060108010602030406090608041104 87
    0x34680c2c60301c01c009a098072a10800366000c110b110780003003c0b4241d00404a00d4910b081e202950b80064030414825402c1c00095840c01c2800305039601d016014049030303a444c0c0107001521500025044904101c2c1d028108441503821890160340e05030002018100e980d81c800c001c03400b60410702402c86407046010006031145825401800a48644491000c09982c6e03802c000ca040b0700452002941c018020f40101e0504407980d40041c2d00010246000714216032604520352814007243e062025551044004011302c04041c45024050002440d10007060308250318020350781c60465605030400c04440101c0e100c3c44a0000c14200208001c9508060240c40e500d036072911003e09104a0101d54600c40b0040c0390310b4840c1c86280c0c143ca034444260a180c0e01c1d400c800700c004203001012690419400c01040d80943c2d0750301c0103003007507001981c2d000c541072814030700040030101d06900c44019903105000c10321015405c2094102520004e181480c0c0c80d540c1c5040c051140702e616000150010318088001d445031 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 57529104 1250 57527854 57527917
    0x8130f05060403090602010e0a030c0c0b030415110928030c0909060b03010b0607080703020a06090f11090c18060909040507080f030703020705010e120105090705041401050a051203 79
    0x2d40c000d4036160b40e02a502e034070590a03a00030004400b1b242d001180140000b034042c01100d681076000f0311101c10550384034070b5a135000394000d030f42c01e41d0305280003e200b40410010707000c0c80c81c100a00e0401d6074101601340e40030401c080b204248168610100c01c1c0303224004a4444030b010015500014140708040d5180c0c081801080b402e007041d2049400d001d240c03681d909050103140c400c2500a0700e460324010b015143e62180e074000c00c0048045024111142000c100769000701d04e0f03500d005481d590523864240c030f4505011090f00700014091600301c0c04101940c001c800a2701d20020080c18503c001f46084400181c491081c05c008a51010411051005001001515600b503850f0003003113a42e10303010311520385c1e5240a00c4000a005070f20800c01800103520034010803410700006401880b100904442c40f500b55001200c1461156201500030041487e00b4001c034117a2942e0340440280b554104400300e8403003280e44c0540340c0250070783c4004152a40c420403c0700c038800c900f5510080d03ca8201d0a01e1140c1 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 57530354 1250 57529104 57529111
    0x20a15090303030f020c0a1212150522051501090e190b0109030501021909050a0e0a0f091a0a05060d020d080708090a1d060405090d0309080405330301030803040308130f0506 76
    0x41d8078603445040340c48480c2b044d0500015907401c1203090318580301c10803400d103100694021554ad0410540142c40d070043c040c0500490f00d09072841e0780340610b03400052103480190300c000190300c445801d1014141d2030000050040348520b10101c1c50f100c00c2c0e00161a03c0d4025880200b103076100159204103000c047c0b01d19440c2c520166210040303140e80c0d8007080a00cac14203000758001d000100d004500826115401504a0011241d001c03c58008a8a60352100c8844038048100e12208000300030828030140b199030b5000d00115015800300a880c1c01041075000781400c0203004c5000064103405100b01081a01c010810082041d441ca6490301c80e0780200c02840103000c010104824007081141c6024000c00b0b108001c00c500a0680540000c01140070f41800503042d903100d201088082115110001415285d20b000000e003540001c00c01e10041540a011a051158410500044c000101010112500320744c0500e0700855646680e0018440010901d000074824106a4604400c06c5000304000c0c0c807 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 57531604 1250 57530354 57530357
    0x21c0207060605090708070503060d1205030f16020709020f04090e030408010b03011422080a050912010903090303050f190f12051b0a0504030602030a09020a15090303030f020c0a12 79
    0x803590f90b02c14058001020b942001c0407400180010301524402c03005180c1c05a4018660161164661a1819000701c0b0f1002d0b2000101e0010400400c0c401810403540c1180c65503074440c00900103c00001e460f0300c07040c0200003403540c00260b203041d40140c03c02644e02a200d04941042398440c0405690703525800792088450a508052404c915441d0601c00c50a010703d100181450696803d06036103120840c2000c0364403a44003424842c004070700c1c1d010140800300c3d01611516a580e0001040150304c66a925030b0090681c10200340340c0c00260300014400880e40d140c10443d171102c9401c460b184141c021551600c1064181f583c80030661940190f24594441e00d50301d82c107031503940d01c866aa0a549080380c0d0921000109400385601c3e00c2d051000f42800038440c94054180741e22035441a003680e01c10794801140d1501c0f50301c12415440c00c0f03150400100556030000c1c5000355800c1c400f40c0511140e1001400b41503442e00c402c14024055012502e001c02c0b20010b41d03100e511a40703842c90082c10440321400 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 57532854 1250 57531604 57531611
    0x1201060602070b1204020904020d230f0c030a08032703090f01030203090d080a0b0a08061005030a17030604060902070b04030e06070c03060e030c070b040303021204050904020f04021c020706 83
    0x14541c0d0410f42207411401c01822900411303940c035000d1010001010300101c0e044200d000860012032561102d50000c00894459401145a42070b40d6030301d00300889000404079045140c980c043e41d0340008a42051551054a050722951b46008540000300c200c46562490314032241e0320207200b40048020700c07416108440c00c800242c41c82c0011022408125404103003640728100120440d4040d20f41594013088044000c118500d400000c1800d4a107158008001940a0818000c401030070900b8a0054403069000b0304501d0324540756849181c230303541400c0558203030003c0071901d19180c40c0c220b400a8002c01da07055503980700c1407500c00318181e41210203030000342003c0c07101ca81c189059411590496002072080c03d8250450b00c0d80f100910580040303035110301c420802c0412840c070170700c859001021698025600e83c5d140d401e01a04001c8a01000782070f0302c10812052020707944000209800c2038041d9041d0080c0c824007c0402e0091144010b42c1c011010307440d10000184245800a1480b54030440090 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 57534104 1250 57532854 57532859
    0xf090601120201021509010f0905070e070201020705060112020a0e07020c0102120a091802070c030b071107061b0501090b09030c0f0c03030717070605190c0c0503040603020d020405120106060207 85
    0x19500740d03400840280160000c100e11020703030950300000c58000c0144030000030044e030401c0002040380c50118089840d9084a48100b0014015a041942c013461070b0000b503140c080240c0c6e4690722481d050003000103030681da000040075901d135502c07200050300706d5202440b80b070b092051029640b8200b524181e8014800c107840750040034184000d4640503407c540752240c1031070418481d200e82042e065440140c040d07090002030040cd05885e0503c00460040166001c3c1d42003044005113900c6d85801d00d00040c1d40031034800c0107a142d011a07410360701501142c410651803250b28046001d02200b42014107202d031a00700b40a0a240d01000401500e9010343c1103e90031104888410b8940890a0304c5d940d00d42c2040c0140d8000c44d0100304408000f1804404207481d040c01542c614084580c01e442c01501c80208100440194a41c0c6c804c0c208203540d541400080400c85a890f1580ea01c00d500a24003096004942086078103040c0c0c05480c054000185036030682c0030b01255484c002d0110380300d440300602c14080d00 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 57535354 1250 57534104 57534119
    0x7050909070c031d010507050114061305100306050406231503010e1c0c050109080306041107051015030b0c030f010b040602070623030f09070503011a090601090b030f090601 76
    0x664540b81d0325498041303c038601c1c2c0079600c10081182000303a05104e000c10070040060000c0c800d503c15166000c410344200c0c1007950620802400c0b40c0c1481c0c2d0403a2070801442154200b51030000f040b6584400007165954942c0352100151814401c204100c0d924003201c10313000703040c050540740300d40799401c002400040620304040c01d07038241c03a00a08403a080742000380d50800c020a81c080c20018a401e264590744602d030f440c40d086507421042901c01ca400402840024030386030044418500099000c1c9007004156101c590b15000006402412565078113945420800310b4a030000c0203503040b0215040d0340c5000440581070703600c2114824002c0c1344c201c00100d24440c0c0c5038151829101640e0040010a050203000d581e604d840074401280700700c3e0265904007140844005601c902c4104480c84001d0501c000207603e0003041c1c0d08800e120740d0402d100c0d01c1080140004184030804220b5180d0416246c48005a81d0f000c15a04070f00744652001003003001c5081c000d03441c41d00845d00c00b02114016a40e4960 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 57536604 1250 57535354 57535367
    0x150315100f0c0609020a05060a0302040905060a03120c020109050301020c0304080c0a08121c06082407050d050a0603020901060809070e1302010809120301060c020a050f0109030b070e04050705090907 87
    0x1e02000708001d001d0260100381103603c00c0007510320240482d410310ba15000012a80e4101c4103540001940005061081c900c5500031980c0108040e81e0300d0414a04503652094141d00039800d500400c0b5942c0d181f0703400e580c4142c1d40d00005000180003150344040c200c1c40643c80758400d000b6000c25204441759000141440f06001d0100c03414400603160040d090307407d03010720781d11030502c0d41e022a03106145103500752510f01c40c070002010726200600c1e41201c1c922584000c40e1a15607640d810585010811001036082012546038107131681c0c0008595580751071a10042c80aa0000385d0045c4c80340d40049696604481101c1c0241005070458040654450748c0e0300441e04211040e681c2031011110030801540114115508102e03200156016580c04580789201a0000d81c007420003d5181d071017810950421b6600726002d440d0644000d0710704031040b00080d101c04038a1000801c1d40c1d41c2800002ca20520600c241449058010000c0c407440c109a4002080c40d0031002c5402d200703182450108103458003d06 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 57537854 1250 57536604 57536627
    0x1b1305090105150f0c0f0601120515010e01090e0a0c06080f0a09020a17010f0e030a090905010e130201050c07030309050a0501031a0909010b061603030b030304140f15031510 76
    0x205051816881c0d80b54044d440d0003155000060780700d9000c101c0841c09092100f1400781001840c5400403c1b45802c046180c0880700c00f202c8020f1603a2001030180c624409201415039141190100e40c1700592080c1c245003520050011302200b9040f035000c180315070700100d010302400e0741800c1c1c2c1c5426165044180100c400f01d00000f9030065100e68100000900faa580417911030400c8000581c80f403001d42c0040945051801800103508002102042e950f046110b6802034601e0700407c1040c5d60401d00c092000820203400e2401c2400354100c1c20f000c680c441ca0440f1013004420050720000c5a917890050007103640d81c0141845480d6040d008110340d40300788900000304466a80d000c101127200803e1144280c80501903010a5482e0340001000e07490b5140185102801009008a420b0b40c03410010100c1e58811140c5100303800811081102c0e005182c400d90b00071404445d031801031655140002c288800c0b1417039002c10f08002008005841d0507000d40300d560f103070080d01d44441600c2c806104580d00c09059 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 57539104 1250 57537854 57537889
    0x40809040605012604060e011a03010c0203090307140301091703070207091b180b0f030411030f0703080a0203040906090e06090c06040306111b030a0311040b030406051b1305090105 79
    0x261881007040c0805602c04d40c005005000010b03d28083c0c030032003400d4a14480940c885449603441c8814241000d10804486010341c1c8007550401c88403900080e1608141d11501c0302c1c005820b01418099a400e42c49043c00a5010f05074060310078542da00401c0c07a80040361000c015008130400014440214003a03900794120524401051a0f0382c890240c0300240d1034080da15040300021b8002c81e05d0618600205040c080b03c180e01030310b80c07a241c5080c00181d03003541901400b039088000804100d42c400200765090700c0c1d200020f540c50340001c0304220310b940030b036611a0000c1410404005802e18465002c01400c0311040b0940c0e42540e2410015562914044d0320f194119600300810808583c1c00d6001c11540703145c4134400c0b4544450081e500291101d058410764060f0400201c003001b60b41c0520400842c001001074072400d143c5040b4984059010091000e02a2600c940009001c0300717180341d1518204000d1060551150744052a0b4045a145030283d5030107841020004101c0b841d01c66504124070201 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 57540354 1250 57539104 57539147
    0x60509010c0606030503040f090615140a020109051f05090705030318030718060806010f030503070602030406090212030a0225030305070f0807060c03230105010e030a060504080904060501 82
    0x94001115528480030301a682c0c296a420b0200001d030f0107200400c0248401c051a48409080091500c2120002d5000415400708030101e0225a034104655441400010070321948036034420005034050182c00c40010010301030799a40200d0141c4024002c1085490000d081140343c4da00394445589280710f0060300c2e410313070050081050124403104540c03910070018007074076959582d0b0200ba050039030703040d90303007003000ba449000074001040104911401041080c104418031455500d41e59120703c204840a44956000070001d010f001d0290009020158083c2c107140c882d50900809a49941028406c900180189076403441850202c0190490060703158100c10b0003d45942d0301910079a007e003d04a403240c0c800e5a034000401c0c1d40c40085c01b02940a090045480301d5040b1004003100c0701e13002c8203014090440c2d116182c100309020070a05441003070a0401002d86400002481c2001d0700c00c0003400a420711080008101c0da1a0160211141c20760301071100c103031154010740d03583c42185060300c40f0410 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 57541604 1250 57540354 57540367
    0x3120903090f13021b011b0c1a1005030609100c030606080609070e0d06020a03050f1509041707030512010b0f0d0f06030c121b080c09090c060301030b0f0903040605 72
    0x615a071480b088840e002d100518005c110200f180c114603200c0c1038054141d5541400c00301324072000041101503060f0f03180c5119041d08a81c5d441658280c00c149241403d00800c3c002290307544800301407005490010211134070703886c150b4030040d6928848045842d07030b141007036510b80f502030080c003541d801d50711740d91100d0401da5030742c0e01441503081c0000c01c0401044203400f9024030341c0c0c44400c5684805c034040c01c80075923039049100c07010303080d0798000c0c100791001610701c0100a4010072002607111758440c00c4a035480b094443e4282400c0c0d01350b542c0e807081500b4a00185007020190801c0040615841c010100c5010740c1c1d0381c903190f00e61402103000d102107a09040005407042a02ca40c0a0801d4800c2020009111070722900c0b090042091078004906c0700c160f03805170000703005801d40c810b501286213180580c0c1140c1400c240c00c0d00d8490421109005251a00c0030400040040c450144200c6018260700d0700c03582d503420b05052907c0c09981c404a4031088001143d00007501000700c1d02941c400c0c2d100c2070328228 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 57542854 1250 57541604 57541609
    0xb13050105070206040302150703020d050a0f050705070b040f0801050606030403020c13111204150504030f0e0103090204110301030308070503070f080c0d05011401110307051b061b03120903090f 85
    0x384030a00480e4818010000403006030b42c1c0c038548d11100c01350310200548401e0300d440c019151040120030b41040c06014400440450350182c410901900d503131a1140c0c4610391850300c10710f441d855130428442050007240c0811018035201004080303912960090005843e5442400000c2c40203550180042e0800b40407906541070810350220b071186812000250010903000180b85c581188040d2030070500044148020301c13040c81c0400507903c02180c070401280c201075501501c150305d91002d01c2c4c103114500240d503d160307001e50301c4600320b02d8014001348080500f1001c151415030007400110042006000480c1966110301d080e248240041c1d1a0090603402e0300300305585c00c030741c010100507481004024645122909000e0b1f01d0080c8101c0d1500c0b180c0c240306d0000901000031040c07220710ec80d403080c058038020940010351851211403000c4030720920490f00d40400c0e81440307144100111085110f101c0e41a0010000040075030305002c84401300952918000c040e164414a049942d106480040c0b42d1881e1 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 57544104 1250 57542854 57542857
    0x6090b0a05060414120715081509090c040c0201022215020d080c07060902040c020703060b10020312100302220f09080d0c02031909140105040b0f0309011119090b13050105 75
    0xa903d68100c1b14040d95034004d1f0800a000c10540a00080303425040c80300e4089007541000ba0207208464070b090605d4192502a5500d40ca40151031040da10f42c7d038602c003698002e40c100c031402c414162044001a1501190b506c0a00052003140c200101000c8454132082c800300d0402c110b541c1c15600c1c04000e848a404d1805c40d0782040d40e00b035a60075a51000c1500690301c9110362400c2201c550007800c0000d140d0701f000c0c401c075003446694901032402502540803072a404408c40d012129040400400c03a19403040302400d610254200031b41014800004c41d81c940344904000d08003c0c4525003c0c00042c030141528003d56100d0040103200f04014041450451456003060b007151105e0f02c100c904100d1321520705407201c94009601c0000c10880c402c148003405640c09540200002802d040303227080e2400303180c454503201e03000c20040703807210110100703655a50a40040795052141c1160070348840d2810034041c0007109407001000411507020000a0440b548810740c1d9126030b0a0011290143c600001035070315 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 57545354 1250 57544104 57544129
    0x603010b091c03030f0b0a0b071e12081f0b0f0c0109170409050c13060c080d0606030507020f0c09060d0221010b1215040f08070606090b0a05060414 65
    0x20041600c101010030240c000d44100b20ba000750f034041183d0328a541c5800498080c96816030082c581d0120500403001d0207000c8070300c000c0c4c1c400c07150010b13540100001c000351013041800810a00c0d0b1011240c0040d903000361020b004428901e03004901c81d00f1098000c9010031140300300744041c0014800562a0840d0788054481101008008541e913440ea43c2d58a03c021102c0310420068000800c0600140c1c4241c8209a844880914441d10342070340b480ca00c2581290611460742002490903041c420800d505d0140e9208030790040d428008540c9174600600501005c54941c80144154094a070b03d0350130005003425040001b61403410151210010f12200f12080d107026600b00400d00365640c4410840e03500b11200300700090000a036941c003001007290140064015280d0742e8040501d0201400301001540c0d00207a010103070a100c806c041c41c15500902402d24080c10716490318000195401c43c5403c448025403041f074481c01705980b14003c0140900031030040c0002242411617000c800d0805084d0000c8 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 57546604 1250 57545354 57545359
    0x6010f051803100609140f04060c11060c030609060d03090b0a03020c0304090e01050708040b0a020d09140114060a0e0a02090406050a06030b0108130308070804110a0b0405100305060603010b09 84
    0x501c211801d02091414000c81d100302e00c0300c1e42d918000c120b00035140c0301d029101d80b039041211060341011011a0b9505101400107040070b551284e002160380d004044041080742d0303201c191801840c0032401726100d40c0040715020300905040c1d00094051519400e00714105501d911209a4103040c02922030701900804544000e2503030800224041c11002c2002d000100079001001c45e20030300c6140180d007580c80145c000400d00c03040106104c0000d0042c1c55490f8040300e00303100180c849140000600c09014285c4014007083d070780c04050a007052041d044250f96201c1e03a0720301c2445480705028081c0c402040d100b440240361211010840400045d00244061040140045111515980010405403803a80070501182d600c0441c0e242958110110325070041180b04205440f049988000e05040320007403860f410041c69030b00103000c100c0400c01c540c054a0b8050580303e0001e4071001884656805800341c9445501000d0703c1e4a011403084c01000d101d2034016090b0380c1540d28002c4828001d0304102444c40d0f = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 57547854 1250 57546604 57546637
    0xc080a090c0f0807080d08041a0a060b03040b070f0e100c140f150a060501050304020103020912010606050408010e03070c050904291501020f071e0801020301030f031706010f05 77
    0x60340990b80034042c00944501000b401c400c07458040701e94540780c020040c07042400b004108001c003080100b100c000703408010104075411641c407400306000510807500071040b040004400d00061003020140da621480040d00e880b6030000e480c5c4070582e003000e000498168444024517840c01154824814402942d104018440d500e030f000c2407607c3d080564650140c8140c0d03208410141044004a901036000304e551441005a1800d080c0003c00b01d1100900290515400291000c031613107031360000032500c0d6914070081120325118880104107170b110380b00d01e154540c200001001035080c0841100d0203554458150790580f894641030100545001f0400d8070709041e2510458504c0c010388034100e03410a000c40c20101140341a5954002410440070480d0441d17000d1021003901240002e4807900780c9403850600000500000014903400340580c100003215400400000b08103c44a494a00e076503119071540510b40200c0d0100f0941201c04030341141c0012081400c42003050f009400500f41c100c000b40828 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 57549104 1250 57547854 57547859
    0x9012c0c040905060f0f0405030f0c031306050c0705011715150a0e10030504030f08060406030807050714090f060114071a0108060106050c03040b0a18060305040203060a0c080a090c 79
    0x10100ca10700401541c040d0441c0c0c1c00c005c40134801c0c0e941d050307201c6104110b10b00c490905881c4c1d25a00e00404980b0820b1640000d2110707501081003013a9000b07904403002014002d62914402461070704007039280c4c4d1705407240d440c02007855030081203100701608410300180d6190390340313080c50540d180d41030710b01b190010000944a100745c640f00780123116007441625107600c007401d448184040c0d030345130992000c205841d0805100000c0c1d40300282c03003c0540103240210254503240d00180081034194401012002c0000b0340e041001004144a0101c41c1400340405242000409102b1001c0d8200d401340d2501078a1800560320b0340c01524a152502c1034540c00c0c2d410000303540c5d144034159202c0e055002c0404031480041000c1d2030104040d60150140d480c5c01400d2221007103155a0720b000718003da2111090104503d1841c5208100c404e83d085c400c400f0780ca4200e0b5035400c02800804082ea030980c040d01505000a10580803401170540580d00d13555802150768403101801c000308001c0304120790403502003200 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 57550354 1250 57549104 57549109
    0xe0f032505060d0204030302070e09030711011107060e091b030f0c0d050c1206030309030c062206050c0c010810090203060d02130209090603070509040f0501060b0a0e040509012c0c 79
    0x283c06080e00c6141c0060380c503421803e0103480c0c080c082d4810340b0515440c3d0100718403480e0101c151084160301c0090044000d900d000142e13030a504d42d0965203081d2181110002d00903610032080c0309020701c1a100c3c00720030b031205c02c600c2d9451020790071680480c200030800306a049050031401a030000300b002d40c03039042c51486000d0300240c80303080c4c43c1003002d1480441c01400c00c00300d1020058001404600031460003d0395000b19407208640c00007a48141d10108450b000b603100c400300c81d00400ca180d207406d4000ca44519000d051504030680301a001d00c0f0307200c641d40d0294086d02c0054017401c202d40c1e0303007090140707080700080c06540000d07c900c1c3c00000c560288401601e07000f000c909080009080561610a21418014080801404d0038441d6004110402c13841e00c54007000d58000ea004241d250601c1c1c0c10341811809808558000312099500145c046a0b071940203403010180e0004841c240400e0b2a010b203a01e09a48940440441c2d01001580d0b14408101c4070f15200c1100c0401c40540300c214001c0b000 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 57551604 1250 57550354 57550357
    0x18051e0106030609060509011505031002090f04050709060f11060a0216050a0302060613061202060901021e031e031006030c03091502030912040b07030c0c0b070f030e0f03250506 78
    0xd045503170b00d858a00748502640e080c0228440c07a2422400300f0892454240065a522400c95140405580c0016290b034540c844042c5240d05003c054018891414a110004c024148521035000042c0000202811591040528150750045000103200607281d0708035a0f4025885034030341000c1c10446011000008005020030820700c0d0090700078042c1c2d4a421014402c088446c4000c2c00e41c0c461a040d828000c12482882c880c034240e4041d66216198802500181d1402c0d0a03a21441e00151042403980070800c0000001c15024015247c41d0414040e01d4854031414003066454514024450f4010b1103101e00c00da211040841e030b246400f05281203e134940b10303c10300e5483c111219841e0008200300c04100c0400c030100c14801000825131601e481c1643d07003c540e0141d01e0300201086210900301c402c0c00404509030300075195201881303540300361529040a02c4004060304030701150b0b10390755074401c91400c00844500500060090f041000700380200000c0ea41d2001340309a01a40005808202a1240030 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 57552854 1250 57551604 57551621
    0x70c021c12030c1404210807020306010902190c1a04020301110a0201050108010c02070602210f03010b1201170703031101060807030f061103041709130c020102040918051e01060306 79
    0x21070008200d4403a0343d0080c0000e030581e0000020000c100b00070403032800c00780a1116108031142810f000d084c0549400c00580c4510300001e503040c031603c400450401040c1d8018030510107000c07484c01695018000550300c4d0b00c1070000c064414190214035020394000246403c0e40a440100006451401c04140c1c00681d04005070280041c1c0d550070050010309400d00c118901034401d80004c1a03002d2400700e000350f480800b0943c503400c4240469040c0a038060040590309183c1c03500d440e803070b02c0350b8640d02800c038035030004988c00f0445451340c000011444a864440c480c5004000040e2043e0750650720705440d03c800e1403500c06005c0d941c403200007031511818018180034510400341d6955406140c245032080e10700e4000c8662416408109100000c0c40040c403218000c441c948011340c40b039294034001074005009200101101b030400c4061410b0703da043d070042c0151203040c40200038140c02d83c003181009101c0031100a00035480759014029207407400c0048140b00032103034000705200b034880d80c3d003406440041 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 57553960 1106 57552854 57552857
    0x20c0d0c0303140a0c080a0c09060f020f0a050609070603050601080406090510090b2215090c08030d060609050f0307090b03030702040e1506030303070c021c12 70
    0x740c12201c3c0200f000d6190841d5840e1002504020340f41d440703040780004900030001052143e40d440f4130a200242e03030342c84001941c200380007601e444081e40c90050541c840c00e59a01c207180c004004c3c0208041c4100050b0440b070419214051030408590045802d00d81408200f1159980c000041580035801460103e0005001d080c8141022890040c803001c160401c80c182d0300b4404091141401800c0c1c441142000a204052001a54981c01c82c0101044c404140d41c803556039042e0010b003201c60080520000003136450791021f14652003481610080c9460b00c00c200001ca40084040005080c140c504901403201840020348409041c028a41ca8544d540482206901c00304141e81c417030340d03006d0000c214844e00c49a8060b80e540540e80d0303400d18404104005030305400c0110549014001540300c402c203000e056800c0140e0510000081c1c3c0704450400340410220300015491b40301da1007070307 = true := by decide +kernel

theorem cover : BRFrame.Cov 57374104 57553960 := by
  have h0 := BRFrame.cov_init 57374104
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57374104 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57374104 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57374104 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57374104 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57374104 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57374104 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57374104 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57374104 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57374104 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57374104 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57374104 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57374104 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57374104 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57374104 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57374104 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57374104 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57374104 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57374104 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57374104 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57374104 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57374104 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57374104 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57374104 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57374104 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57374104 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57374104 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57374104 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57374104 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57374104 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57374104 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57374104 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57374104 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57374104 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57374104 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57374104 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57374104 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57374104 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57374104 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57374104 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57374104 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57374104 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57374104 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57374104 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57374104 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57374104 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57374104 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57374104 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57374104 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57374104 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57374104 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57374104 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57374104 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57374104 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57374104 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57374104 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57374104 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57374104 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57374104 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57374104 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57374104 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57374104 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57374104 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57374104 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57374104 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57374104 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57374104 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57374104 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57374104 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57374104 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57374104 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57374104 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57374104 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57374104 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57374104 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57374104 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57374104 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57374104 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57374104 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57374104 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57374104 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57374104 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57374104 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57374104 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57374104 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57374104 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57374104 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57374104 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57374104 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57374104 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57374104 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57374104 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57374104 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57374104 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57374104 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57374104 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57374104 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57374104 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57374104 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57374104 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57374104 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57374104 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57374104 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57374104 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57374104 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57374104 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57374104 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57374104 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57374104 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57374104 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57374104 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57374104 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57374104 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57374104 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57374104 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57374104 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57374104 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57374104 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57374104 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57374104 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57374104 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57374104 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57374104 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57374104 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57374104 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57374104 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57374104 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57374104 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57374104 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57374104 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57374104 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57374104 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57374104 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57374104 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57374104 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57374104 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57374104 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57374104 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57374104 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57374104 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57374104 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57374104 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57374104 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57374104 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57374104 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 57374104 ≤ n) (h2 : n < 57553960) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
