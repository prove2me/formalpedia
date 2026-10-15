-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5323
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:29:38.981894+00:00
-- url     : https://prove2.me/submissions/30903fbe-d881-452d-98ce-685896dbcc36

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 957194244 ≤ n < 957374100 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 957195494 1250 957194244 957194261
    0x6090c2907080708130905090d090b03060d05120c060115050f0a03150303050315222c0a03020d0206060319241a0603040503031503150a0c080a 63
    0x10325445852045060190a03a40090310980d040303003003803160390001030b00f0100506950f0f4401252901c1c00c5c0c00c00403170307608072040500b4003489a0311480755103019641002c4090f044455250441d80c0741e6032400081845110b509400410314080c02190751600032400015080e119410411102a6a20303480c4801c1000802201007003c1101840005281c0720000000c040e550018075010440c855080c4044558889507001200401d9020040040c9c0e21107440c1201f800304411035040914284d06503101c22605841003105004540340c1c07408a040247c211800c0074000301c240300e01c000020b4014034598132954819021001400307001c000c0801e441c400070f4060300822004000e4150003903516106604180703041c0080310480c00d58904182541c1c48200310303c2c0800700011012403088811103100c41c800300b00a19991192200380207220201c0c1c000002d89030f00c40449244131400d000c00d1030001303243c0042c1c0000f0447c9103541c4c008001030003032030790805c51038002c1c2900c882c5680e464100b161415280c080 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 957196744 1250 957195494 957195539
    0x6180708011505093015071e080103020f040e0f06040605090d091e05100908010b190504020c0a0f03090303030b0f0904121e0201020909100b04060309060b0d06090c 72
    0x7948182031142c5c841e07181218140b00440051184582d60354250826000100a2103001706620400c502140c2040e012021141c002c5010f600074030f108180500351070018040a03006000003405941d4540700d07680000c04124124007160300031481010102e559001c101c400701d85142c03d0030b022030441d16000505503103038801038540c0e4603114180024070400040070703042006144004840003d69071514260b2400411440e5140f05c80f59084c0003030345080d2241741c13000c2ca000307803001203005490314025140801590421100580e40ea0703548030895181440c0b002d0007428640c100700c002010550008020001c0f00c1c4641c409005080d0070f01c0811070204031034101c0540040e4544d002900090009440e04201229800c055000c2000315444003001180000c5500250b0743c0090080303910b01e452080d46600c60388101c400000d140c10590340380e1490145100d440203050320760b5030501c20001641c00c0340310303104005807142d40003000030704000d40130302641c40017503485800a400101303454840d80180e0540c110306 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 957197994 1250 957196744 957196759
    0x1a09120c0913020102011b02151842040c0602010203011203080703150603020714010c0203040e0703021611010e010309050c011409060a032007020312030618070801150509 75
    0xc00924081e000b0240307030200c1c115540c86024021034040e040040400300d0b050f90050034000004801e1101e06600540718669851007030030590105e003c00502c0303030302a44856031900107144000b8100c0c130303444404940d4008803241d0b440180728030407003120407144a0350080400c05c1680d503035124168201e01c028000c2180303041191048202090003140c40503041051460001024240c00740d915425010030780140000903000500001030200c401c0740d02130400140d070000c0110a03185d04c030282d540d200354403a5800d450343d16800101d003903000354141c8005140403a0510036290326880c0400c2103000d4241d440303011070355404104005502c6842003822560380b200040180310042c07401500c494451241407042c4036410040c18400da05c0d25809480c0094158601062411a403100d03a00301060300c0315140e150304424409500941c1d0001420321007200c00d040c15960b01d0301d40c06c0114107441030000d501141403c031a0280b24416034814402ca040320203408034488840140507040301c5611a0b400400c0c0c0c0b0808 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 957199244 1250 957197994 957198001
    0xc02010302090609090c0c0d03110a03051807061709060f0c0913240e040302100209040b03010c23070b0a0f020927010f03030512040302071a09120c09 66
    0x358010220620020b010307a0620380074400207044050111b40085000701e0105260000c090108060b0f203022a031802c00f8800d170001e100d0852078034061450098100354440000c1281200703007210148150300c2c0d040c16140003546400002e0002500c003080c1d2500c246611001905103c008180b80d401030845241c80140b5481310115070071241c00007034809610030307480c014422014629104241030089903288130144220719128074202c4201641c0060302c20810740341040000b1341d003c11710b94a07250140000586a0b20320201140041049442c1c0316055031a200d00340503540c1d0416445108100c100f522000c1d5210807070f40c801018050b038403005248901402c08a498040b843d0010001194003d030010b00300748110001451070724202c3c1a60820700314040c0365064041c01d0b0720100d03015005d00684984514a10351700108039104d04c03140881640c1960000c241013600c03c0c840c207030007047d0301e03020495400348070714510704103902010190380f04d0060708518042411002c03c006203e0314005107440c00076503 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 957200494 1250 957199244 957199247
    0xa2301030b060d021204020f01080601080f04391e0515090d0f0309060215041b05030133380f0a0f02011a0f01140406020a0201021605010c0201 63
    0xa14080010741c000c8061098000c441c0343ca10280c02d070301c86100c0c034140442c1401e00510249000d000c1d1a14104481002005041d0341c0168040350410607400143c0400d40d10ba09040d10141c299500381d1424004054074003412140400d5442c15821182c1d03107100c0403a0780d0f11000c40004540c201e21070076144011004000504e851a0182803591545103200c0c41c1040300e10026004114486040781c0201a010098041c5940700b2600c9001d090140014506496031045082e00720000030802071801807040c5407142100301110100c4028800a8000e009600445058541d4000785140d90a4085003d0344043d4000341c0d811020411505582c5105504d101c4050010107a15079001e00000390076803c20001300800e01d00350003840000d1059982584540800b04000c100c0d000840003c01107a06040180f140d680c00c5120104440c0000c903094404084000010f0300d203090118441a007090300420000740568001c510401d00a00c00d9090b40d0305460801004503044500d40103050014020a06500055 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 957201744 1250 957200494 957200501
    0xb03070819030504090213060f020d140c0a05102921070b0d05040303110c060c09040f02040f060f0801081b210c011d03150a0603050a0b060a230103 65
    0x254000d03d4200d2030706440c1e17000c3c0e000360380c040031190710a01e0008404010fa00c0d800240300d0342c824a41d201916907240919401409040354045090152000041d0500460410889400700c0d990000a40d0f603140000f6240c440106504e20042c199a00c0d0200489042034103894441400c0d0300041101c40801030f617070402d24000c1040032107202c0300e104803d0086841901703140903044083d0950030220300c0c0c0c17815140083c140e030300300301004c80c0018050040d2480f840c0d0103c0c1e460392008044020f1511030360410000f4003c0c0030039102c51107041e4030000d4042980b41607024000c0c20760380c4540b10700a801c20f000c402110500c000744940205500030424200300d036810303a66960000c450003800603240c100f484407030f00c0800c0c9048283c5242c56000903404140741d41c0202011602030502c41d20f800038020000007103911114081c48503000401c03904c0010341c0c40a15584001c0203503070032108650f40c803003180ca84001d50407002d0301da0611580e1040d90024801c48404500c076000c018003000e001c8a5903c00700154040c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 957202994 1250 957201744 957201793
    0x2060a020d090b04080a090504060b09090919050c180705030a090507090e0d0305090102181c0c0602060f090106030f0206030424060302011407051f2a030b030708 71
    0x7692125801e00c04035400e20b102d07502880c003841c030761070b682c40c0c0c51000030748840c9203a40001d0003031781030480400c52240e100060b01c1c441034080e035421034140d4406a010341484483d040c40b0f81100091004070041c8030f4000b4140407802426104a02804030000d14013003148421141c190020b00100b00141d034013291504215540c0b0311480c01c4400042e1148061401c1d1410841101c14130303032060104582c0c0e00e505004082e04202610000c5103004414030b56154165102c01195001d1609c3c80c3d0000c41107070100c000e8000c19a00030f00d51003181d80c0c5a440c001d4440100382c1c3c1c42c08030307401801c000c07901660061080f0382c11a54011030070030a603401d603400e010807908001d000360f40b00c00e4000780c18842c60401810a50100d85403020011b080c1c0c4c154030000d8804401c204101c681800c4c14401d01300019000102c00e406071034852612503244a24001e140e0103880e0115038007225400406407c4001e0240c8404410302c415292405d01100502d003091641c2c8880501c1a841c80b0f81c440b18103100c04a0703503101c10411 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 957204244 1250 957202994 957203017
    0x31204120309181a010801050102100c110d090f0e090a03030c0e03070f06121a040b120a06020d1811061b01060e0610080f010303030f0906090f02031c02060a02 70
    0x12443d650300340602c2c0c1000e582c21194040c98446804031079203080094003100808013420040f4565041c100000e40d5420195038202a481e6101c3c040c141150040d96500c2c11808004211200780140002c0203200b01c42c28070401102c1d640b40c020115419294010781e9101e401d900000b00034840035918201e0240040007462001d101d0040101a000e440c184003a00c050a500424010454940b039801003140400070400e03502103107809020b02820500841c480910722044030041411500c250003e09481012400c0b086184144007040d401c010454024000e0941e0100c410841030403402c0009801481c0f0040040408101c007050500b10710b412000b40040e403d030795004007600a0440501800c46a95400c8075a050411108004082c508020a51b00303101840c0b800c140c0c5070070528a04182507106000003801d240c0c81d100b8505190049900044009411090074070054401d802c080343d564859100503802405521000c90300545142c3c2089407140b1213500603c003aa5486141b24025082000c1c51070 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 957205494 1250 957204244 957204257
    0x7030e1f050d1d1507030908190212030f0a1104081009140133031e080d021605100e0c0d110907050c060109110304260a020a020306060312041203 64
    0xc440040d5400c28902c640f0a0600a1651070107101c4100303a4014028040340c2014288000807000401600c00e41c0c035043d00782a0300440c036000d040000d90400c04008201d50308003002104126214420a0700e0300c1c000d0100c1030017003141810032001c00016220740d009440c080d1b03004122010503121a640694034450156800390f07090307021180c0b41400e40d1175a80788110301c5405901c1c0300906220301c605003d0302d1100c080f0494036584c031b1507450010215103160356080564041d0810014030226408480c0c1d0707104106021560703503000c60700894045401c00e606036014401e000c503080ca201d01b18880c20b1802034164000307060303010382c1c0420400b003280b540004580c913003103283c201303001c41d02e4581001c0d005810549070305840b181c03c0e1100e180f8044050348202c61050a090703410720992542021a9081608011841d0b0750f03800c0e800c40b400300c1d001d00c41a20b034040840015480c402c2035000c500c80082034822400c1e119181c451004050380d6140d8600307020b01c070711420441048844040100548410720900780706 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 957206744 1250 957205494 957205511
    0x9050d08030a090227011e0302011412010303110f0601081c03090203060a06240806120307050d050415050c0601210b070507061409120a20010207030e1f050d 69
    0xa00914803450b00c404a411001c41101114010f01d42c8603003d1f00038540709508a03034002242d500743c00f1191001a0505ca00313180640d6103441002c3c00c0b0703640c40b2641d900760f05155950789002003600f85038001c0620540510306a1401408022800c103040300c844400600042e0304407800c103541aa802c0c4499410300d640d94800d080161401d120310341c80350078005400a00c0d1480c0c15008038103c403007046034900d5400000b03155170015400840c034541098082e0340300002c09103240e50851a5100e80300002c2c0203071203004900e9190691000c014001d5070008603488100c0e40701d0300015100c1d405584192090380d0441c2d401804104202c03442005000b14003c0c0e28000c00c4696261000c06031400e440e40e60001d00000b480c3c130306000c0b442c05160341c612885041c48900345882050240c699110207050030080500040c100e21040c81242c0c3d021000c0c0140d8a00c1c180022210a42c0d4000e601c0f40c01c0c03ca01282d54a44840480c0ca0414040415158100500121400c600b038007140d4507400302900e800403590f80e0100b07 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 957207994 1250 957206744 957206749
    0x403030b06091f030b150a050906160c03051002250c0b040e0106141c09140d08040212070506030a091b030f0201020f1f0923060406050709050d08030a0902 68
    0x4082c030b5042500f484030050382005008013521200b07900c107801013039803280d404c5036441403038200e41410a96140540d00c076000c040c000b9005109903001e02c1180e100038180e10342440000034654080300d100d10100d511080e00c901e0208242c1c01003400400c1e450704146c4456501c1d81d03403003001c4603001d8030402c100072500d91550381d0080c15800a4002441055101005210403600000e001c1011001e4a43c480c2c00e00340c000e084088802181d01c0c1407004036841c0d100443c10480050034845220a0080070380e501080412002030400c0070480e000d03413140c0300c1c4641130000c608020a034001030f42c00160180c2e01c0c5d5592500031002600384460101c807048202c0d400428140007c0c207020018520400d4404800300701400028074000c11075000c0195900002c07101260018060240030340c2c1c0e019034002140c04001810301c00c984c13012100415030420700e09000c8502003400400e25520480c8104020030071a2520f19081b0390060316401200d07003100b8441900e60202b4030003000340d5408081c1e801d0105205c0c840750301 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 957209244 1250 957207994 957208009
    0x50103050c0d0b18040b07141207050a0309020402191b030203031602030904091112060c04060f0201092a06030506013e060a11090a1e091514040c080403030b0609 71
    0x2003e8501c5c07011b00302800b4040341d022a01c99240600061440e0401c007009000039007450300500030b44d090000c000f45648070741c5e00a400400174075130005c10171500c0341e1418402c500034503100001d1710001510b100c01c01100303034a02e021000c510f0741c240c0d00650442d621042e000144420000360942980700134007102c48281c0d541c0c040c01a881d071040035841820341e414018081c00003001010003040d40c12420400010083c0c0c0005d840c04c486941c41d190140c0d04202c0c805a0060103e05400b502c10080546010380c81c08911150703142803072405036045103070355550104038111042503c000f40000ca42c900c10561000d100004c004e41d029034403030149040c3d07030101210004131040140c2081142c001d113080220001440c42039031001000c0b9070700945400141780001d95801c4650065081a22560058289600c07550403400301078881d01c0070401c0342585e4602105d2242c10944103c80041c00800544501ca08160083c3e00c0300301200d844041c4a600c0350f0350309a000d001c1e014401604110144040c0b00659604031 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 957210494 1250 957209244 957209251
    0x5010e070302100e0306070819050907210507050114160302010e0601051219080c0601170106050a03030c020f040f09061d06100b1c0603030e0a050103050c0d0b18 71
    0x200600c0014614818001030159500085051101903816015142c40c0401d81c294071414034580075030740b5501c0c0c65851502d404c0080c4051611450181000f800c10000200b900a03218296540551000380c0c1a4130b01540611541c0101a41c1006c80104444d5014058180b02c0459001c03110b42054847c1c6c07000310302036480c1d003015030041c0c1d1201d12a40d210301c001d10005016090076518120140c90028045569003454220344078041444041c05041c00855803c0d551040950340580b26196982d00d03922800c91800050000c0c55440c1440024851030250349003411650f248d21303031614800d020780070412402c0381c0d0301c8259040342d00c0710058448241039104000d0201d2040c840020b05030701c099107001054610a42c40340199109005200382e070b0745441003a0017107640100140e9501c071303105118204c003414000340107041e643c1021700120403d5084418001d070007005483c2000255690030046095070010b070369030038010008101c507546407009034021401c60707a005801c2c05104d04003101402104401103 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 957211744 1250 957210494 957210521
    0x1b0c102a03150b030105150c03120403080118020322020d080d021213030c1209080616110a11010302180a030807022805010305090c031005060114070c0605030c04030501 74
    0x4040300c0041d0030620b07160001401c03007074003460f08560620000c524890711003030190340031090208100054400c20801c9490200c034a140c00d140a080c60300e0050070b0075100780101c0d02c1503411145074501e00a942e20a0f03070310841e029070000e489a40d920010595441d440e001c140e0f080f0025600c11804a61400001c05001c2c4014000503540c50a0391414401d901001d0620700f8035208000310803011942c0468590a8a604496003564240a40c0c01c10b50b481d40040c0d020400c02e000c0e4104010040040c40405c810f0035200381c07903130480c6044810b10240c0301d808149004110000d50780d5541c00d00e51295000d480a42c40c0c040454609400080c00141d6040c82e039401100c0c518400641d04085040c040e054526100d081850106840b1482c3c02803100e610310303801110304242d5140c0000380640000c100040ca90740010303081c1c9410740311a180342000b50104a415601050004d8184602d924805044030006c580000a07200100d042030000c42d030960001e030080c0381480082c00040041402131042081070400d1 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 957212994 1250 957211744 957211751
    0x2030a060e0610060c080301141215040240060504020c0d0e0114090d0f061a3f03090604080607090b07050d0806031c081b0c102a03 58
    0x260803060044030444e040300007000450141c1e540012100c0d41642d0566101c480814101103070729000c0f40083c858404000003500c280c01d103800032a03801c0703001c640c01540240e480212060300c40840200700711708202081103092070b01012103030b011002c00440c144081206004250f81359140005401d1380c008102c014229003044015031001d0340c0000c00fa1008560a0074440b6910001020700c81540c0500e0146a02500e490581c81c0c0410071103d130061541c6a00040c05c001c018402030740341241007012907015003c1c01072200120510103828008182e0080045050301021040050980d0460004c054039030315031006000c00d1926075252000341c070282021400801040c6040403000380214566406400a21000c20800c00410000b0480904440d50350070001000c0c1c80d948042840c06024001c21800d86074640650104940e010811500030292038045100308405000407080743d00c00c58215407002c2e40981040c806220702da400803900b846540001c040d511102d0282c41d22502807500400c80001d40c3c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 957214244 1250 957212994 957213001
    0x18010c02070e0a050c0a050a05040e0a020904050606090d03030b0d0b07021501051e10090f090209180f06120307151e15060e0d080c06090d030c0c030c02030a060e06 72
    0x30ba1814075440741d0b10031401e01c850f08145172680c4030351003000750040c100310300099048203c0340a00b04417001458528200d4405181a070301c000c00039001034408511a07424080416200d10b410000c0d41e00c0c0c804003c0460721807400c00d42e025001454030180b06a0880c05a0081c007010030030f1191151f00c21991038002e00390703500c103c4840000346441604018441c59552070710032645508681070340d0aa450039145044071070303105035090380c0c1d21000798460700009051010100b80f4401c55000f403e9214020ba514440300c6070000c407854083c10007103e0740e0000c00b40010008040b490020f111030110354981c801d903840c00d041c40c1c0f14002e105040040f84402d090701c601e42d088483e800002560010300c0c030b141c002c11807480655541da10990a5214060801880c411601942d98400c001c19519550014000e591000504c41140e1118000c81e00034849002c3d5081d0344114602900643c82400d06642e41c034140ba0000755000e0341c0c07414030000b0590705442414084c40004596218240c201c4816100602c2c8910713 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 957215494 1250 957214244 957214259
    0x20c1207050d0609022e03020f13030521030f1308042c09030913050702010612120e2e140d0e0f030408120706090c060e04061d060918010c0207 63
    0x4450482c5104541b03d200610525806440414002003001e140140e500c0a903605020802d0151084c081c2022400782000001c010000078400c8030910303141c0c41800d2104a0b04812007490004617000000c07007851500250f003082d8010034450311244203040c0c4c1707820b040c0ca4442e0105542140d0a10140030220043c08003100d250507000e55901401ca04003c0d498041d02e0400f16003201c40406101d000d49844602080400e030013134204034003610720221074840d083c1103810210003c1c1c5003800384102040c1584c05034251414059140c030500301f034142c429401012404080c20b00040f00c00c0b901303410850403034424107540c018040140207520b24840045860b0410707404040c1020404615485c840d801044108450100810041030b01c001302c00c015519410746080600140070305002c003c0180d401d403240400d1580e005001c405400c2c100b0745041001035200d002c0c000548107a00c1920540c91b03190f200250030303441c26024042c0d11280c044008a5120443c480742401c3d200c0b500988409078012000500c50072 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 957216744 1250 957215494 957215509
    0x619050306041401060c201003051009050903040308030a0f09080702100810052103040605030f24040c0903020312070201110304060807050c0f1903020c0f01020c1207050d060902 78
    0x600f00000c0c0c000455240072805041c006103003e004203c91075245a8007464002100301100c10b10002d010f504504401c40320003001420f04031100000d449014001140c000301c03912070180702c1c04c18000210b01e45400d540707a0216540000b416a480c41743c49808012240744a802852415441110710320386904a510420406480303007481c2a040000345810080b0b04040b00d9a00c008070f0b01c06a42e403100c601070701d10b0309400542401d60f0304909440000340025405a00600440c418201104181c00c02c2d100c241e88940c44000c0c46000b240c0c40b499842c91010b00b8501540483c02211440c01e00440c1690740b23030b002c64203001c22902000b0a4030300104401040d560010400340c150702c000000782d03181031309102003d440410301403e424104580800c42007081d140400030b40129400c0b0204460400b801c03040c40d228103800400c0d048005001e44580c0907004e0400c00f1802044040503005080a10b40d00c105100c0e041180d001042e6a41c03062020000d00380c1c961034051107a40c1d0240901241440d00f500601ca0b01 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 957217994 1250 957216744 957216761
    0x60e03060604090c0b090f040c020d170906041205160302030301061b0b0c091801030501090c091e0506040f09060605011803030507110103090b0f0f100501080a0b061905030604 77
    0x256040c8010b00c0f000601d00107080c02510300003858030f40c4800140c0041941e52454003503546e0458030340484200480c0d000101081ca644950b07480d40000c0d1030710030a02c2e190340002d9881c0c0d4015402400800e00003480841d0904800b040351a00360b041c140c003a100d60b881544802415400340c0c100000501a00c2da006040c0303e05003148205210721042d40c1d58628500ca0402400340145202c04140c6c40b91941e91920780f010510292a03d0035010358590034117600074a420001241c40155036a0005444003047c0201543c8002c3c010342c0ea100f0030780c5501c1010203400010700c1d040e07105580360f40e0b10040076647d20618a80c1800f4500000f03419040c0000504444600c100840c01000a610304000090340002141c828552005900c1042d14282d00140d0281448010050011510804202d403190f0a1168130b8441c594200101e20642c0b105000d60702040003601500c0e00180d440c10000d02d60030001c1d001807072540b902500311481c0c0b0140b6100c00100100c503100d58400540000306200d480d20b820300171840b0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 957219244 1250 957217994 957217999
    0x60201150b0913061208030603011a1c050c15090f030c10050706020403020a14100509100806032b020d030b010e130e01020309010209091f030201050c011104060e030606 74
    0x95150038941078a0280c0100304416100d122040203007000d450b07040d08520010808003000000d12a020310b49490181c100300e400c14042c2d8a4030114000d50115031344000d21240000c2c0c10302854441e596400340e41903074401025112882900300201e000d849108201c1c01c02011340842b15280d04032070080000450403c111a4440c1d4003c402e608083d503981501c840d040b900600304180d43d5941c603e040c0d0040d01465001070341c03100d4103250000701c0b030b00440585d801c0d058003101c11030444945207005807854001d201c21702c1e41108110134000b505034061001150170101c0207045071068903e000f807042885290000d0040c400c4290030000d82810f804000f44d00080206003010b01454034514002811685002c0143d40b00ea6441e84182d030300b00b02c10ba8041c51121962030000d40d928038111031042e0103540710200c0c0310f010f0404500025054003001d0740050811014034a0450f8a07491a0011122034200300710692140d507a8421910081c5000d01c000c2000384201d03101c0303110b1411400304050405c4002400b960 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 957220494 1250 957219244 957219281
    0x609150301091502250812071b0b0601120e03030c0a030908070311060c041404050c07061401061103030f0f090708011821080c0a050d020325020f030702010518060310060201 76
    0x1900b10007e841856401140301042c0c1d40d696801103c1001d40351404060a8900c144000d082c03104a540b40362143c042a01e5981c00310202018040444030703225020701d020b401c14804142c01641040c018004006240703004100d0008907142e002041d40000305c00c81c0841e08044507000011400c0c4001c580c09041c101070700e81414505901068011140380e400d600c101c1d902c80004c2c80584582066401a58010b40c041141400c20311208804142c20b014030008154200341c2c3c1403a80000100f224070444101c0c00d221007540343c00940307580108000c0c0030078001c0d01808074003141d0f90100344074403010b0f60050070320000c1921144c02c03c0007a0100d0f1021284100304070403005c19645401c104000d403c4050100c41a03034410008908a5040c095a40031007016130000091080707040d0f8128803070303600507804071400500014114003a6603c40414500c01e9003908280100c0e4095030041000e0410700542005801115220200080c503e600450b11243c680c280000e007031007d941e0920461400103000760015 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 957221744 1250 957220494 957220567
    0x603060f0609070516050d09050a030c05090a0b030312010e060402031e0601020319120b030c0a14030c0405071107050307050109090f0608010e07031a0609150301091502 74
    0x40100d100c000d003054000e44424011a2005115100301c0d00c441500070540c0e02e88058a1034265122032980791808001060590003103580d00c1d00e9400c1c5000c6a900400c6900681e280c08140003d03d040140103945c2180e4800800ba6180c8051000f0040c4030076080205000e5810285520014040039000d80d0007980306000b0498a0741600b83d0400d444000508141040da442c040102e1075031084182580316080d641017211585078019209404c1e0110302c150a005032001a01850355403900c800401780c0c485013014040040241c042c90240441e04080c05031182c1c1c10070140802d0170b8810981e1036400240d00721110703817500030060040c40040c007000c5003d046102c0c41c04000034044242c0c0e0041c1148682c3d81c906d50940425182d00c804014214003009000001140c02c41c076845003418402540c50200e20070074000045142c055041c1301c0d1301d0041240e00e2a855424905014244409141c0e0b01990307121035940110f80e001c954641011030001c405a6a02e003449412801542502d109410340000c10152 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 957222994 1250 957221744 957221761
    0x803030a050a152706170606150a0f02070504090c1d040803190b0a0305150106021504061a0904060605131a0d0c030c060503040b060d1a070e04050108030d05060306 72
    0x5100441320480c07500c5007403101036012030100d50046001521614030300980002c400d940052a51000944041541e0183d42d5a13400e02080d20401019401d030a20108028420140202180c0f805e41c030341072044505464991000c18211b6051107400d560100524400704140180c0c3c0c00806003a200003503140308141081d07a1030b801c00e03000c040e0000b520715490540b50800c02e07545034401d01e10503200030441102c242d0741e820a40e86503c4070100d4a08146088800840d14034000030380c580040b5016164117003290780e40e031140c000411044807403c0f016884c005200c1c49070741e6008000c6000b203005010004038940342404109154900c154000d2160781407022491103040c004114a050586c161400840800b01d468000344031202600001c249034603414001c02c106038880040c51041d8800d00290b00c140c1c9600c2c0402a000c0d059400c0140104040030294032403d101e5413001e81c201c402800d100000e800c00e41c000409582c0241c00440450713001240411072070606008a980181c03040c0d02520039410110350 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 957224244 1250 957222994 957223031
    0x2a031902072c0f06061621080f19020705030316030f090f2009010303020303060103230a0f020f0f090411091c030c12020a0209091911030f0102040803030a050a 70
    0x2002494002520000d060f90310390344100c0f0943c41c0314086d030190200d040e1804c2086c1c211182003014005d2000281d082d090340c02881094040c1c0c10500d00003002d40c3d05d0050b0fa14000800200341000e80341c00b401000005601000558003902c07066180e42c07031601c600e900003012965031481001032075090510050101d090b28003c2440c0b146c00003000031002c1100d2600c2401c03500d034000640c0c0c111145d400004141035020024600850090b607061081001d00b04449800030982135140700c030f82400a01142100110341e0004221021003a40541051611030812016410040c6410b0105100261101d01481c0500c65902002844603a040c200410180403480c60602010201d85510341d2032404030074540240001200c0c1d543c80501c554443c565008000d445507045842240103215000c080350300c88901040a5094151000301c1048000150711a54135030300614a800f60140030b0f48030210000f02080c002032000c2e0001c0001140d680c140300220030b00b02c620050401c00d07018544020b00e060b911007100d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 957225494 1250 957224244 957224251
    0x16090506121c0c06113004150507030b04051302090901060e24060406030f0c0f020c0103090c12030f140405030d050d0b120c010f03022a031902072c 65
    0xc0e1500300a890381c54040e0041002460b95245020f020662150480210341d40201c0729861860a586d82030703d1160300c2e1040203007510014420001c41c0c00202910a10343e020700d900c09840d281c08920f003580c00d00803804a44045d03c01010751031003c4901704c19810550741c45908240b00000801c0f0700d41c5440c25070304502d240500ba040000c24210650302c0c001140304d184d000345030380c0102003e61341c0355140d00190061200e10780411005017814002001140194480060496180c014002c2ca0410400441c020325262004460f0b01c070605802241c50344c0b20b2503410310624803c1c2c0b1200054842050098018440c1204140c40610100030900040e28041400c5401070b51301d06100380c8408000c1c01000c00b030010303c0700d03554000c220030705189145200003440c62031845086e03d44001d4512000004c8069200b616000182c0b03c0d45441000e41e840d105000b651411a240e074152402e03c00704e00e041c0301125816118510050303000070024041920b0017503112081c010507601d4400c0b04031101d1243d040708040103 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 957226744 1250 957225494 957225497
    0x1506070305040902030906060109080316080f0f0415020601050d0503070b0414010c0320040b090d0503090d050312010501110607030c1806091404050f0f060316090506121c 75
    0x204494041501400944000c0c010040c001e40d103e01d030410303d065480b00205e03a01ea0004128120000c0c40d20000720483c1c0810003682641c60000358540c86800325540b180a0b000c062a03001c024900d1701c01c04880c00340c009003040000c482d007800c0001100074a0008180c000d203125400030f001010000f14000708441c4c0c0264042078071003099482e424070400c03419090036649015420024910001c65156004000e001c01d0851400b40500011100d80c1050196020b804440403081201548170300d80380c03007a5109580304504691400803100040307107a051100e401220b60382d00200b88117200824040140e07024000a1a1031503e0105d010342044d40c5c0d06025082c03505056480e0140c0340018440c5030208215110740c010b4590103a9102c10003000075415100304507401790000d0a602051401d8060240241c0440100300525211090342c03441044003d051280d0600c105043d5881d80903260b81030100130300c500540014580350410500541607164900302d0542c0d00103030f40c42e200503000f1807190800740505 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 957227994 1250 957226744 957226747
    0x3030b010201090f080909010f050d0807081908040606091107061a060408070608150312030a15090c030c2a02120a0b09070b040303080105010f17040b06010212031506 73
    0x8800060380103003d0404040c02450310380240c0c4050005120082180031415240101d8581e40c0c0c01108017500d015004040d8840c04021112020681d56005492801d010741c4e181e92503d07043d00d00102c4030400143c10303e008140300008002c1440524400c4d07500400c0e02c0c00341030100e411000d05140c458451b0b850300415541e41d91a0200c290154805011140c5c42c0191080782e813542c235004059540c0b081d03440b500780000c15100014800c40140c200596880308040d009001050201000d032010f504010088183c1a030340302d200e220701c0f01940b00c4035802421400000140450034480080584100c03007d12428042c48a8503124146500011954000c083c1190f0710306090a07480050301e1103600144040d150710030061b440e014050309402d094080d1040e0f1084075031056840c1c40c0009207000324413015010644a200411055003e1002070a030541d6900d801c603240b000d4a03500190080090f0307025990b56400001b00100355030104240821901511590b1b0704510f41030210380001840041c02d00d006110 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 957229244 1250 957227994 957228011
    0xa2103110a061d010c1107050907020f03030a02040f0b090901030809030111070b071e1d0d05010914010c09080c0d0f050706230408030912031b071419030303 69
    0x2018041c8401d2554040018080d40f901405036028054075560302c0000d95181417000e00b40780380502960b815504500d0007415240e8038140400c408108010200c00a502800c0450412a04144000e40c464101e9040042c0c94509040a2410300c1c0e2980d000303050000400c00c005d441e2075807102e0031141100d601602e03140d41d07101800003081c050800e2225443c0c0211000c50258104818202418400d440f1030707440c0040022050750741034158500c1c50b03450000c282500d4100e0f440b0506007540d0301c024640500302404543c0349075100c90840301c5524080e1044060840185620002030040c00008403640c17800605090802203126140c82c0f407083c40d00d1082582c0303c601c0c01040f103500c505564241d040800d0b0707501540c1e20b9030702402e5500344601900c02000e613102c08001d0340c003d410964065920002c0150308001c5040d0510001d0500070320021102d00c4180800369041b108103c207244c4c118402000751050f0751400600e24000803030070008030702ca101030840c500c3e514100380c2c044404607505031070085440ca8 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 957230494 1250 957229244 957229277
    0x3090c0d08040918020405060409030f0c060b0603041203060609050102030d180b131406040c03020405060a08012903190314070204091208070f1e0215070804020a2103 73
    0x201d540d101c502042d0518101c21321000140d0301001641c0c2c000d4605000698400301004100c603241e1380000d012035030065910040302d1040000040d928419000041c1310004500001d607190001c540441e403030034102c0c0c00706106a50601802d00107202e9800c05540d56400c00001035102d000d001c884076440c0350350310092a2001004807004100c80d402081044280c00c14090300e025140341d0103800c1c0c480400d41502010403d00c00900c0500c642d4110007400c241e5421542000040c2c08081c00041d80124082c070f0100d00104280709a89480702d03801c0140c4040864030054110307101d030b00500c85200723402c0324a440c2451a00c03a9122404944e061621894411500714000024090303203401075042482d04030030808109600440100389010394a4416403541d804030201c2c0d440740e041300c42c040003a40302036803050450700d100341d040c043c500b490050743c0c17600582c501c8141480c0001ca4406001800450a000175400c01d42c42400141c4000440481c070740034501400c003c10644900b0040c01c2050340400600c036503 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 957231744 1250 957230494 957230497
    0x50d0e070f0609030b0c04050108041121063103050a0c140c090112020d080306011704050607080c19081503010e010c080a060608061c0b0906100b03090c0d08 69
    0x10652051010070082d115100101118414002100d1484043d000309045107040d0701510f0807500142e41d172a10683c0d51342c1e00c12550452070443c898020002031b0f80c5072550302d402c07040140b4884141000384014900300c0b451074000e168544454408501140a44030800c1204003034000d416094204650381c0c3d1350039030040f20901c04412000d80340d2000c01640c0e840124001c100442d003690111120b2000d641c0742d1541804030092204000d41c0309207202d20107000580c605014641c08070050501204101341e40c0c52a0580f824100c50840e10747d004001004103080e00108c85680040d0030000701030070004015212400721900d5040d66080c0800321b80003c11441c1415040303001000c001d00240302421640c0481400380c54004044070104420800080181c6042c0c45104102c4a5a0303a0302d103100d4954200740680e50102c0e19401c0c9424400509002c04078034000559070040a1100091080389042c8480e40e001e404590403c400c100010414000010302c00240902402811a40c03851502260318155120307 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 957232994 1250 957231744 957231749
    0x40c0506040e0406050c0322030e15040302030f0303060a03032a1b2c04020d050102041502010b04090b06220f02040f0803030f1803070b010b0912010507050d0e07 71
    0x30100c0001c0215880b541088224016403080105100c0e80d02d4001c4000058001200c01414110700320a00003007040e40c84905260b842d0007410700343c013085000408508029060140304521800014041007181000c00000344445e085001075030031402c200c400150b42c520103100c00740030030040c4120007106a0910000083c0c071041e81090561a160350b142003004203807410703051a5880c51402c000660201c80c0e03000101c812808c0b50f01078040380c0b10300544182041c8043c0007a40c020706000c0c1c44800066091001b80060110034000480760030500c0340c02402e41d1440c9540c00d008a00300880d00002801c282c1229170010350440d4813001c652803040d801c00020750700f40e14860616007800317002e0840207281c0c0e001f401660048038150321925240c503217a90392440261a0001846407840c001441080041c01c803a41c240f0002090340d02d07181064131031000d02d050031380203044240d00002d0307035001a181c17401c111070780148074030000e02245c600781070050105d00982040c000c250f0744840e000300d03861000b40000e002 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 957234244 1250 957232994 957232999
    0x907030e01050a05070e01180b1806071a0a0204081209130f051e011a210c04060305220b070e030f0312090708070501030f0605100c0203011a030a0b040c05 68
    0x810f00e4080a00d20280c00d041e21003101080710041002d800794403c2100b000c0d000441c0d00511009031a05c0b10f0020036500155603516503000c920004120b076610f02000f0100c0d14000c52084202000b00d450562400c00302038080703542280304004c20400b401c0041100c4e4600c0460300c15841e00d61400402042ca281900c010303064480f0f180c241100590f208540c001801000d14460f100d11014085144042526007070003007041040d0b41485180403000c22000411050a815035152806035400c0300344040d034081500e002c1c0d00f40310013050600c0500e80c54400c0d5640560b03640386002c1c3d2010b403e020920350040140d0050039000c0030380001341843d030045050709104240034080f107031030444007410725440e604551070450840a0b800003160340038000050342c03415200444d010380961854040150b0080c0010101000555114400040c49554403413071010b20310a281c588054030b21007841010308503001c4800e440a00354295202030041d0f2400100e01c0300140d800032100b00991583c2c01c1c401d0340800c2c550300659 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 957235494 1250 957234244 957234251
    0xb16020d11090a090b06030d050301090b0604030b04121409010c0308060105040f170c0d020117040f0c0b031902030115030207060b03060c0c0f07032a0f14150301030b0103020907030e01 81
    0x65815410780c8050032185c01383d41758070071607140c2008168581000c2000080002d60500c014080c80c9100d90001380d1a0320020036403403800e50b0703035031300d440550100b16400d881e1000025140684140c0080395469250002c01c94103142c0b22240c00060306402449201408000c000300000c0c11a034024070071035000e40000044401101d075150402564801c64041e941d00e40d00412040d4540350501c03a4814240550503141c0b42940140e40c2e401c085220b40040c810342e2400c05090450700440c00d50100200074000408503159a4a409070641102e0041c501c1180001c038410001006241c00e04107001d803403d00e06140240c2d42d589241801005411032240055040c081e09051040d0405400003d024004105050314414040c1e01039103521028a4071010b444920703050100701480c082d0f0300700070894011640701d11840b540c4481122040da5050341081480142d2480701c00342528003041c2010481c1c044020f0b032881c640c11661608510780040c0710003030054040101147d40c1e0b50203500400700b40c100250080 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 957236744 1250 957235494 957235501
    0x72c100803130306061a03130f0f0308090d170109020a1101151d04020a1202010201020d0c05130e010830030411090105040b1509010908030f0408070b16020d1109 71
    0x241d0840080f03200444400d840c200000600c1c454095480a4078034103010421f00750b0f5900b603c416202d40d080c0608880c014043c08405001030500c00481003100e00a039a0a051454614110307880d10f500201520144601503000c65410780324000a41d065410403c00561107034440b2405850350301d0034040843c5154204050908010000026101210306c0c641c59008000003401d020b042c0c02000340c070040d4000307010750414030400e1f00907803040e07214901c1840014604045010260203c50030b603003d03100000d000180c1401ca50041e40c51900181c850b10082c0c803165450039156507603a030342d040304090580c584401d0052140200d0704e5004200701c2901601079582c0f4207072030003c08000d402e03406c0c10702c03820b440000030610781490302c81c906007000040e08542c217041551071514040c2e00042c440c3c504004006101044810b400c1c00900258603004841d9034542c0c0c1001d94071820030342c0c0c642020140800600c4400451420561100b445a406032030407000c640041c144a203d241001007095084040309050 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 957237994 1250 957236744 957236767
    0x30d150e0a0b100f0e0d080904050c0c0601031101090e10091505030c15121303021009050d0c021215160f02030717390d05040306180b070f02072c100803 67
    0x24844000d00315810449942d40052a41ca5030007013144033300c4154408001400040c1048040c414022414102103041d65600c0d0101a42035000f02c40312007100d070440714200a00da801d40200d80041c01c900c210801b10b241080c001c00c0d41d801c2808015441080b007111141e02c0300340600c04a8400c80078040001c1110304d450440003540180d0208c041f001881101013110040219204108201e0703440001390503200800e14013190788840030030059a000301ca405089400c2c0307100b0030503900980d00f06c218440441c602031407130864240056400300288008100c80d441030382c0d404002c0303c01c0780d070340318950010705480303a13003031004600806500002038540c480180661a02c040c0b00907104811402c079142441c1b00000b03125071074895009008001ca04184000c1c0000b81c015000342048403501088000303500c003039440e584503004050341c40d2004565051100d080d20f40d03040c8a2100580a1004031202c50103803d00381c1024481c2c00b200e07031200c005007500400d44245015a401c030080c5030420880b82c0b02d4800c10700 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 957239244 1250 957237994 957237997
    0x120f0a0c111c170322050c0405130b0901060303020c120304050a0e061e150a02010905010609051801060605030a1d0f031812100905030d150e0a0b100f0e0d08 69
    0x14142da0201c00f80d014003050425401c1164882c40c08481013200b82c5200c1c89801100e003a92010807506070003250700001403501c0d24441d951096800d40803000c1e0542003410810320308035014050802d241d04009003800400e400081911050300183d950301140b00010740401d00f14082c6800840d40b0a10a100c00200001031104003401180102c421002d50200c0b84500b8031040024542c5c1a04a52441000c00d0340420301c2c00a0007907141e040c00040740c0005241e0301c4070b08640c510341050700b08950b80c1051290084074540e83c04c2c1c0341c0b22039400800074a400d1842c09482808000e10080741261100c03204030904807002ca101d16540502000c0355052181e00b9255512500045580c03111802c104030034449514100c5294000c08581e280940401a20b8095010280804c01401e40306480100115002c084003807061451145c01c58140b42c0702103050180540b281200502210081030824071408081d644442d0101041003c500300206000c4801200359a0310a4a10b02194800112800e50040c400f1080 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 957240494 1250 957239244 957239299
    0x30b0402150a1e0804050606060309071a0a030e060c25122c010c02060a03021c0608070f05060d1a18150a06020a030509031606030c02120f0a0c11 64
    0x11403111011900f10000c0300e100d003080314040d002d68440c1021034014101140155040000181680c28264480d100c0e9101504c240160780c090007000207481e421039034103100d003080004a03200917004600307051180d220580984140c42c14080021655891048006010407507075079400404032006142d4840060030540400b5940c1d4040e285005403490341e060012504195a24140c5401554034207a40a205a27904030240f25030038142d0810aa1032a0325140b11600104407400602180c49801d010f078650510303070580e20003034420581c0e0b40180311035602c083c2610f5503514202c200199403c2030b010b05106404207018101d40200c0e1a0140580a449418200b8848c0007201c201000848900c028003590000c01d104d10030040e04815059000207200340010700a407a0014201c400c05048070400423b0348600b40d02c80000711381d844410030103245c0c0500030070072030301603c0784c0050034034110145010181c4951a016000c000280c0d00784000c01100d070154548044028020002e0500c4030560040d041c8c0320341 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 957241744 1250 957240494 957240527
    0xf070c150f0e190b09011808030415050c041e05060f04080f0703030203190311041206050f01051e010504030f0f03080f250c121e1701030b0402150a 65
    0x24036401c04800001030032203550914040841810300030f82d16810140780001c2d01041055407506140444000403040348252240547c40842e6241030620381022901d03903e030382d041c0456003030904001030b028408090300d04607109000140c2801052280040280e20550406540002d02181d44400008010007600a0314142000c68008419042004d96a900b09100080c0140c1c4104504400b52012901d40f1001d441a4200030945090030482902a504141c0101542401001883d814407400b070050580298880c0f100c01150350600c40030640e01404c0c0c607000c0c103d03241401c0f0400c6050b4406d00450b0001e542010500c0343c120741a03d40858141595071059001404401c0030800c485d152031a982d01820380900000744590a1151340a144041e0030f0200e810b0190a040001c08600c062520301180d500580e20084c43c1c040707045640c1c8001a14a804008004c0c2011a3b5100c1c040f4041060b81529002045004503903103520006529802d81044011b2552000c14407084007074200c104501c40c007080 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 957242994 1250 957241744 957241751
    0xa02040504060f051c02130c020c0a050d11012a050c121902041a0916090f0621020f0d050f01091a1011030c330f070c150f 54
    0x11180c10548040b1140684d961001c02c9000c141c030288803c0503240081031000d400c1480c9110329500e10402c1b980c3c0800e050005d44c00002185e4030610386450400042c003400c9540c0368107180191520b070110018030740d049052203249480085034808408540c05000484900c08400c03c0d02441d00540342d811503180540034030b818400e00030100350042101c00d1521204103d55003046801e03020040545681288030306003144048040480d034a0341d48081c0c0c415800c159142100400d400c00040181201354070440412040c01e00c188111383d40100f6080050784101e14107405511081e012a009204050303004a501ca0001a8001d1040b03041e04032501c106c040c1280d500031a85d1360303607140e003c2e280e481c6440c1d08aa02890362511503460321245601c01c02846103407130529107041c0c0c5031035861039008444500040d030280d801041105004841202e05140586c0c00e03254801500783c04580a81006d00740c0104619007a0000b0a103510034607403046a01d800c621950400c07005042d046000749404850000c101d400c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 957244244 1250 957242994 957242999
    0x6090e0f0f06060d06091e062c120304050f06011d060108061005030735060609030d0f11100209040f110913060812210108060c030901020c01050a0204050406 69
    0x301088003840398102034040409070303030183d503240002c01030306c50b003290030146405130103401980c54181c201445101d10000284104540c00c0302d010f03000070710101e140000100c003c00304404400b045081c01e040070f8080c0182c5a868601e002804c00e0b000f0300e840006032140b203000003100c680c0c07003008006071b4000402108042d01d407000111000e81040380c0c503e40100003844000902c5110740b006645c01192440c10501a07010b800060707420088004404440300440700c440d050b6000007c081c1a0001d904403446498080c3c0040444d44500100515400f0b00422104000185025800c89542c0400e04002d8440203038030700c903081000b50080300d050b44c003aa1802e9a9580303441c07138520078000078414504030203007400c070001304000c00c0d03071000c1400792181600c9441c0094040c0080010503582603100701030a40311901883c0d210241340d44e000e41d64000c80b0701c20004021641010442c039802c240076141c195a65500c81004502a10542c07014030090362a050800007101001d501510a56808a81c00d10840f035 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 957245494 1250 957244244 957244273
    0xc19031b022d2701150302120a0609290913142409070315060f03060203010603180c0b0a03020906030f07090603020a08060906040b0904060c080a0e0c0f0406090e0f 72
    0x54a800e07030b03a643c40d544480148500b8000303035002c0038980c009140152500460071110ba0040406a4003582c01d252a00c205010b550024000c603100709440542c0d21003544910640490003034106c0350060701905203180803070310601d10300f404400429000881c0741404038407171581c1c548c0c071034a004a40a200c030180c000c148140c2615100240100d801500a00340c2900710b45540950034045000000010303601d0380c4c0000c0d4181c039609040b0045000f654016120342c94500080d050f11100825100e003820003248050024900750300410035103046a02c025141c401c00d040940091249540060303000c4404010403100144011096200d0b0b20b240d500d4001141d61004140d040c0c0c001c0c44006000705213030310002421418400c0c2c0340341d845000104041000c6840310003007035680c502994191165a1504060b884440e042240f29801000a090070000c61800c6403443d511214008031341c901ca4a01d1825025a55541da0803a001620003418208074100c1801590b40e580c07015108101414000c1d4815071a40c0c4 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 957246744 1250 957245494 957245539
    0xb030d05180108160e121501030512040b0a030902030106050a08011b030e03070303111315030c050405010c02010513050913050c0406080a03140d050106050c19031b022d 74
    0x760b52076250011081030501d0145c0d03d8500403403e0742d8011520004105901104210f0805008161380801d030b525415810803500341640c96940e5003074000d00b04810048841208115041406149400600c01d01203100090240c070300c950001e075004241120210b1000c1c01913000700d00034070198410280d0002022021741c2900c0201d64220a15001880800082030180d0090000350082d6031005207003000391036902194605507007004503540b9003031070140266605841410394041141c2001401d081c50303e00000c20803411701d07400078108030001c036201c903a0403000984c03100500307c010070038004d61130645169541c140008030295220701c21070030354003880e0410340f0134202a90501d42c09003074400041e480c15103440040506c1020400d608204031002003000d440703254040c1805d0b070381d1543e9039800030300810315024000603603503501e12500c945140002d420140c00700a17406480b1201c00c584078a070000844003003030302001d4a202d07507800a8000840200d000840e405103070440e404000c0c03040c00c56102008 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 957247994 1250 957246744 957246751
    0x920010201061406070201030906050a020406020d0207050904060e0a0f05031309060b032d04050106181407120e0703060603020a0b070803010608060a1d07030606020d0e04020d0b030d05180108 84
    0x3141c07076050f40509007026801000802c2c010f05010400382a5079035600115007085604010383c1381c0c0131074240710f6182d06100c2c4019120051006000450801002618031103000c1c00061800740e840f044030301e0f59842400b00e074280b00d800480c07052a480060900e107807241d221300e2180c6044c1159080100f00c074103881c0325160943e120b4442581c2140c4d28044c85070881601c00c0c0c1403503006030071456244080070514003c03500c110320074800441c00600c0d00e1006641140016940b01885c0d003004000e404c00b18038090226403201141c9007405030000c1400c40c1ca0003d00d007050f01d1384203c1c092008042b00388040c541001c81140d200b91034800762550346629440e41130042280051146000b0401001242d200e07000c4c0030b42001c0005c0144130900c3d13603006101d894640e0628580343c1c10840c4010040075075007620459009044170300203445525020b00c4010441c3c6849100076100755400705640b034141c0364980c09141980d2014003110b100300e500b1403014000341c00040d0920031100c5446604501548280c064901 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 957249244 1250 957247994 957248009
    0x306060507060b0411031003110603041e080d0908131a04030813051f020f07080a080d0906020a08101409010b030a3209010509060f0702010609092001020106 69
    0x2001c4240c1d55200241c10007030034042d8000d0300e4402039071486088400540c0200091031a1800581c42c61030100015410140d61910500301401000080b6004001305041c420040111440380f050368a042000e0740252503048030040d2806001c0c400f0064141c0041c40010b9a41c404001003940d1140142c035601c0494001e0300c1c0300c510a0000b0000960b940c030181c01d0dc00050401020f400c1e40301da000c2455010110340d0304030148840030340d04a02c9501444500300340c0da20003000d400c0303403400c140319070341d0356410198000c2a142c5c0c001340040300f401d240e901ca02801d83d4044019980c454040000400c003500940b40303034081c0540404000784c14440d106000d55104000340c08921160700e03110200101e81c1000300400c00007919243c1441d03a05022101c004000d0504020490181951041d02003800721300800f1010b41e43e2400c01400083c160010f001a40240c1180340d0052665804000300d014129036072202a840f802c1c076120f10200003155411203480c0105c0d8010f06200352110004a00380c0c0c40621483c02c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 957250494 1250 957249244 957249247
    0x201020c0d0c061107080a210e031b060d05040c06090801150504020a05160c090f0e03030105041e110307080a0b0d02011107030f0c080d090303020d08180f061603060605 74
    0x400300c4d014410100e0841d100f10207660f403442d50f4007102400c20b8842c120031508140c0103121812075a07241440001140e040d8581040d0030031050f070100e5602e4000f00f03408001c40429080041c3c040d42d900c011145241c88801d000c0c00541040e1402c0a0100e24500403500030407690000865007400501c500f241d4005168041d0074128a4901031000070760100340d6010400004214868900904070360800500b44140f074200c0a991820400c00201c400c2d01c400c100002741003c40c401d101c4d00c03002055070706440084400080d00e0340350124500d802d80c900c818002c851070034496058071041b40751015600c2000c9a403a1052075507624250038003100d07480c55146601079030880c4c4038405544204070000c49001500b049400150312078442d0b885000400804840c2c4140f46801030003440400c1c803c01e000c07461103041c11044c060541e074010391a0720b03103800d81e401040500c100007003240b034500d0119040c060ba4802982d0080c152000415207400c0700710b4000883d81460402d096190b40305c2e22036501100c002c1d80e54603 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 957251744 1250 957250494 957250499
    0x30828080a1a030604050d0e0402090306011e05030f01060914160e01090b0c06011a120103110d080309100e0708072310020a030305010e0f0105090426070201020c0d0c 73
    0x12008002010710200b10000c503621002c403d0720104400c0340154000c1009166400c0480c03802440500317148000d50140d4014044043c09840004d0b00605440100f041551402000d06030301000c0c4e0400d40c0f207540d2511802c0f000c41211241988150151a0100d03820b115454004e06002035404056030f0000503075001d50585401180b042c2d00b490506039051401d0701c205650b031082031906800850407000703030b900214010032800c0d51150419100c1598a1019414603140200041440703e05100c00b4001d0610301506800a07503031b095200c801181c1c00090a5164140a0b18035aa00c0401901140e82c0ca460305a43c0d41c100c803800290303c000c0311f02000c01010140d0400c146610b405000c0c00006c60300c107000060500d203680c0c5401c124034561007262700500940030141402001d80d541a8080c1c000b006060041c40107402103c8080c03810340f1000e44a0f00d000c1c4c0c40394600b1022580c216842c000c12411559560410f1640c0c01c40201003190003682100d40346108502000103102003480024108403255104 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 957252994 1250 957251744 957251761
    0x10030f080a200d17040302030a0f090503030d051e01080d1b050615150a0815030f06010b09040b0402180405040309030c2606090d05030c04030c03082808 67
    0x8011180072490121650000d03201c0a03501e0401c2c040b05440a600660708641c81d140c3c3c407880d0325881040741001d01e403da0400b030714003a44038459003241e0f02c02c005200f214000f04030f0148021100800e0b0140843e0b5179894405c440380c00500c810354050301142c02c03d000e81e890940114070b115041e12031220103403040184d041002e039a900300180c240c00c04141d01039000c1010031018040300b44640701c0c400c00c01801d09417810030400401032084a4181d41c4000707108012030298440c5e00302c3d51007022000d0020b42c840300e040000e40f5126a40c0700d8840700384500c00000c111581008083c0c01140c1c0c0c181c41c01c0c80144440700800c4103034012040c50318800d8108050100a40c0351582000b9041030203406c0861101c0d89944428000c4903440d0012031107011741d401003d0101c14411010120140d501c00500650f0902803403850304d17400201100c804000007c030100e40400a2941104d004503031155040000540e00c0c0740c6081180c02801c81812050b10045000b500145d0058181c0c121045940da8020301c1e07640c0f40302 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 957254244 1250 957252994 957252997
    0xf06081e01150c1704263d0609063f0503030108060601081302010509010804112115040b0c13090903020a05010509030c030703080c250302010510030f08 67
    0x40c01420800c0d000043c101250310401c03d80001d442021080360717101d081041c2207455402010340c111040c1d40810209114590202c2c00c010129007415400f14001026451410b4002c0e00c44000c1e01802032540081317050014643c000811100005401d0100944d61154002c038405401c1c0c03640441501c45a00d02c80038a10302100c0208681d07126500301a94505464451658000360805101d0b60b11090034481e403580c22100321648042c405050b882d00350b166a0000780140102007815060110785000318040202d1203c9480304030714064100950039803803621040c03c07000b00340401d80b01401146520145003001100d100d12544e00302500107542d07210001c0b0107801d540310500030f0500b84100300000c150305100b8080c0252840c002c0d0b00900302e0700b5613414110700f1514041c01541e0564010002d0811110011090314207840d00f41c1810135080c0d0f03c01c061180a40b02c2c180c1804040030402d44a0700c9a02d098500101e00740d80258001c200c01d59074070044643e001c0040c000038040c2688482c0f4103000410b540c0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 957255494 1250 957254244 957254279
    0x910091a070e01021c0504380307110c0105121005091f090528020903070e16030c0e1c0f03180602070f05040e0307020a03120225060309020303130f06081e01 69
    0x202c0c100b40305c4018030011046007409400b48c11542c0001051161144d480500b42c0c1010801d03034007800c080b100c0640040d01c1485402401c44001c45404001006010030140c402d00400000e4403001b450720380501582d1041060200100c1050725085010500ca446841514403c52034441c2e412801c8820108004c80038030f501440704c0516800f081440002d440601c6140700400001d4014403050030444400007230040c10780710590806241a281d008180d5002c0e55540b2017540646a65002c0c072600043e40d031543d40c004001400040754041490b042561001191001c02d00521008903255210001242c13926030074492000901c28458091000349443d40c480042030390118110f13031602a2039408207510422a40c411345502d5009884100d43c00d40500c2003864822a100c125086080f070344c5000d0140f1f208034000d11080541e00c440d03c10440d202002100c002800501c0045441542c0e12115441240507020307500c00a102400850f0342d0441e0002101c00d10580401401183d07801c4c1001004100c2245 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 957256744 1250 957255494 957255539
    0x8030402030304150c0c090c1d030109080c030702090105011e050a05121302040c0f0c0b0a020c0f03030a1407020d0f0e0d0f1101080910091a070e01021c0504 69
    0x100b00003e2021605803420281c1402601d45d003001072040e06120801101701c0d8171440380a030424407441c20b440d40c000840c056644140e01c00c3c0c40b91034039000120b070042845450040101e000054440c1c0f00c854004090100288226025000391b030f00d034001103450501c0300404080480e12180d0416035030b8003510161220f5000362410900380150342000c00b81c4038500355100e08074201014180001e50900f4000e0750310103a244e0070401015003507100010000d55010102411004410004c58034040031501158110300303403901143c0640807004201c988070340c42501c406030440c1c0751000a501200c0400030451041e01150050020300418841c10740700c0952603c0600b0401444407103034281641d40c032200b051020b00880781014804920300d080407010050015850501200400300f0005000014000060401401c030100d0780407011b1034241c010213180342003186546002d404100c4820351000d03e244408030240e003200c0000310054070190b60040e0340600600040c1c41040148000303003034842d46086881d40c0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 957257994 1250 957256744 957256747
    0x8040308070c12080601030608030c1b0d082a010b060f031005060c01060f0819080a260a0b04090320030f0a0e03210a0819060314010c1b080304020303 66
    0x142c0c1d1407443d000c400198007004950300000707100d559641f40c840c00c1c015004231380c015403501281429a0f60b560752000b504110201d0304840d200300907264107100810f030303503803000410303444e40280b42d00200441e88404c161440c4d000c641d40f5008a03140d050040c80d50b1040b014006524108403a05508240da200a140c40d258002011000034584ca40c0300040451003982c2d00000307221410603803550008001707680f000344558890906100030080c850054100950b20030782d030301d41d10b590810045d0783c0f1201640301d08000c0314618604542c80840039000d14403c03480000700b004a080d28504000c03c682c020b0ac8040e00054041d6040c00071131500f408103c076905403010031a81082c800050314481544403003600d03000564210050300b0541020020f41015641e0340b03502c0f00c0c5504959070104200c1c0202000003040116510108200010003044007020001c03000017442880d440f03041c6040c00c110f03488a40b0101c0e610300304142c6543d503c80c5001c00301d10503c94050100d0312600380c8541c20a078001a0042e030f0716020 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 957259244 1250 957257994 957258017
    0x120a0503060d061e02031617010501030203040302120412020a0b0715110412111009151404031b0810140406090809030615010f05030c1b010b12012009010804030807 72
    0x4034440040070701e41303405801594a2505044c41030445280c45034000038031404014645140555000303150550f2001e2070011f0b206c0c1d03114102249048a089491070b1849800180131444240344007003041140c0c021748094410755034560081d8040d20884102a00b0b41c803003464401000e00f005e42002c1da9542080c0c41c2d25080c41d4882c424828171030203200c02210f04001d83d008400c0f41d424940c4e408080b002031400c01c032211a1038a004090103c1c180e800080030000d007801455000244072090320080e40c0c0041c2e070880e1640303400d210041c40c14514020890b85100d0b80050144185150080c6480c0510440902c02940c4540d13803060062304003c00111086401442580700e80c0e20100100d0b846603d14100b0b0038002000080003502c901c0102e403d901c100907082040101040100d03003260700120060310101215904d0030310707081c010701c83c0b00c054075801a0f8804680d080c0810540001250a0b01046408611030880e26415081d206510559000c64034440025010038010300410390301180c94100b8240119 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 957260494 1250 957259244 957259271
    0x90c050312180121020c0a170d0605030f0a02062a0304060807020604021c0c05030607110c0612070f050f0f210636070c05120a0503060d06 61
    0x12a14560078028000400c001e14421100b8214a030400070078200700020609820155218500042c0b0804000c0c0c3c00007500aa929020071965624541040c400005002e101c000c0b20160307480b400041e880740342026000f003440c5c80c011400c0f050400301c4030001d10040140381c0c24012581c000e900440031002d03000c1e80202c9a8042d00d0543c8840c0c141a50280d540c070703420311401801c200d102504000455108500304070040c0ca0754820845182d944c01d0f42064800c100b40b0f407a42c0d19000e07903008a074050080e6018403400c2c5030084850103000c44030f04150303541d051100050110328000d2482900d01610440301140c101802000083c0b1410010300d442441d044c15500850130651100400074a6502c0c005507207106801890b242c2c41d641243c0442580d03240c21704100040e00800c3c0202e41d50500c0883d05500d0208800c14100c440c0e111404c490140e54074030b0140c1b4040d121a003060016a014001c5244501120040004480315000280c030f4440c2940c40d00c100b400100088584d0840f84260b44540d00050700 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 957261744 1250 957260494 957260503
    0xd0f0e040f0c08150d170910021b010206040825061815020702030c1002030d091a070c05060a020f0c1518030a090b0a03090f0c0f210303090c0503 64
    0x4048040d0100d90304038507440c010f000d03030700040c0003408010805120032165a5195440a0000d81220000000c0000c001000c0300e04c0c860b180c15203600851307000503260305a401060103034101070781d810408240c002c42c000583e15101f0464004001c02e9080080311213604004088818941d00100d42d980f181d80b079640c0d00c0c002c480d0305002800c80051442405820803e80c0e07105020042c19890066050074190f80c00701c1e40d038405422105229001ca1011441340a10170003e4a03c01020f45000b444640c4d01806c000d43c900001600210003842c0b800d001640d158029000405d00a0b03212000303201941e00c100d03212009400800c40040d08000801010b443c1000400516442001c0d00c4440c60b00350410740550f400b07290b030f5100c00307907070b6030700300b442072410058200201c8011138142c1e1203c595200501002100203241010000b0020645c2c51029814003018900200548000d0504105107584800703050010341040f030750844a0310046a48400043e119070400d6080da446103107000320450b16140000c1c00c1 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 957262994 1250 957261744 957261761
    0x8030c03150603310818220902040c0201020a050301170a0605011d160509041e0203010b0a1704020d021012060915090e070e1b070f03021e0d0f0e04 65
    0x202d0900308402640c680ca036500c0e0861207040207200e02e800035005c4e030760910303a4003403160140a1144908051040d640303c90080e0007107012500341c2c0c10106001c0300c0380708000b4002848140e000d00e1030000d07030300d13a558014403c55040101e152a01c50442e0300c0e000c800c07050300860700e10030840c80c016064040005581401114007801500d4880031043c00e030f60403e0010641c004014110a0001010b00300320184c0150445500040940d00031542841c0d0a86072140c1b1000c00c8011054240300100000d0354500c800302400101c000b95071501d01d500440c104400c803c4400b0355000e90b000348854460001890b0910182501c85128141151390481c08441d1000b116209d51100f14410780b01d814603e550b103c0845c450000e00010f08040020109407910a03540e0000c1c0d000d08044021b90170003146030b21071005941c0a0007036518074400d90b1444a4600840c007170b840507038101c1c0944160307040622040320042c8250000f107030040050641d41c418407400c40e02a034071940d51209004a082e00c004858407503002c3c0101 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 957264244 1250 957262994 957263011
    0xc03160b01030b0603120d020a0912050607080c041521050a05190e1203090f030304060b0117070c03050906212e050f01050405060d05010801051308030c03150603 71
    0x100d5600d1800d000d00038040092a0301e109400900c131007a140c074802c40540701c007401680b500580f110030320601525070001a401001d04410282116010071100003912071040b13000380e548400d0b0b915019640a4540614041c420411401c0c40c0704160072403051010b604900134a40108400d43c100c442140d04903041035075082c107120346810411540440c1101180e5184c0501c51007004014000c43c0f40c01d0b2111100305070660401c800101084801a00b040b220003c0704581050340c1d80c0e81418644600200410040d40c0e02242c261918580719820348141c0c00d2181680e5103541000010f1650300b2203c0707a00a010311a400101030001000080900c2600d0070244c9404995070480d00308201035100b203034010060010b40c8904001c89010340d0f030703d03030101030b04551064480c1e102c60303095800161024003035508516000740021812022060b0550000390480c0d907000001c00041d00d981c421031a07042d80942c0003403c22402080072941d0030300c0300c2c002550712020b400004d070b0300d196036000060340940c000d48001c076 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 957265494 1250 957264244 957264263
    0x5181305090a1103030c07120c0f061106100b07060b01111608060609090a030e01050435071508040203030415021b0a060806040c120f020406090b03100b0c0316 70
    0x14100074003400f0748105658210000d5041c081e031301d45480d070348142ea4001da82819800e15600c0040081520700c25002c2c0c038010a03203c5905455034130040c09001c00c1d079000d00b80c600c244004100e1000c05c4049460507110b001c64024035002e41070719010302070003282d80c4a034100482c11941d002070b19428031642e01580354505d00486c00d01c0c60110380c4c41c9801c8019100700c0c0f0800c050340a012410030001171920645a050819501131610301d00140c410340156404655468007100c0408400c400d0710910314a403221074200b00c14007190001d03160381e84001038050641c03a20a1041e0b02555035018480c000e0b40107100408a03440d042d26160359111210000e03501c0d80159005654804a030741000c40c0d04005050191000d0f01c48601e0440014201000941a0383c000c5a4505080150318491201000940680d9130244061482c483c0e030704000b980580716020004100c120003007041c18401d02201e0013011203102e107900340f5041c00d0f00381c4590361094840c850039110030010b0700079480503c1c01410720103024141c100d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 957266744 1250 957265494 957265513
    0x5030d050c10020f030f130204180b072c04090501020406051b061e04060b04060b190503010b0703031d0a06051509060d030e01030605060c010504030314070518130509 73
    0x552074010000c0307551010b540140500600181e0701d1040d0390b40020360605007906900d0b0b5050481c0d260580b460040d4005003403e203c0300302e40a01e50b4021000d184034242e014020343c2c0700f420440f0f1444062a9002c01021100c540550740b00507251400c1c80c0d02401000025204060b64400d801caa009130711003000f19202095032102d100740740b0440300000c0030001c043d007194504066079007618203a0200e400d100110380301c08038007403150310b074080d0720301d143c1c0900f04201c2c03152540700002540d0800c8608519400040c3c8141005620800a5a04860b5200c5086062032407030f540c2500a1309143c4101030048031130480c030035510310003042004611070181d00c1c00200d500b0070a50000740c040100c20324900406c121003e004480c1c4a00301040115509803401c0c030440150240101c0151420381d100d1a40b01ea804607030f01c20020b1045d8412800389100352820401652101d4641c01050801c8070b071900410800c0c840030307a030070440351440501040c2c001d00302c00c1c107000c9a00c010381c102c41c000e482451055204101d007 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 957267994 1250 957266744 957266767
    0x809102004090c270302010804031e0c060c2c030313230d030f2307110a06020c0307090f18111e06160203010204170a05010b010e13051005030d05 64
    0x1101828548102101c5210f980703130940304650b0100c1e220090400425100140506102c0c42039200b500741088100f42c0801c4814500410807281c05100b61515494500007407520750243c0074862400c60030036035941c6180803001d555a60a40301c200c1142d0503000801070300050b60380019045014000b40481c18806941e04212103030114068140d01d4083c4502021203004280c120f07c2080e0503400302d1411900380c0d104590409001195014250a9100e0114243c010000000e01e84840c0c3c0500303031940c1081d19603584c001c980d23134583c1e40a000d41540021000b44000200c50b040002c55010400700807441e00b504101d000c0e01c8074054038003038550804000c034082492800400c0d0408800009601d00d91a07140b4400007585071240e544080d0210030881d00050840d00e0a4065400410407480e10504000150403556110f401e0001c0445940d40390030b1040c402c030360040c0425201ca1001030f00ca8482c10100d0030000c0c00800e8080c201040d0400810303c000f849a808000c075a04000785a80c8854486134074411 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 957269244 1250 957267994 957268007
    0x2150601090b1903090506070c02121b060307050c1e01050907180b0d0b010f03020a09590c04061a0f0f040807060f0809102004090c 58
    0x420304001e62240c081107800c81c20350507116408001c4144242e060954041034000b8410800028500d0080e5030070003100c21b03000103025000074025540c2c4010004419071140d01d420307040c2460100700001c2042501141000b00240d64014036900348030746861004e80704549020f00c085103800080c0007007000e0500c003010a01901d42c00030014401020740310b08141d04c0e00c803941007030000c090407169101c03850a9030741d490392030b8000740c1a013201d041b400c19615080d8280c00b1a0307041c002070340545007001d800601c05080780b003521141d003980440550502c4001d0301420598002107035040521003500341c91035505101e030400245104995201c40d0541000c00c7e505804d151240d080184251300c2c1c039100b08440d02007a60810281520f00000a03918852000b243c1440c1c0180650b000300c4100103c0d01262800c00010104160703080d54440701da801816840403129202c08917040b00d01030b0040113013800d6001030741d044054410300d10701000c04644150303000c00b0000c5d049540400040d60f12250031040c0182c2010 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 957270494 1250 957269244 957269251
    0x130f090213020901020703020f131a03070b071a06040f0c0c030e030a0804030b18160609050409021f021c081f150f021e1006050103021303030c021f0215 67
    0x1030950803d222600041c0d1500903503c40a4011a018170000416507503400440c8040345042104000119001110102402e0700c415294080e2103000300100d9138100c088152805c04e136000da00d112180e00c402c00c500210b403c000d07084540142c0c440b0709040394074902e8080c081d039401d92503403030481d0b00040d0301340180181c041d400e4032070103600701d030ba00c200200722000111070a0301d4112004280355101d60101a050700010742c8174115a0049524400c902c1d540c011114080358419070340c000d000b9458400b000101c0d44c05400082d4494201003030801d014144224a418003002e60060315528550003410321300d0301a82142980015082400b000203141501502100c00d51a48145c1510741b41440c4610400c1e0641042c0107050100144485000c5d52003001601a04418025409810f503e0800490b03603034807000400f401d1050400c2070205440d4840d1094070387c40610f0604455403149152020340d545010074034240c0e000610580e1080c0840079003c1c00d00394035201a0b0042c88007043d186840d0f080380c100034 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 957271744 1250 957270494 957270529
    0x1122604120620090a0b0702060909040b04030809160320060a09180c08130c03020d14010e060c0927040803010305060c0705030a0311070c0611071d070e130f0902 71
    0x5104c0810385890f41003504080d2110b0700400303a907481507400011014000d125004d580806214100300410206141070390044d0b1194413041e403652250f13000151181c1000486401191104400700045520804520a190220806c80c440d0205d0100032800d19403141e220398010411541c81000010449042d100310140305420412030000582c400400704031000c0c01a105520104500105000c074003c07620008513401415102125003500e03201da030b030303403485000c030851946440b104018140000c101648180b0004c40e0251402c2d0401c02000704502d04e0080c654291004801c440203046240c00016020720b010b07540f040d880f98910b01e04540b4000008080c03004010062109100082d000400d071120b40040341000304003500141e68110751800f03140700180a089042c00300041d61500541030580c42c620a50640b00c100e6100d8901481d5100a4030702403034444030b003400007030050384900000195035600810349404040e0000580e016620300c81130b40020203548104600031841d01c00d0702200c02e080c25 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 957272994 1250 957271744 957271747
    0xe0f01231009090212030a02100501050906180c09040f1b180306050601032901080c040b07080307030e0d020606030705150d0902150a1701122604120620 67
    0x198101c4841c1001c103108141610b034541c803040d0210f507070304070f120041d00649608603501c60450740300c000c4d0f40d40f100c0410184202c0c80d00780003180d60b00b00240f49070311500c0b000d03210007549442250302c1b13041404000d24000300e0010501464650f80d550740150450440c126102140442c520221000071040208d03001090298640c0307d030156a00c01d410740000ca0381c11620008040d0749604c0160050100c4090108860260060840480460f010001c0d200b13002aa0341103410b5440403d510301c01c0c4110f0254188000c0c0c00e21000c000650721800031a408030341460f002c09c0c201710b001905854414401c4090000d84c02400400070141800c015040040c0000c66001c44039030201d010b00e004034031540901201c1c142d16561642d06549903000d2285185000b4180650741c0c5882c80b800030800224950440254004031000050341d034403d00700039003171039000f1001440800103503009100300c404ea600c495903040c6040c84005004501d11500d0342905002d10004154526158021100038100d41c8006c0c010b91070 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 957274244 1250 957272994 957273001
    0x14060106030e07060c03232a0c09090106050a03030207080105090105040206041203020c06041509123512090f0703051f0204080f0705091303020a03050d0e0f0123 71
    0x6000a4003000c8803000e0a064464881c46d0500f01c901c0048000400381c00300e810000c1004003a480b9000345a400741c0f03a00b40c0d044516000140e501c4084990660807032540c00f076200d01445240210809412982c0d2000001d81c1959441c007198620549500030340141c1c000100c1004518030070300503241d014070004020401e51034254009080790045000300380c4080721403101002014001c1145002310007004200c580c80da40d0f5481d261021000081c030480005600c940005030041020100900f01c5a10104540e0010740100c0a03800d4400007800003c0c1c6581c000d24103010030100800202052070302d5001004451402c00805440c000142100e1403035940420f0b030400c0852404120f9280201c0c6000c4c4d64030600c448064184041e0050b03400c012130502400d00d125105800004540003114001d980e6590b199641c0c40031508030300d2a407140500541c1200c07032550002845200207104403202c02400045031064042001d02d80f480700e985c003058a82d99004c103c1840c108498900c40191801c200c490303820b24 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 957275494 1250 957274244 957274271
    0x18090209010f05150a030f0516030b0d02090610050706090501050709150f030e1608010207030e0a08070e180d08191e05041110030504031b0302031219091406010603 72
    0x78403c004281e01400468145e030540c3c829085040f04408010050220b401c05081d11003c80c1e01c0c0841c918042407400072f801515003480884400c01640040100d0441e5403100140711002401100f10810010200b002c000042c019124451aa9000d030300002803d1400c40c2001d004454140c20400c411240300007201b00880c0c7c040001700004001e440c4c04a4000798601c0c615103440c4620b04110f414007004000441c4145056014240c0070703003e5540d900800300883c05000d10102c40340241216500b04290601400c541c1c0a56180c215074009002032904d5036100c0c807242019a85000c500000e023540e814807034a10a01e41005035600b80c034000400010852505000002d407041c0000308506072518001401c2c0710186203020243c1902038441c91f80007940c014018028001150118007040701c10b00911100c44080852180443d45078004500e0300203c541350090203103000b07000800e5038008856107946904180031340031030180300310f841d0140588421070040c02c0800c16040081054078040202c5203c4 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 957276744 1250 957275494 957275509
    0x50403050303190b1c120f0c080c0a15050f07030225020a03051203070210060317160206040902300c0c07033305060907110718090209010f05 62
    0x841d100100c2c4014040c583c042001d0030900002540c0302c80030b82e4515076040460884031600038426088140da03a540107609803904c40403200c00710b0000b0307807085078040003c03c90740c014100c025a90040b03480340c1c0b86507910b00d40300c00c148400300107110b03450340e0910055400c003443c1c0f60b82040b49401c080d403d1101e44643c40c03480e40c0305c8400221082151500000c1952114840040030b190800705032059141843c400c0c0d8415030082c1cad651030040c401e107180e940425049100d400103496011310003c410700d8120300795480c00d070041e10007000b92010a03030242c8010fa90b03040c01040207200007240940c80d2107681d0203602e4208140200c1d80b40042082c0c1c13803c0030078980c00d019958060291148182c55200101442d80340502c0d0713400084c0f45084c100d1400550003000411043e64601d0361302031000d41100380140b1015214103560700c42c0c100640b0760108406c240900741c0050003820036011255101d80c0c0e60811800c58400701c101251213070f550a000c41c19400c1064001e0b01405c42c0d10070503038180d4075090108141 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 957277994 1250 957276744 957276751
    0x31109060307180c0507201c050307140f0129040e060f0712020705160902070b01052404260d090e0a0b030a3503130f17030f07050403050303 62
    0x207195148542c0b5802401780f02903450700c07034100da84601d010081420800b0002100343c01188100d44450f41d400842d490580c00f0180e20703034450701a40c184015569060400481c16001d02503a004085001811210034410410b4900300b41500d10055a5030308400c81120a5503c0400c0c000c3d03007003c0d50008504000110b031a0403004803107014106590350f141c1220711040462115909900004008050140000340702020f051007400440420344d8460004c0124803c1c1c80e4010300304961480100260700c1c1c04481040032200c0307060f5419024604440c4100b444d0302903002050031602c1c6030002514020882003886c08030301428002c1039404411103000e84069403500c00e000d038415081d00040c102000740d41040c80c48000207000c98082100500d011951020010050003c007482c1b4016260084403281041c031010a881c5000303032558070350000121048000c23100540d0b03410b27204001c1400040217006a134059045801040d500c909003003d400c0100080a055503041002c184030a1001c90b5021040f030b0340 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 957279244 1250 957277994 957278039
    0xc120f08090a0b04031104060b090102100b06090301290109080601090b04180305071a10170a2a050102070303050a052a0f15010b040303081e01031109060307 69
    0x100d80c4600c10000d00c411005810090f2807031000b0400000b0040480c0d080c13000c030343c4200c800b03001041d1140c6060005000d92040940140d02c01300c8550312001c0c1a034006c0c111408040d110302c0c581300740326001c64203565440600780071182041422401e89201c40b0f030322540b141d0b001d02c1c10300aa14030301081320340c0c0c40301c0c18020011a140d03100c075011003ea6850b07000c011000f0f18800f10141d80d041c1414040c001d0b07041905c0983d689004030304500c0704e080c2c0000411744103d0111141c5d80d885424011031514180b4070081010581c400c12079038801052034030506a0b000100080b0090100d015000103d00e50010be0b0312542c15075000c03441c1403000030340000a60303c11901c0c6140003a1105a007a50026201c00c200240484035a900204001d200350082010140040002e040f90603441c0c4081e164455a0341c2407245100fa03050910090000a11074074455820131102d0908581c4440d2100520320154000c3c0d104032a4030603001032902e1242001701c0034070780c2f00c00110040c00301d0a01d0030540c2980c5510b01d030307140315 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 957280494 1250 957279244 957279247
    0xf101e050c12040608180f16062d0c03031d340911090a0905010906081f2a1e03021603110312040c05030105090f191e06090c120f08 58
    0x100c001b8041198032a41e0040904607000c550601030b240388a01120301840707002649030300341d00400380e0603540640c0c000c41c0390131110302c180c103039001d8100ea68074500d5804404158a40c0203503040301c2c0581c200d65840214401c050662180c3d9003009480796005018010399031105140001741d82c0c0410882e510443e80c8586001c64141182c1217030300b40b140305440c80b40303031310024682d03005c06c8111490388601d05072140c000342049003549483c1e42d540d032120382d100720710318240702001c45c41100c01c41d41d0841001e840c0c91441d0002c040c644140000c03044c9481840300f500042d40e080e40341c500420200d2030b200c80031060382011850000d620403200900080c06602405200008205c5502d1010400c200d17403402c1503014040880f82890310708003028141a2244034400d41c01c0502103000004003003900100da0729008010700b4402460100c840318001006020703540180040f030b036075822561058058100c14422000050b403032140c0d18000242002580014040c01005000000040c4407104c00c0e105041d040076029 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 957281744 1250 957280494 957280531
    0x80906150f1315050d050a1101031107060902010f08010e1b0408010c0801090c03020c0718022107110f0d050c0f0d020a03030608030304020f101e050c12040608 70
    0x2075025245600269003007602580341080400c0198891107008000c240301000c0e1561325810011000b242c5140900325030858000600003980c1c02c60200c480d101e040c14042400144c440d040c010507001780401751103641d240c40f0420110741e800904101d80123824103240f0301c00e506080c28103c207042d00429600c07000015042805502503000f041d100100341c84002408944112480202840350a01c24040300c1400c0840468509002e4025248080441d00042404901c0c00000c103171a507100781501d91000d0303401c00610720f210525650706080520941202c205900f0000802454104e070b100d008290f0303400c2508110343c0c0c0c40c1c003c81c50362805d009a103819600da1001c00c1e142420316618560b03000144c8100c03a100c40c8080e8011400e0b00703000c0c1c0207480410900f42d4074601c5a403603100c03c03200258803c01a8040700184c1c40c182039804030344040d41c5403440c9520620888803a02c65681848034005c50004502e41c84401030402801500c4904145801e0604d440c10380040c085000c060003401009107a0840d0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 957282994 1250 957281744 957281749
    0xf03010909060e03040f0806250804081303061a030106050109050f0111060115090b1903020d0207020a060509040f02040b0d0902031f050f07020a0c030b1302180105040c08090615 78
    0x1070b11483d81c031425640e4603945c1e101c00510a8045115555150040d907001400310aa48031b5158024401c00814600c00c0c824410121614000103108540586080c4118035450760718545d044082d5124602c001080348007050380704070360214000a0703403280c1c1c1402010310003664414030390340458005a610303981000d0402c1c0142c0703418102c03403040c0382944074040000980c4014805034500300c1c0c10580320510b0854542d110740c1c84600c01c00e012025185a82d40c06407000d0351081e8010a6042000c08c801824814a03074001440c103c400c0d480308001400104101000307181038454080d88691844085107000e2500156a40d2030207510b461148440d03850881c0400c0d5202801021004c1c1141101c10918400040310407005140507a00900b1461500707001448040c00000c3c650061904500403c00292460b910b00c10300000003000074844d10020301050700140c40d1050300642c074080703a0881891a606080c1403008481c00348130341000300305140090000c140f40204505030071401c885040e81305140b401c2c01 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 957284244 1250 957282994 957283001
    0x13080a02010b2d040f0608010216020f101e05211b16020405060f060d0933150504020406120f09020d140c0607140d020c060435210f0301090906 63
    0x41d407e540005400c500741c0c8286c2d00c44803950b80c0700700c40429104004c4028061001d030070904850214600818501014a00e61101182c40410740750892a201c1a00341901c1d1981d00545600c410301d1404040c440304540485030800b1103140264460f080c00c200209070405001e1f0003401038061175488020400d581c540e01c50400f004c882c041c080300ea8980000810324010100e041080e25143d8a600c440c80c0301c15020180e203040101c1c2307100b04005600150300c5540060075035007003d495100600704001a1a01c55002400092100382c8403101804a250002c070705440c0c080303803440e5216143c12609001683d031210780900c101c0e04440f00c4100302d0380340441c0c03614100ca0441150740c40700000c1a4001004001645c1320402c40c03510041d60b4034405a1030040e0f82d80c48070282d1141c2e00038018071052100c901c4079446661b60a01d820154180c4400c140d0504104903824007540b0200e0f0484480301003482101c0b418070b2041c2004001580c64030f207002d019903015000c10301500c034880b82ca030340c1003100f072154640 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 957285494 1250 957284244 957284249
    0x1204080417030a170f18070e090f100b0307180e030432090a020d11040605190e01090302040b0f0a0e06041a0607030813080a02010b2d040f06 62
    0x1004201d00344011055502d4204000c01c200040e020714205042544400205004a000500f03621840d102c40c400c094030941c141c01c000f2507512500900240030300e80520390901030321214000c1c01080c511000010b0800040341100004641884000170681c2c07000200e140455690922030089800c4a00341080541424003409640d80720214001c40c1c2d800c034400e12228141c1c1e510085941c40c80003241342110648845501640c0000d00c9000580986400e40051101040d44000002c003007000080100c0790303801079001134001880100300380c4400c2c5132601c1284203d51150500f411b03003108034030000f0088540780c000280103d850b04101030841c5c540311045403803030600800e540640703a00c0b504031060180c82183ca0178411401e211511002c04c0c080c98107010080c901070452880d00c4c00d60f0b2001d440300c00019056603174000104c1e11080102d00103201070f0611140d15400842c2d400c1070b850401032456410f803442c0d05862440c4a04203100145204641005e21050b030300400d00506181c00c0000030549035 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 957286744 1250 957285494 957285509
    0x7140c120d060602060f040b0a14040f05060106170a0906021611010f090609170309150a09050f030d141309020717070206120a0f1406010206060108070512040804 71
    0x1440000e60018604058140780e01c1c08003003000a01c0d5100012039840302d040e907100c0d011807445004180400c03000c1c0d09169200056010100713a85d400c507030010a00c1c1000b1034095482100400d04d503420004140400c50041c034070b0385072220440e086170003101d10742500505107a0141c1e91300c001207810031a258055a031f0004001c0f0241408200307030304011001c402d407031a14500191180c0c1980c8034450290905200783c03a00d0303a4520003540e041883e01850005070b0b40000c0002d00c02881201d1180c1d542e10810000c2e21550b00f070780e07901c1e0708500742c0c00382c000055500258417494003171452003066180040c40903c1d0221601d040c85121100c2c20700d695091107044400c00c0170f10f01541e0003180d45550b40d001480d802d481050a031461003d120508d1055024954000358400c404011030703001c4204018800d80c2000d401034002500e221000c81c0300d41107840045001d84d00210a40420845d50780620500307034004800e00300f1441074544208010498032400c00801070340d0310358401050130f0006610a07100980f102 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 957287994 1250 957286744 957286753
    0x10518250309060e030c0f1f15050a0618080106030305030c0304231e0f030708070501022502041a030c1005041a190507020f040f090609060b10020102070b07140c 71
    0x25007031300c0f9440b580003c000c130b9000d02c5103454440b60340c003000980f250781000201c0c1c290107018100502e00060031800441460107507019901040654400c00030704001c0120b40c46440204200c5088819294000da0080c402640f41241c01c00c0881e400c00c0882c0e0f071001030b09251964999a41c90114045500d0301880300c00b065400c502405060701c0000c4943c1002c0c1d0015450300da007800310360166075030407050950280c0340d041030080c0c00000c2c07003213005000564800d200150803e040b448058110740c99001d110705411452035840420b6081600c164001c80002980340500c060020002c20b03a165015020f060080380c1001015440c02d100c1d0058a028001a00383d1516443c0320300d8032403070306400c64650b0f03411802c1c80c980385031907160003142100c40c8250301914903000a0300000800c802010a01102c2d00e5183c0c03103100150010344240300c1c4152651107044005415140c20003441114804514640103580c0b04002c40c034081103e0100700ca03031221440c07401c0507485240b915034420760300800240d000300b4400c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 957289244 1250 957287994 957288011
    0x23009120a051608070b0702060f04092d0506012307060203130b01050a150315090e0a0c050114090603060d02092415120a06081501051825030906 64
    0x31440550f05004440041c2c440c1c1e45411919865110510440d48131440400ca003000508002c00500040080d41044a00301303030b0f4501c09a070a071000706e07441c2150400c1006d05000350fa42040c41300341c141031080c00300b0050340c070309080003038414603c1080006803403400882c244020201c40003100d1080350b100303005540b80d0030701c1d554008508c3c24200c1d007202d500e01585c00104241c02c00c402400211940c01140e04003a0164110940040040345035101626100000100f5130100500802e440209010018202c1088a0030400c0000d41142c100d02d04011041031140000b0003c0000c1c4c8201c5102141d40c0340d07480d141c550008114991400d0002e41080f0f204042025809280c8034003c5135a05600085922130701100c10070402c2c59180301c04211011040c071401e03503403003c3c4025180d0302201760080001c54944420381d96240802c000124a400052000140200c0c1421041d07558076444c02c1e0801c1015003024025043c1141120311001d5110401d0b00810301c506120350020800150000d40401c484c04 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 957290494 1250 957289244 957289253
    0x1512010e031b0c030102030906040f060902091e160c11030c090415060602010c05070f1a0c0414030109170307180f06030509070630050f0403023009120a 67
    0x81c00e4040c1c0039018050926050f43c14101802180e21640510b0050704260382e407544c0c0d6140900b14000c080e00c15554415070340700140c80b1404424020f810145007180d25003203043c00c2c52420400240486603281c01c2c00b10500b5815004288d100619600580d030b412121700103804245000689074a007540507847d04140410b11049070f409480001c1000c0d007e100290329920241d00781c0f50241241c400040c810040440450700d154070381900d40388541c10b00c160181009038200e40c44030044d03481e0b01c444034001504000401894100b00742c281c0e400c0e0001c2c0300d07803d540d80760741034070306c0c0702031001c500d003000000008480f80d11500584a0319400400b4418010f0f4440c44907050360f020a016a00200c1c0c40c2c0310205400240010305801200c4e51682c4034102c071000d48820380c00c08040503002c1e07000c8280110b01c14802d16807030300440e0304c2150980042c051501d45030400a11385101e002907500641180503001403240d206040e00b0380d07902e0f003410455a95160803001700e40c01010001480d40e403402840c07240410072 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 957291744 1250 957290494 957290527
    0xc04050a0e06130206040b0702010c060e0607021b0618060d1e0c03200a05070b01030f0c1703090103110d0e06010311040e1e030c070810141512010e03 66
    0x91060354102e55031075407050b801005040800710701941c0b20300f045c0400c10182454100a1058610600d098090407401e96105030a0700d6402c1400300c0e06030000820400042e904100c0c403030009400c16003160040e80c4420114009210704c0e0320b0f5005c540342c41e414042c42501c5510803600da00e080b2000c2000740e100411000320007410307a034585c25021410403008819291090003446404c0d03588041030203001b5010a004100c6a2100c515141400828082c00d004542c500762a01d0083d4041d621040c0c905419141ca40c600181c075800010180502ca00d0700e414031103002065480d03000b420308000622060044008403503010780d02c020440380307040c10904602c0c2040451082c0c105e130321035405405a58122000c0100790703401e01c0c009200c60707032040c1300c00d0700070000c481da64110040c2e0b0442030300d19100040c102181800e186420070b81c080d50001c000344130010200e200c0c0c10781000c0078485403c0541040c0c0d4102041042d500c100c0392084011005000083c48290b1107507000c0c003039100403656120382100c00800e85 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 957292994 1250 957291744 957291761
    0x30607080406110301050f0118091401080601080a1a040c170c040b01021b1e09070c030810120b100b042d0608062e050d0b0d020a12050c04050a 63
    0x8607041283c489440f0005034180d9060350b40c01000c11413050000d0004548000381c82040c1640c00060500004822201d40b04290f410b91810540c1c0c1a076605080800340b42000680c0700f071116500c0b0080c180081090035440310b0a040003490b1440094036942444035000c1c2654000041101c409810a11021400074181d4104403007030350140303c0c1c02031500059841d06040380c40c240e822607091895000c2850010700303602203001200c1c044c0300b05000d1940422041c400c21552180071501c42090102490b411040059000c0c40e00c0815103d100e08001c101c071107038403a6110007080d01c0c04910129411420101c8ac0e20007414440e21807544561380c544225040e103844c403411a0f60310786403404100c5a03240d00c0081c8000d0300c4580e15041840c0e2521414800721420842c0700c03a4124007110366000d45408080c1c0107800320045a940d442c0c8078003012964004a40d0403a10545c4138110710600e460041e11409500c00440303000c1c0400c00004103090900f1801e000304105243e0340940707881b00300682d4690350740c4890103 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 957294244 1250 957292994 957293003
    0xc010906050c040e0906010e0a0b0102030f0d0504031805030c040f1b09050f031203070f140a08040317061f03150e18030a0203160c0b12090c0a0303200c0306070804 72
    0xf02174440c009000d031940028000d00a5101d003860000d011307d121508140e64171001031044900d00001d002c4086240d80040c0000c2c514070b40c0b510305000900d07030312149070020b1410b4041d1040c02c0c945402e00081e0340f08560bc602500564548802c60f4076440b4580c4842d00c0e1941032908100014020301c4000c1008030b0600403140f0174540b0000000ca80c3c28006070701c005042c0340450803480ccd5252148144c1e0103502520080e03040020345080403412820401c06040021900d40b02c40f000e50620746009400d0141944840c21808644000c202d0b4540d6105030010030f0f03a01c00495590040812901180a401842304081c20070841c1500054180503c90840d4814480804000d540d501c2d120702c00703500ca00c02c41c0d00540040e4002c1c0725440068041a40500ca00c038451103158824a0b80d0750350742c41c825002020f0301a20218210101b03c0800d4040c000d1400d41e837402c44900420b903040d66005842281c1c9188a408000300b00300100001b8001002580314a006c000d086908902d0100700050111204987c100d4 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 957295494 1250 957294244 957294269
    0x109050d14070b070206030109090c17010f060b0c19020112020a021c05041a030601030f0e0c040c050405010f08100305071e080c010e060703121b180f0b0c010906050c04 74
    0x143c0c2da018082511296a40240b4040c510f03403816018902400079404203803124a00ca000000d03988070414110b05034006030100105044001c44440c0c01142c0c2c603030b0b010840c6450200200000b04c41c01107aa810383c6011170b0700081e2a0007a42c00101c8040c0c41400b100d000862000600c42070320740d00080e03080c0c52a404100c5040b400551544111945e00881c4151030041c43c0d04100700c500c01c080074000e10340c040010b02d030000d103a004a084102c103076680500d038803910380c008148500c1942040d00501d45403480c03d003070a501d0280350100003400e0a10a081e400b00700000000858540c2c6058180c91009517044012515819215042544c0c611514500c1d0091500c0802000808100c0410f41000340300058440c00f5610015900b071180707a07030000340110100b10480083ca180501c45201742e61480d071314000040c0d03419880301005001c0390204003d00503900c502e12003c2088501594083c800d0702d00e01d045c4a5120010315240501414620714020601810402008014a0710034083e000310b40300148082c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 957296744 1250 957295494 957295499
    0x10181505180d020d0201050d110d0507120507050301150e191806060c020108090f06090d110303010807091e141b070f020f150d0c08180a0f020109050d1407 68
    0x42c0c14820200007500f110908903a803000d0745c02080a015010311100011628078400944264071b540441810310000e5a208140500342d40d10400710303e07050641410030003d500300108c0c043c01e103000520031404005940340840300540c3c860141040c101001405418000d801d540100d14403000038024000001d0f8000c0761140340d02034074001d010032958651600c450b0145980c00445285000504007500c0b44680b034070812611204024682c45580001c1c041c0000d00d200d9800100030350004841c3c4101a4002e000501c400030300440c0d040e08580c2c01c01c0d80007070350900d920007044d8902c42800d600001e00b4500700a1a00005000030f8151241d0031100100c1c2a030109421540000c2c003650001401c1c0d01c10f803881510040c03d000914060304080100a0030048401124074619944450140074460fa2110364000406800c103403000c1d0031030b428a11a28242c070101054980d10103103104e02425458030116100107690060603810050700780980b41c9a00c0c0f895904081c2240743c4403503510b100324440c1c1e0303000 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 957297994 1250 957296744 957296749
    0x30705060109051b04060503041509050d1101050606270307080d12140c0d091b06050d060807080a03080403050f0412050d14090906030c06070b01031e021018150518 72
    0x100c900361451612180e0440c1c4880c1c81c0e002b041d40d42c24100e112003959444034000072410411030780201d035600b80c3c3c0b40f0301d0880e0080c40403821354001403c1c050042038184540130011008200c491036564144144210342d451500c0020304d4181d080e07001c150140200b41c400600c0781d0703100c1d00c0d40c1184803803c10140003c001c1c810005200300e82c11240080f5a541c1803200c6010807045e034204804c0103000e5811891100e2254452268031045540002c0204d8000103806550060a006280c010502c100250082d14a00001c0948401c02400700404000b0803000003800c05002d507050f985000001404036898544407400301c01000c50031b980944192045030203408650b8450001c0000402c48142700508085a2a05110110a002d0314281cac0c07501441c0800c550545a0b4400307021072a0058009034480c0d459800c10003a400041c00f001501242c801100c1800342c0c444020401c03100940d0b290086e19600b181640c1031558401e900b10b8008942424000d0915913032040c06005d2a06030a4003546480c1400000c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 957299244 1250 957297994 957297997
    0x1403030f0c0f24062107061206090902060912031e0a081803041203170406090b0f01061d0f0a0306020a021203090c01031503170a1106061f02030705060109051b 70
    0x1501c043c1008244005842410308902031412800050391281100d809035005504140d500d8104500290030034010b01c0c1d040700c0c58040c0c0c000903c034801c0100500489071700850200c0c401e01e025140581c1c5100058900c1d10010422914200030200741c06c00c1c1c2e010740c56413a0700d15a0200020b98005100c010200700c1d04041c1c040d24000700402da000461520386800d001aa21509481003601400326541606c0c10b00d02d440c1d043c0f1807003180b0034440010075600e58503040111901c050400310208420700010300c1695040801c181c9103030341440811281075404000504e600300c1146c000c61308103420503c00410015941c001d0b000705072041d020b45200c4400050682c0c058041120003810681c4400303e18440e5500907840060700f0b0030b00130201000507889450303030b601c100c0c40006485174a0348001150a009903028100c0000c101144026000ca800e010780000d42142c0400306940c920501003404000590003081201c40e40e0741d01c030301500c030b580d0780d0786485a00500c801c85003d424000c80100c01c1100641900 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 957300494 1250 957299244 957299293
    0x6130b07031e091e09050906011508010f030f020d060c020a03021c0c150204050303043317191103010e0c09101404030c27060f1403030f0c0f 62
    0x2e83d9000400e26048100000c203401c08040000c00c0040c034008038503040785014a42c407c810000c02488a075140441c2030340000752540140d0100f00d1220014480310340a40401c0c0704407600044500300c0107055000041000e5040d0800403c01340c034200c4c9106e0751030b030003150b11500e181c0a5000d03108000303280c11070440c030307001e0b150b04000002e0151040c66001641c0740d00a060203504070b04005081584640100386540c0c4030390071250a8050324a1400d0b4090004080d0300c1803100340c5084402d5050703150b040680f540550310780d18046003960700300040c200d8580c0025003044c10403044040c08121020103801c00d8507032003800b400e1b189250100000c1c0350a0040002c0707031450100a40069180d482c003042c12191280040f03d04480000100800404034440d4401400500b84110040441c00c103001c419043c0b111200d000082030130b0502c0c204102c59151b0154000444c1e0846400c0e006800c40c1c01c0002e070852007541500e0540001c041041000b01500155110030a0703800f03001c80d100ae031030031140d0985080095 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 957301744 1250 957300494 957300497
    0x503070b090402210c030a0c090506030a02160b130c0503030301030b1801092414040c090b06090409050f120309071a09030a14010c11070302090606130b07031e 70
    0xc000115a50805500a01200c0d910036401c20304100071040480580c4d40981780c40314100790101c14044c2400442c40b6800d9420201d0404485c0c7c103151102082c0f00d800014500c0c80050750101d2140c2d0b0310307000c2c501c0c4c070352420b035000f0580c803503038078000d4030f100e0001d220820240c80d07020803c0400300f0241400802c8034162074001004031415a15003448003031105411b41d0409030780d500c4640200010b050f05074909410010b0600c0c1c003000b40c0c18250b04904036038813003402c1d20084907040c050202048c0300c400c043c002e0760b003541c1000c1100035026000c00c02900c60484c2503034216180c0200c000c00d010002c90340f2071650100314213480840b0740290f92414140001d8400100da6009140204840248401e228070003501d281c6840c0c4c00d080244000906015a02d881a1008180c62036401c001c1c4200707119004c03030000c5905060402c58503a2032816134a041c13030301000b406184a880482c46580d210030a0700d003280c035081d29414199403030305480460741d0000d550450106c0e04104105403c0d01d00c5881036814503555 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 957302994 1250 957301744 957301747
    0x607030f0b15160602070b1501030c080703050915010306020903070e010605120604060e070305100b070308180106080307050a02010f0503010305060a0f1e060f080a17031f1203090503070b 82
    0x7015402c60032548040d034442581d510403400040041c81c1400604209802248103290342c3c5815100d050369100011103a0b8105854190404922a04072014a401c2601c524002803246e9401d040689800c00c0158050900848140000b04020880e001403102c0503054003501c022940e12400305d1040c0f80d00307010f4be1010480c28841080c480740c80d200001e520001c014000318005944415007519040f042c0c6142e00042d40342d108119600380d880180e80020b15264480525000d01e5844c01440c5002c040c1c45485405210003500f807180d40250022409028020b056940d96200381c035026640e103820f40d40407400300380181f00074600580250140c0b81201d8124002c0c2c8031550703c600210740100302c410207000c000380c2e07503071400d8024400b000d40d01c60880d503041074006480e90030101700110102c8664401e1416078480007031070300011440000d180740300c487ca100706603e94640d08103448015080304041c89c0850888100064110000d550050000d80030b0388402c0300c5c1a0300c0c0c0342490b82351076a90250b08090340c030 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 957304244 1250 957302994 957303019
    0xf060f0c0507080a05040308160b010501080108101a1809070e0114010305130606090c1e0c030f0c020d0b150307080606011812110319030906050721020607030f0b 71
    0x4004102814071072401c60b2030070340c4a030740d08c40391900b1510490214400801c0b6a4080200800049015110908004042c3d40c503003000f02c0c2c0e8583e4022107455100780c5a102098401024151601c2080c400510396840c031081d1420040c85580111240ea039103214003d00012005110340701141607903480c118054000e402d03603005602500700507000b0074810281e5103611000c61b04500c13944d0058002110b002c9107a00741907400038010b080c6250000711040c1c480301011102c030f42048801118640c0750038050300070620b0801c15a01d400c2c0b07520b03000c1e4104280c04145401c00c0782d08a00e80b0b214850799200d0383e2103080c44809040c2e41d4489401000349a9101401042c069030046011072252107030000c03511070007922080c0c24608003d4050049440c801d07c00000311251400344110090004086488000d90070035440003440a800c07403152030180b002c0000c41c40c0c2441604001c099140c1c020001c6456182c0080b072000356214000c50744100081c0c078001746c0001c0c3d00210300500d8442c003001068001d1080 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 957305494 1250 957304244 957304253
    0x102030307080c2a07050a0e0f040804030501020f120f04030212090604050414040b06011d0d02150307021509030c060a050901060e0705091e0607060e07080a0f060f0c0507 75
    0x5002525080071507000384045226403040d0110441003c21018130f500c0c1e90300062148504d05040d0b9080345100c2c852903d801c0c440d9103082000194822694200c046880d2500c1c103000c10603120b03640000c0c2180d4000a46281c9060317100006045403240300d43d0000c620707960610301403280f003400d48000380180c001c000803181003103182c1d025210181d0010440c520340341d5500001401c032078407440d8aa041c00e10b45030400042c0403103c1d06c0d9035400042800c21b40307007200301000c606282c010704121540c07143c107580c900700c002d6442ea80301081c0b0303491407142c0c6182d507414003040113592803090341c08044803007108400241099001009680c05100d106d030040100e03468001044015060003015070b5004e66070342c00002400d0720a1071009003d000d4a458150741c4980f62030900c45074101100414041d5070384969071211039165502110452504803500050852000c90018144035140d4001901341c480e48904505001c68924100100f41c030510081100ca962441c0103030a5510302c40408005c07500600081c00402c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 957306744 1250 957305494 957305507
    0x3021506040626010b0d080a0807140f1206120705150c0618010c030c0801051311310e19091203020c011503151d0106141e0102030307 59
    0x4400030300200380c543c0c488503222100581d040000303080d42e43d103801c805001ca0080c441d0401c12078040d00d6000f1061401e4444950745d1059010314020440c15078002500b9611581000a43c4624480559078864002c10241032a8018a07141c4c1c2e4002e2111020840d10b20700115440409050040600b003918074089c204a840301034001c0d0b0159458080088614104040c00141d01c104402038680800e01580760682e42103c1011015000341032400d44a0700500b0b0f000394280341191030485002410b0001035490001411281c0011001000042548260086d0303c006c49000e600102142403500c0e13030f103502c100e00c4410003072140320308038114040032455910b04080c0100550a4410020410015550b03070f007805401d02060303400020780c0c08101007402010130b02a0388102059000c00e60f82050568507000710034000b028800000950310300c0000c03a1202095001c080240070200208090765440343c0c04c001c4000200c891f244a55481c40c1111a00c00d000802d500008006030300039030070760b034039082d083e44d98 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 957307994 1250 957306744 957306751
    0x507051b012d0608030703020f1506030a0b060112060b030603391c06051005060a021b0102010b03060901021b12030c0313050a050706031104081902011106100503060a09030215 77
    0x302910b03181d003c50031130010002401450702c00c1c0c0c020410564803550303090402c030813030280d8200d0300401014083e05030340c000b50506180c3e4000e28814a00c0c0c4640c00140c1e01d002d04483c44904584c03c0100000b400310054014500c90f5506405641c400d101d01d040351000703400907020040c05500801d2003020030620891141d20075400c003170280341d00394010440e0b615100d02ea1580854000e900e0782c00b0000e20303c0200c141d150042505a070700904000c00c074500652682c0c0028012603881001045108240e031003500424008903001d001e4818130308051402c03a010b5804085050100441030312200707000600011211000c82e074001c103682c21911b46a412010a50000d005074110502c1701000b2030200d8024440381c186580301e034004004103850100080c0980e800c0414005c0b42ca1803d010420002d1008110301904440d00010141040c40354030040c2d4038600d00344900310040c49460200b001140f813101c0c081341078580c00c070102d814540d1500002c0d1300b41c90704840000d0042e04007411755403042c0012400240c0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 957309244 1250 957307994 957308081
    0x4031209050d05010e10051603052d0a05070504060215060112050109090b0601080907120c0902030106050c12090a060809010902060c0c01080f0f01031b090507051b01 73
    0x918903968030001c2c03000d0800480c1a50030365901c802c1050300da0010804141448240c0e8001d114600c0c0c821581445104140f91003420b040d200c4e000281400016000029401740181c013401c1c0707003d11850f44100c0204222662400389181c40d02007910140200141c900301e82c20342c0d005101d0010006019140c0740030103400503040c84002e4800d8203984416001d024060580038400082c82d4400d030411030303455180544818103000c41401484904840403841c001541c1c4145445020009a031400b18154a2a0783c40f221510b88044004100325070711074002c006c4440072404030b80b060444002d0007840c0d4425140c5150380409440801c11486015800c125405042c4100000f10701e03106030081541c0c0d92108560300420380000c406450990b070402581c64010300400d02c030040c81e00d0314201c98071300480b06000c06800c15042c0a0000410036640140c500580181c40781881181001e40001e421500a00b03c104d1030800f005400710b00c003080c141300f4038007051800c81c50303c00304074204c0c8804080100344140440 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 957310494 1250 957309244 957309257
    0x24071b030c06030203090d03050402100c050c09091f1a0f120d0206071706090609040519050a121b02040b03070801061404051614091807020a17040803040312 69
    0x8081440c001c078481c010005500c015070b0b6403030304036501030910001c4100002414507000c14000585c86010403110700c6841428680030044960a0642c5014032815800d64045030500808c603410101050480c0c45920f8400c41c520021003602e002d8040d6513181408403064811281c103c401481d0181c000c90613104042c0c2400c085a610004850520000ca841c04015900c01004e02560540c40500001400300d8104022258200680001c44400e00a04440e20a54410740864180302c0140f080414002500801c86540c1ea403c0c41d049480e1b000c00d500039103010043c410801182030207001000c040408003a41c0b00c4d02c20440c2d070300b080003e14080e001c8a03014440d40c1004602034409100e1180600040900316054850600410042e21802807054010040d144650282c0580040b081c4034401200303070703d660f00c0b00000c402184288401c00c0c40c51117503811080c18000681d401140d80302c00d4074080c00c8401c3c0c4a0743d211032010403600c264231840e01640d2040004101042d0a0750414456150a10704070 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 957311744 1250 957310494 957310499
    0x506070f09080d0e030606010513090902010905030f3313081905070510020705030d051515030405011a0d290115090f0b0f0304050c03010c0e24071b 65
    0x2850310103083c10384400706640c64240150303460300f0000c442d031006091900502d840d0741d007031030017080340164801e03901c0c515240c1500004580c00381e44101c000c1c1c400a0115802d90740716201c0c007650f4580c254000541820399008942920200702d03a0104401034407408074284e5151015a10881411007a041c0c4003120700b400314085070303003035050500780b0446540e4a0701d841d58882d003401c0f0b042c10800d4034190f0110b40b040103110005000442a80c24110728650001045c0c0e035a400828a85100c1e041d04a0340510072000400003801404042c0d03000700e000300d000701704a4400a0b5048920214140496417281c0d18020140000f00c0c0c3c0011510a0b40c0c0d54071801981d5075068400c0b040b1404282c11502446030800c0501c00d2040d44800100003c000c0845507640c09884c0100e00319151080c0c210b00340b0104000400034040c800100000e03a07101101500030040d010700300400a02034441e0200d07403849444460a1120340728203090381c12006105101e00945070880715030324420511500d5250454180c50003100 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 957312994 1250 957311744 957311759
    0xf03010b0a151202031005090a0e01090c03030e0f1309061b05031b0301050d0602090f150301050a0f082d06010f1404022b0207021306060f0206040506070f09 69
    0x4040c010442d003107080202d140c0001020340b84a48074019200c440d4418001c204411100c000010211034081c1c800c42400e4884120440103008629805c140da0b44c200000e2004101c8143c0c00315003107e009688031101d8107400401c00000e0080e2132803107944091031041d001204034250740b00003c07643c422500018035801c95400040e804c4e24440410020076808001c000644e01c5036115250140d1860004503e158100000201825440c840c0030701f070150b01160104550f282c44600146040004200c0400c0d080c24010b02141c0f9402409017a009442c0342c4800100c104244020b0425212188040c00c04c81100380d2601c0d4a0880d11502941520151703200840910020320480f07010300340200c82080010b013004000944425101c940500882c410405584c010305560200d1180d441c03a01800d105000a404412010303014051010358044840c0400e10980c00030b6512400807500e00da00c1c2c1205165224009a85803201201e01501c982c0004000456861041d400d030584c261080c10f0501009858008 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 957314244 1250 957312994 957313009
    0x1505181204031202030703090e060d1b091d030306040e0a020d06090b011403250b0c03040f0510170405120a080402030c10020a03050c030c0a030504090c050301140f03010b 75
    0x25800d9030032400141442405882c0e0445070258a990008500d00301c00c9a50080074a840da109120b0b00314807400101e2030030b5880b000c4150080740c00c201200c1014501e0f81e0001490b08192107103103039151410460f840d10304900c1c03866080560003d8061421541d41205101c050030f00e0603844242c0380212480040180e0741d125000528a01540f80058080c082c0d203031200d503004068100000000c40704030358603100ea4001503c10a0ba8447c0615401420307440d0f07245d03041c1d0082c16009040e800f40041065410343c280040940101d40e144001c54603038075074070300900c0089000c01c00000002a01c40344051141c88503804030700d0704184120100d840b5400c000340c5c000880d0b00003645610004a9000070f20055250402002c620080211083e110460540c031010b5a12254400f00a0500034082040c00200070140141e85000c00f04100340e5114405503d0018180c0c1e00500801d25070314541101c130020244030b60140c81c140c03094042501c07454600d2904000444a206070301a03810b6480f0310611659845201 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 957315494 1250 957314244 957314263
    0xa0c120b03070e0c0301030b060405010b030112020103060e070c03030515060a05250309080114070e12070302090f010303020601080706050a0809011514030f0303100501140c071d090109150518 84
    0x80000c1d46a5044d8623180e0301151001c1c1a031072040741020700503c000d420610840e0304444074001c5080a01c00c00b440181d000c1e14040d80702095082d08002000400c94104481d08603003803080e0741c104415915107030924036030248841c40c80d4200303c05200711450140100010042101e5004036000503600c3d800c4070316140403060104800040c10b14204210181007400341c051240c0f08146d00151134907240e4801480e0040001c40d880c42142402100b03202240c1c144034400c00b440e009001d00e0a00d2030302d680754a0a585003031004400500c101c0000080c41e910100d56882034030441e0b5141d0f480e003511400c0031920b88401410258065580b40f916144c551158040303180181040c40c48a002ca02c0c82c0c50070182028401c0d1044540c603002001000004002c144114040c0e0f03800f400c10201076071179402d10703890b640990030000c0c0036880341803800f10307140c5580c942c410a54207d0078403040351130380c0d0030614509071405564028644005484442c03841c0003160401d542c00600310705003911018441c00050b24110152 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 957316744 1250 957315494 957315511
    0x30e150d0204330503061503010314070509011a032203020a020a0618050405100e0f04021005040501051b1218090f040b161e03140a0c120b03070e 64
    0x40820034003c0c04041030312085a80d83d0740080704000420a05040000e90f0070880410500100007000c0360350708420004040a8880712540342e40c2c42e0300d07040329955500000d841c1171b07101d000700000b070510f020380c0c0d514141d81c0713200d083c42c000344440c80500d1a250409072408000c0c002c107400005c0328040d10380a40d000e00303009500a0402c1c45007801400b0481c1660341080042002c100982502e00b030160144400f156070136100090144c1d61503c2e14104000c0d65003100314070900b0722060061603030740b010250f0f005034000c44209441091406007514540300301d10401380443c60a011101d014040102c0c404003403c003500c180c510281200c4864441a80b14810f020b401c2001c3d4041d0450034109114a80e510003e11283d500340c0e03040c191a6100d01035001403280b14501d0206802c1100340b44114144000c5070300100340d01210300702d40b450180c06003000d83d107502c407075000e0f410008007030fa0014015614000701c4e68882d00400c505010510020b85048081d01d80c140c490403100042028148801c00c0c07190090 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 957317994 1250 957316744 957316747
    0xc07020405150a0e010b07080c012d06050303070b0604020c0f060c0d0e07050d080f0708040311100f050a2601060314070e0f1c120305090d08010e04030e150d02 70
    0xe0300b0401c0a0486800145185102800506c2450440000c84a1264100d9005502c42003554105409022880003400d4a0749041507031004805500c5100d507c0c0d101c502c0428883d41e61030701b042c90390340d001d1003a0143c0071400c0200461118201a401452841d540901351000d034000000036a140c000c058582114140001030f00c2140700b00e007031145181d004c01c0c050103800d915150800040c005481c400e40609041d000094004c0d040c60017070121050607030b000b480c454079581e4904009503580c10030410035000d60988111040c1003403040701d0b9603100341c089845442c10007000c5a01152100e04000b1441c8031110f03801c1041440d00420380d0340a0003480c0d1550701240010003219512420607002e4050028003c42d0500c6d070043c4ea030b4030b0751500b040e494241c038580c01100c40c000c41030125988112000d06014844000111f0301c80c2d02d60019072090820350105d52a00e40e00000488a1a90034443c00c042480450042000284031745900e9000b208014407103900d20500740d00c0d403051940f006100c00d120560 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 957319244 1250 957317994 957318031
    0xc07080d020723091e1303110303060d171b07050102011506080109020f070f060b0102121201051201020f12041101050c03090d0204060909030c020901050a1203080c07020405 76
    0x80c104140009880480d603c0c580600118500455806550700718a01c6204110b0010b07089070651a80401a0403020404c1d24032030074031501240346c0400c46001500014112040e40c07095250000460340960320151402401d64502d03101c00f44d40e81d0700764000324221081041109a00310345011340f44400300060010781039091609001a08440400d5541203001c0c0401e2410030150307420072032490464400110243c3d0318600703850f604003d4850170b0b1004001c0740c180e90300c41060140305e84c8501c011540a80840700c0301b180501d0041000d01480d5082e00d01c3e1b040e800014441c50038100c4094210510050015003401030b5151664055005111110068048270b42000107010840b001003811711001e01700145480e441034460750302c030300c100e0305002c0c0138100d100010710441d200da60060740148080c45d010001d03200c00f850001c10040800c032041c3c1c49645008004201450700314000f50407034986c00414540360310749035819100703000b0007859818481c2e018441d010160300c650042e0703842202066545450081d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 957320494 1250 957319244 957319247
    0x1050f01110c0a03111f02060a0b0a0b0a020d0f0815060c190503030f01060512061c020301021b0c030c011731350714070e100b0a080105010c06020c07080d 68
    0x40102807049400c4481c1c561b03885607004182c95070461011540880e0074111000230401180703180c1c5c007060f00b01c0c40c001a2100b500b9800310f06104c00541640e83c1e548240100f070f00486403000190f030650b240c03812810301c1c101c1a14000008110b070359800b82c00c1e1101084031140501c0e0b00644a038050702c481d00000304100c0c0404070010039901400d420f08106042071070091030740d1010703080107040300c0c0218017000da0191489200c24410402d558014001e541e500c0100e80744003410700002d02142024480c0d20000c003079034038021404908140041e0340d8400d01300260040d04000e000041c1141d0405001c011b04e170f124000100000002c000001480503400a00a241980d0a0f03840000500c21441d5289042401007101d1803038192001500d082590310342540d428a000a607500800f42d03102489550400503165600d1a8045d108098040501c03601c196106a0241144910121b10001411280061200f58000c0b000507080c1e6008541c01410154150341c00e5107014031a4002c080d940d070104175401c1000d13 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 957321744 1250 957320494 957320509
    0x7080d030605010f08010e06060c010b04110a020c0904120e010c060204060503070e010302070b01030b061206040501051807080309040f0906180213060e160c0516060206070801050f01110c0a0311 85
    0x9071185817035450b540c034003d07465600c0d100141c85070740304120001d50300c15588425001407007003a0700108100081004201030440780c0d413000803c00b0250040050f06404d5280ca01c03006131040350800002110700455080c00c035100c0e060266114140041c0030054008590a840640702074500c945405030b6030700f0328100c0540550074050840303041500401a0000180c0d0030300c002811130707600000f03041c21030320303140c00044441c0c0030003400b48045d200f501c04200600c241500f1a5001d41d550809603484a9401070700c5540f14076103805a00090f40c420000c5c030086060960182e20503412003d000a070610a640e40d850035a541e90030345002c0081c0e0681c01d002985002d80440d50b880e011346104003d45407420041c201904001000b100440450b4011050320320b000d48a440046c43e0300c0720a42e40c80945080324800c1c000050701428006102e50800580c4043c015042c072811780c1d40c01050709211280c5000110340380003180302245207a0280c941d2900c2540c4400d00c0f40805548a210b05d000702d41e2030754080c4800c0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 957322994 1250 957321744 957321767
    0x60d03110312241f02031c090b06030115060c1a09060a05010501021605060708070b04030f1202031003080d2a021002070b0601140c0a121209170c07080d03060501 71
    0x104840300c0c4801d0a56110004d01389403884002a108401c00c0d0a042a401c42c000c0d50f490004007411507522194030082e1354821001c0c81c0c4100c6840610b17490b510203060032280f14501c240e8242582180900c6858096062103c00f14450380c41c0910712031241064a00c070030400c0d02d0300b10302e540c804030038858000d031140101400b4080030301c0200000c89008180840e035444504c03c8034010240050614280828030040311607041d0480400741c0a400c10345801014408082000400150400340c072000d080b9181c001c80c2d004800425452103098215111403889a000071560010380390745070341c40001000b911845414007200c1e514841d80301202d801d406810645c80d009202c608134410400800004d600c4020b050f00503000f07282070841150500103c0100e4401d50311550114440d400d014010064017510302d00310021165200c10310b01d2180c41d4400d007914a0303036000510410880200c140002480300240c09110300340e8084480d41e90f42e40f1095410182c01d4241e03080083d407202c1041c032255030003400c494003 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 957324244 1250 957322994 957323041
    0x40314011812021e1c0c1403071709031f02090310060501020709140c0a0909090813080f060103060b0d0f0b100803040e281415010512060d03110312 65
    0x2010001d00c1e02c8180c40e01c1403406040c0d4aa0003080320a001d0310302ca12401441568044080b003607401c07088087c00c0c1d0360382008008580c181c400b4104520a1684030301074920519025004120f0201014044000c1040e6008004030099090088202c140d0b020820400302a1007008000f8406d803e200c002400c101080d0403429000c3e04080d0810001c109607503500b0b5220800c030301c2d52a01e6405181c0c0c102d0714581d0a900629032107003890440c1e814030031448010301c0301c1d050701004010182d6682d001300b601d603644811040c8540c0c1202004001103502900b00040f07404000b842211440c83c01e50350f80e0380c840e41d50081664a10382c42d50400c00401d025400c4400034000110045050528101c118040034000800704d54a5004c84034810300c01c2c1c8404012050ac07200003007030034040c81405408244919000316041200980354039071600c081d5006108131403200784070407007242d425901c4c40d00340428140341e118201d08001c8000b0341031000d5a800c0c0060035003400040058072039406c180c0044c100b0002590304811 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 957325494 1250 957324244 957324283
    0x106080a02030a060c02031c06050301060f120b0402010e03070b070219050a1e0b0408011a0a080703061a0423070e090f0406240501020106091104031401181202 70
    0x1001d603400007a0700041a41c00000130880c031031078000032401d40c040d604c80300d030795468264184480116180c10200c140c0d403068008008059880700701c0001a96640b04254030140742ca0b44000c041003400e950590310500604203107185900500210385000c52660096201000103d040011440c1203500210840d800c020306008007401e00c000503110070014422000066040c900540c03900481940d6800203122490b141521107a49030300702c4d4044d1803041444091240c04800450b081d00d031a03885602689c0e802d40003003a0741402d660b2104c0042c8500c00861000545090b9020a2640c55004401c0400004100c012500103142008030000c280038041e1020712181c1c1d2007420042c1c8429901d507034020454100d11440e0786803030034840e000f082c0360104071402800002c1c1c4074900c2c4a1112584045410a03070080007400d65500d1110103c41c00c100c5000102e4a081101300f0100d2196081450341d42881c00000400d000308500007004082031070800c03180402500c205c19421601805407514800802c0f0642 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 957326744 1250 957325494 957325513
    0x1202090609060c0f1504140703030801050f0111061e090d020a060b060d0c020f1002090a05010c0201020f01090c0e181c030b121b0d11090c07021908010608 68
    0x36828000c0381111409000045000a203200c0c0800c8520040b5442c082950381e486103800c0c0b000d00c519012141660010180b070210000d419000480d60216505a61144aa03909080421000035010340041d810440c5125040307480c2c28042c0302e150b015143c180320200c0d1060010012514100c4001c0480500d5040605c0c00c0780345503004501d50040702da00120000380e440d540000660180540c00b4403c070b40c5450600d10700c4c041c80e00007c14889014504044800028907010068140d00c178100c2041e4000050010401c4154015520340c1b441c18414015103d10003500000a400c5070f001150076107643c40c13071090801c6401002960560441c2c42d220302d070101d210040424a55404400c4940030400c101901c100c0b84984c401d500081040200510b00d51003100607100d40c07a1307110b602d44603030349028130800011400c6281020104201580c4003545101103156802085480d02d0014506603030342000300b200400590381d8400e0100c4640741d846407601c2c15400e10031500d0031506c0d0f58100e814181e0026250 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 957327994 1250 957326744 957326749
    0x22201b010b06130b0f04090e07061b030912050f031201031e03080f1f080313081c121104090f1a1804020f04142a0a1d150a120209 57
    0x68109840141c1896a600c6882c04211741c2148100e030710110403540b504114030001240481c0003021200c03a5a1600315503103120949141c030100c0f0708001000f00f0b4003e682000854101071231000c1141c018000d07100c05104801210341503600102d07003010700384400300040c004c0126000c1600180c041c03290032501c04505696014214110181c110b1044140030800110080080042c0a41c1124400c0403194031554030b48540ea603c0c1c10807000044200404c0c0d00104490000148540140b102c032040307205008a054002e885003922114911038260b1079a038072407a008900401403000744042980020642c100014a0007200d121060801c56000c8400100310340d0350701d5080d680011164111070340c105440c0e500c0010800e401d040d40203900a418003c1c1d01d201402c1200c085440368000040500611517005154485200380c050078429088040c0202d407152441000d960300020003100c1804103100040000900303004064001e48154400000c1300511580c0c030400b01d16805496010650404103143c00 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 957329244 1250 957327994 957328027
    0x4030f09120803010512010f15090615050f0c01060806040c03060515010e0103110d05010b040e0907060c3302041401030501080717070909060209090622201b010b06 72
    0x1741d0351181559280030f4084401c20342c000c404000010b0010040346000074014114021544951515545005030004002103404001d03148801c80e5590f8518001c1000202c8107103820100541b205596502000702d400030f42001050b00443c0180001c0d070902e89589845c8040c0c440052031002802082404228a03903004214107824038001d09002c201201e15014500041c041c40d16410490380c241400003880508500050040d144140503030202c1b640c58841c075956030300c8140b14090000c0c0328100282c0108414812880c4c4107062082c4000182c403100355090307880010180c12492184e40010104403a60500307581e001030318004e007420302480d071500b00b0994031a8a144142c0d01c007032a00fd5500e1403007501c24000500a440f24850401c170900c2a810040000e401035000c90b070044510002090862038038802d003283d031102c203030030400101018400d0b030b8002c0c0035402c400306d00c084051020540c1c5145e000c8013401c0540b1090aa1605100440b1400c030f0035a8170319940f5074001da0f000c12004079590404038 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 957330494 1250 957329244 957329249
    0x20a030807120f021305010f02150601140702221a06030604200f1c050f0a1a100309260f030c04050a09090308060a08030a03180b04030f0912080301 65
    0x348200b030150001d10b81c401418a00030b086284520005020315500c81c04030700e810a580080c0d036490040640d401003070b0303030721010349441c0d1802c9915400011040e611400e514802d080300c4100440c142140d550105410b50703040034020501e601c0c04400d142c141200f034819410002640c400d005011820310010401c1480701500c0d0f00d004581742d45048002044102d82850000c0c244010541e4813040340440e51000c2d04602802c1075003a07150220006c1d403990b10300030303640108000c0040b140d2035166000950020200e03035400e880405480088021155a030782a52000d101030354602180621440ca0412071400d041d0204000801241c2035805400180000703850b641c8002c0d5207002c1d5691030300d0600c80c4080c081d5901c0140d001d400b048012403841c2481d0000c045041c0300b603c030708002d620750f0300400c40015428001c2c0c0215030300c14080040c2103407207078101074000b411120b112140c500f410345070041d08180c02c0b9400d401045203010408001079202c00c19034018100002c50440318401551240344034407062 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 957331744 1250 957330494 957330497
    0x50a1b08041b0e070f02011e0c12110705070e2517040609060b010f051e0403020a03240b03032b05150102010f02181005070b0702060412020a030807 65
    0x348001400c0042964010040550004104100558401803a141100216182e20000d0100207907203140d030340140207004030400c1e00001c2440d05820011201c0082100005e1030b400c0141e007002400304200c241c4100c81c00100d0f0450280d42e41c03030850400d40e180080c10390250f8580302c1d22600304800b600c6c01d25070000d2100c240b010b03200720181840d4400c41d0070700d4211421074401c1d0380c01018002002055400b802c102d9108110902044001c10010364404810041c5040480c83c204141c2d000c002a00198240301c8503061426810300340c40f41c02080c900390007034004503284212495068a01860b0409260842e5241d10301403007960103040100b500c0c2d000704031110390741e000810030040d030710548000b804045110340e11040009240003021000001005901140594a1720134040301002c00c1f4002c0301c1004a825503981042d0f10450180101421420b42d0074082000900000c0700081040c0e04441c05580c80758001e1141d4101801e102c1c41ea1140604110155030042d03142000084c0c05c80045d50b40312606 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 957332994 1250 957331744 957331757
    0x504061e0e0903040b0d0b18060a0302010809030c032a0304060c06050606090d0b0a0b01020706090e0721020403032c0d1b030c0e0601210905030706090510050a1b 71
    0x100c40b1028a1801a40c0040d09007220100700c030105004d0035808500111012100c0d80510580c03c1c540140001c0217460341c0d904085882010b00141d4041d02d480364118040b141120301c2c040550f1583e0b801d40e081011154202d1010104105a130070301040020322007204803026510b098508200541028100d090040c015072326040043c01d140d40328070a0707402241c00500f07a80c961083c04d2919507036035603040761000d1400d868070401403225480099440305440c2d190300c95441d801c1c1400d41030170040c0307401800101080b92102242e0840d200d6081c01212240a4900240c1c5407419031801400e0310f000c16510910f1144401402090a44c41c044210703020301058804a682ca00c00341802218180181e0401c005644507030b0002040182510f403c80407280c1c094034400c3d0310f40340d9400444e421750315416202215a0060f480210003002580050005032080301242e14140d0180d0762a420b031403c41d80d06880581084030882d80d001c060303000300c40d40500201c40030050240050803009007868201d9611041001 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 957334244 1250 957332994 957333001
    0x602071406070807030c050706030b01020d0c170c0d0806060306130504030e090108070603242d06050406030b0409080a030b0a0b0304060203040311010204031e1a070203040504061e0e 80
    0x110003088480382500f01904580d545800e00307000d01003101c460b40c04c0720903225200002aa01d88030380b1400d155010140e0141c00410a8020110768981000078195100148040441d954074030302030080540c00c482e44098000d800d450b2001616404006101a0040360108104025603580c0000c82e0b02115404100003290303200d600b01128800320300c00440d90403d1280b400400d01005c00940e9030200d503083d603000c3c0320484119001102611100b201050f01c80c0b8028410b1203144003100035002d1941c802e446c2500b640c0d000c42034880c040320017a031201001c100c000809105550b0302d80541105650103450a0104585070303621030340e091003040f101c00101a034911001e4800d035582a0268002c01040381050303203a040a041c140d001350702c1541c00b20003140c1110340914040034103000f690211b0b5041481e400103c00c0c0350050900100c2000c0003160245a00c0c03681c80c02400c003183c1e00c02d02607880740d4011a200e908001c00e01c4112600c58000d02c03498110200000000c4000250813016140b44160244030340d00c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 957335494 1250 957334244 957334249
    0x80103140c0301050c09040f060e0c07151b080603030a020a112706090f0103050a03050306060904050a05091e06010b0a0507170901120c0e0936070e0106020714 70
    0x19609401c0a0b415420301c002d220110758450040d104054040301c0c10824410400d00c2c12040f1103642c03065090240c510f400080104600ca80940201030140d945900b4003440b0040c2c0340100c5e000d80102441c000d07000d041c02c0c40050f0740000759a603c21401d0f4011407802d401554003035070702d100c140c8008110341d400760a00e41036a103600d4101c40040300094120051321002014007445408125452402102013000040070101001410750480350848040c0c0040511600c04403410760000700031a4000d42c04210025003a245c501c0703a0b41c850707104004000780a061840e800c81c2000119a809684030102100e50346100b000815000d0449015100140d59940359800c20364441c052070902811072445c00303c442d40301d041d040000b403007000d00986c0c69900110050b0303946004c0300c004c442c4100000300700250140340750824451268001c03007000b000000496940c40031008517030035034031544003210b16a501c4a20000c0b00b0401c0303030041c09a80c0c011516541c18414000c1d960061880b480c0b03000441800c00407843e4 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 957336744 1250 957335494 957335503
    0x3050d2123220320070612020d0b12010e0d0311250204090c1802130603020d061505040302040513030c1226090f01150b070203101a0306130308010314 66
    0x600c0c00c014800b4014030705010b0162110510903803903c103680718504452500118110054603025180e034094803540603420b400035006981000005c1d5500c8a9240840d13a407000c410705481e14042c00401c81c0a20080050b050104d81040395046c103041c0308203401520a0070058400800440c2e070900781c40365201d0182d410001602c54040d400519100760079050101403081007040e10740144007544822030a480d44001c0340329400c845603485046c08000c3c4640c030712980007072018200d070400c041201922078444914112b003412440001c074038001030400840c20305005050703001c62040c0f41540001c981c0d44000c0c080c200054070060622000c40c0c2d003c1120750042041201c2c4040140100380e022822140c4080d56080613141940390f880342c24100b4400e603030140544000c0b0404080c0040d55a40340c03050988040d08800c20490b498004c10024220303411282c41101d4188591140000b0b2202001050509100000c0e2400a130400303a5004000030030f42142c3c0c1141100d80c0224540c1d6420124950582031 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 957337994 1250 957336744 957336781
    0x821060609101e031b020609070e0c0715020a090f0302060a05070503070501062c1501080c0706050c0909010503060c0a0f030905011530120903050d2123 67
    0x240c074072908940408503403617402030061824505d82d84002038a400360581c2c3d00c190840c0d000340558813803d42800440e20480300c0580004040040c40c3c10110f06684520303a10045030b0100304d883e9408543c104400e43d1003240d54004140341e8140340741da20300795000310b5000c2c480d0418070010b00c140050b02400300a400c004070313400560407400030400181c03958104132000b40400354181e060108003204500d81160341c03403110301400401c482c803004281c4400064841d01802004103031b00d1407052000c040030803840e0040c2c1b80310709403070409240d0b40c0c420501000189641030300b00314001e60241d000c0001a4a0130811103003441003e00380101000458207003140540392014000749103508019000c080040094492410307035007841c0000c8602200840c2400038004680d04004100000010710800300d42108100cbc0c00209281c070b02904c82e00d40780e8465520b40003107080000300040102003031b00901c0300c1e205a00030398844080011702c403100c40300203102d83e074000740c21260003c50404c601140c003001504000184 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 957339244 1250 957337994 957338027
    0x16020f15070b0a0b01080708060d1b082802060d1a040e010207060c03291215090c0108070903110f1003091104090b04030810080a082106060910 63
    0x10344544518090390502e400762106090282441d54059480d070141210a2141d84140e030381c0c1645648140030481c044a8105003524281150051001c2500b8444d84100180022500500f40e085204403006803031440d480300e1702c00c501c000028000c0140d4800e0119a92654000408280000032400c2c41e4901c0ca045069140d00524050b4420040070303041d0013820849006250070441d281c1400c1d8142c0586000c04c0803880c20300440a4042400ca100908140c43e042018080245108a40030640c2c5807802c901c02d4101a480c8800400c0300388002004241c48200013841c1401031801e1a90014000b40030500006080c014012001e0005460f210040b54000d800180100b40b86416040081d009090b0408141d460b5415940c203c0004d003054010495869840041c003a1a565a03031021200c92070064119044c52441d113600090300741d0700b0400820000c1c080e100c10755a5030703507203003050101225054848507446101c1d810061160754600c107440b0702050580c0c000e000000e07170304001c030384041c10340c071080a = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 957340494 1250 957339244 957339247
    0x901031212230703200a031a031905120a140f070507062105060d17040306060303090e2a0d1103040b040b0117100b010c02090a0e1216020f15 62
    0xb8040700b01004001c0c05444607880403c45c0130906000315400d50f02c0160507403c540002c10054000610a07480507507000100d283d01c43d103000c0034000207800c04e94281e003981c00f2584030800c02800d2000034040c1c1503510b0240d0204501e04a94a0b1003d8511009010b0030241010003041c4810002d91311400c0b2040c241d4048160b0f440d00d500c0d008090f24134a807500070784010b540000b10400e610b40740e501c113090103030a008040d000a03c029684480440303440041d12440c0110602c000000140343d4050100910b03c26113400aa040c00c00c105a00079007030090074030311038214030400c6a0420b0740325030300840c4142c02541c0c3c85903102d5400d032109015105140c1c0407040407000208000c28040050314490169108502c40e0358075982c1d81c11018070310207a500030038065800415246107080101d85c0000782100741810b0401e05a40e039900001c1e03200d241200d0401655441d040740100c0042e0521200c0100744861860505003450410703407030050785001400900400c41c00d04590b40b00d03034540e0b1040700080c0700c010316203 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 957341744 1250 957340494 957340541
    0xc030705010c030c020106080604020d0f0c090f0c0f0e0f06041701020405040e07063908090301200d021c020301030c03140c090a090309030b0c04030b060901031212 72
    0x14002c284074107944002038502182c2c1c4c144540306004072404c071a0b01d000101219260b5400700010040c0c038600440e504240081c00400050b40d03062000000c107211a00050200c034a1340b0354006940155141c0c804001d944410010f0880d040303802c50030700703800c159100b488511803031004c14003a01c540d41210003000010701840c442c1050540080040c0c40c020384050040c4950000500c1c0e5602241c0250300c00f0070790b0786168000100c440036603d05001c0c4004160001c403410000100d40c001c295440a45000100040808403801e090240008500449412180d901d1400c14130000300c0c0592640840d1042c0c000620744820020302c1000320020ba1150811943d0f96541d2508a003075008038442110070f040300a0000010b45404540708030001000b030718100e229540c80c05954010500d00d0011024001994800700105d400741503614419440e030030500340e680703080d402d00142081c001001588110310110041c0000f8611a441c0034400341c080c1400d190912190440d4800380041060003410b60700003000d00c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 957342994 1250 957341744 957341753
    0x30609060b0306011e1211190b18190e06012001061202011805090c0913140910020705030906031015050703080105040e0a120302120a0f06060f020c0d03050c0307 71
    0x2d400000071500440c01740b60b615010004200031080c1c025180405200340c211b9142044608441030b00310034800c9407807032500c502030540160494030f000080e5042d102ca500b1443d080c81070806d51100e90a20b603201c5580e00e03008030200103c80041889040006800d40c03901800c0c2d031b02d5111552400111300a210968556440740340f194034107401a4000f03400e00d114880003480c140c071501c09960b4080c0ca411950b0390741c07044400c050f50040724640d4110400303020030400c419151141c0700350854000445026030520541c418600144440d0304040e89104014880c0090340000031105a1041569165100d58622031022408030180d80300348203542c22000140c1e0001e40c000000c0020510984864282c2d9032108203220417a00c154000f0641940301007182c6001c203515070f1108000c10f901d4503000d07103401c50300101441081801d5800c940903030f49504070031802094a0041c10301070074480c6041d480442d0b21410003580c62400105850080c0c484514081c10f26100380700302d5110340032500890341d581c11580b40 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 957344244 1250 957342994 957343019
    0x41a03030f0a03180309030f030504081b040b03070f0e060411040902090103050a0b0102060a0906150f0314060f040602030c0904050c03340509060d09050708010b0f0a030609060b030601 81
    0xc0603000a0f18011584618214001400380c0c02c98045c0c0c2d1b5162910700350f030b031800324405c030b030007020f4003401010b120014820b01c08002100d070b001c13182c50301a009000c10304180700503910322011703061203031b000507900340168144076119100b15810500d0410040d140c0c900400d0081c1a1511042c0a0300030024000c10010a00d4004008520782aa0204016980c0300b03540341c103c42403130418500507013059011031500165500048091341c00380398001044c4000c4006849041002d40c40364415035442d140030414450120400c107090022600544005d14000407405c101e200010001480c081d404070100b0700950107a000d46a017050090f1081000b810205030204458108036403070207070b02c00c200359428a070366a100702e495a0341484c48032000c41003c00d11400c0e01c2d80d40220070b02d1900901c0902060741c55982c14002e060405000b05d001d00340741c40c03c20215a080d6030100200d180240e47c5e0f07512046507512910820801c0780e4003d000014642124034041c00501050b0000551500c5400000301c0c0c0700d61200d1 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 957345494 1250 957344244 957344257
    0xc090307081612021c15230a0c02030306010c1704030303020711222003010906061e1e0203130b0c070e04021c14010f0510061d041a03030f 61
    0x40b92021026558003a0819010b000c081c003d410a020240041102845060b0311540354401d40c0000700f400b0400518504491020400284000081e1481401842c00301c0d03115401aa10780c4080c4803c034040d08000e5501d10025054904220720707a5030100038407405d03010b81c01002e042c0d99015035549540b420010080e40203c00192001e1a040c5032940c91071604000700580703240c2c50440740c824544c00e691558010038070a0003012480c002030003403485040924000b1406414120030016425003855401801c1d4021a00e640403440c41e5186241d130303e55006020b4500684184058030100c0800342012801c41c0030f4000102c5602503007581c04903164060502810f20368050308101e038032701603803550102100e0b201541c019402210b403201150701640200140e4610a006030303064114103880a083c0ca085881d2107281d02d01180e96041400754006215a00000a003e0f510307000301c080c0a4041f0010b081449640c115110344c3c0e941e4111142180f52030070042d0802c000800f520788446690400d0700a0b9880071 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 957346744 1250 957345494 957345523
    0x6091006050609030c041d060405010e070806010b190306180632040902061c0b010e010906200c06070c050a12050d3c1709030a080c09030708 62
    0xc04046a107082090a40700c410300010300130001c0915403c240b10040649140c038151956101001c4ea500070010828a401503100d50000a0400307103820ba1103090000a0704554115040340e070040102a803008207075441000480100c140c0244190300c150f0042c40140d025021007a44641d0904295150380d110b0b8049404142c0030340c0b0890f420705c0a05070024041c001d2140c0b101c101d1401c400c0c10313082c40c0d40700e042c90a06c00303400c5925254110003400e40010162090b01c920540740c0b02c1c009450b51340440c038964161400c1c01c200191b00d00308400544514000c07034425981d41c024803d02002403400304440c265440d40507001a540d80e486042c1600050303003502405000710440c80700082d283d001d054404444640040161007200d014060464908103000c80c50a195000c0b006c01c40ba5040c00a902030040555060040180c041580300142c2030080d00040100b03141441d50070802240c0740070040701c0580c4c00900d4106e01c41d65580c0c40a103218018500d03016058401c40c400410000400500300241c180b51 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 957347994 1250 957346744 957346751
    0x905030306010f2c040e01021308070503010203061f02150c0c070e040c030f08120c1b01050603030412020102070f0f0e090d050409020714011b1206150807050c060910 73
    0x100b00c01503500030100c1002c41d0582e00700303a030134803100c0640a030510f81c0341c500100080b541ca031424032201e003680c1110283c0c89124803040390401c0710600400494000b864194000e60841c500800016a0041204ea602051219600003002d010f4403d000806c83d00340000507104031402c10a07078804050300150050307101c03031080d1a00400c0e01c4402d002c005109a6126003212506070465890004a4181c2c000c2100c500c13070148514480e9415200415224404440f999522071381c60f10280c00c481110b014040c0842e900d090248660fa84021045900786c07800c02d040e085000f40140700407403070400310f036102c9014250048004950b5015404801c02210070581d5100d0b642c0e103c112003151030324001c050402c007250042200300849041600a040c2c510301070028006400b43c030110540c01d6545589020490300d06180708a5101038200307882d801c42051072074040285604000d4501440d00407850f030383c000c0c07003804000076600911800c00c6031403603013800b820b503034131401c003007885a648401003100050824103 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 957349244 1250 957347994 957348017
    0x30f210a2309030406111002030405150a051902030603070506120105150c03040e070c0f06050412180315180309050a05010815190512030d060b03010b03180709090503030601 76
    0x61401d160750003510204065440c081c50302034161500c41b0301c20a1405c107401a104a0016101d007840038511a60003540645030281700c8101d05040e88030000c0c42c60072824a01010b10844041080c50481d280543d50001a80c9485d003400003854980c543c0e0015070f11480c001281514158129280350403100e007903412004010514409070804e00802030110360b59401030001b00180200b03001d8045c1c101c44036040c994810a840e80341c104102c541c0413020b40e03103580c50384107000812401c0d42c4804104d601510f084464442c90030b00c105040007913840050301e07505145800c00030702e82007588903034008160000516a0001549400b0f41604035038854140720780451140041d0030750040650070302c25410b00c2c0050005600c441308001d00d106841c03801c4d54111404d444041aa40c80f02288445490407180086440704002c070307504001d40750950072101503480f0a100410400031014241e0341c00101c140204942e55110f030034140d24212041d40000e00ba6402c1440301020710001000441c0200400c1ea147d048420 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 957350494 1250 957349244 957349301
    0xd081e0a0c030503040c05060a020a0c140f0f04020d29090709030605091e10060b0f0403020d03170106050d050604090b070509060d0501091506030b0102030f210a 71
    0x40c020a28021400001c41000001d03c220000c41e40f151080c46ea644010303440380080741007904802172010240c5d011140f20307030a1040b4041081e00801002000721220149070340803071100c039103000603240600f0f610090124282d86640581f0000031000404114420b1070001d021101d030701c030f0051050850303486148000c050038803047c8644617400b41e0716003030340c228999036a1900a100041c004559070190304002c410a074030202e0f00c0c10520304624000c0c1180e20035040c0311812142194000c104a040030400d02c0300150325034042c0c030110703078040b00e00302c020300064141500c0400341c890b11043da02c014800081601a0060003804072000c0b502020042640c40d507041c4412205c3ca0b50000c2c14403d44980001c952500c10070040900d003170041c0495003400e00a00d44001502d600380c00c2200f0b61a20b458100c0d01002144c403042005010794a400c3c0803264032070b00081c7d01c03032255246441240d00300140d0503214034440580d0302d5404604481945a03403400b102e0410003082d412046981451045e107141a840 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 957351744 1250 957350494 957350497
    0x1111c0b090402060322110109050105030f0711030421060609021602041d01090501230f0601030f14190509030f040b07050c0d0b100b0c0c040e0c0d081e 67
    0x34901400010703041e11542c08108183e000100b0358040d01500b0700c0d00c041d40030301c082c128401d00761051510034028160700001610100450b00100e04000701070080000c09880c0310000798010040e41010700f2002418030440e41940304940142501d0045403107052001c24210b020395958902400d410800b10b5212458142648a075031504144a480114108050310b0281d101e1500001c40d003031481d00200c0c5811425003900c196150598081c1d65031b40000281c0c022a1004154003010076800d904180785c0701d04190307199440a000b1504040d6903d0520034008155445000480b0316491644104e24201d91208000701041e103010348414102004206110400019110a4505004800d0415080404041568000980554442c850840039000c107480b0170b0f000305080c50140528103814507058003448114000e540c4003c0c0004000c101050b21038038045034035103a15000300c42c0460002d080d03801e61031509050350704043c0c4c4a0300650584081045060040c20040204105a10001c004000110f00c2e07 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 957352994 1250 957351744 957351761
    0xc010e060702090901022217010e06011e09020403050102031b041d0408090a06021014070c0206090d050d0c03030b040e1504170a0f17041e0c0801111c 66
    0x60058000601d855603503d03a00048042c001410b00410a40107001c0641e403440494280b04108018003440d102d48070703a001040340c507400a2040c032442510565840a05100b214040041c1031100341d02600e070442c0b86001042c031300f0800e5440e20b4070380c1040e5000b0f40c0140c1e04044123000046140682c00700440503a000c03109049034a812880141d81030800d001c2c070090003180c1901c0300b0031000e5155038903d14600b0103800640e001b84040e0176150030050442c0c1da081480460024507a040018182c2c1c06408e008007503174162440b03030b02d80d03001c0004503100d02c03081c6000408502603110280c1c1900c0d800301c22045440c2c00307903406002450222003030000311400050300e4036040c0c000030300c000c0040c01c501a0094000d880344001110311007200310342d1900b640208822000141c50340c141d500909a01c04060401806040341c0f004150605a0710454500c20360650000b200e6420040e080c2808883c11800004011b024000e101c00c240d41c40d0341070310300d50003400c965442c90021a1941a112164400c000e071 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 957354244 1250 957352994 957352999
    0x6030606100e060c0d1106150a03200a23120d05070512040905011d15130f0617011d2a21060c0c0a02060903010b06030708090c010e 58
    0x1081000c015044803062100c0919a4010b001001000d5140d00104000c810400c1176984030510310f6115000d0b00e00b015400340480c0d00c0c641042010000d0307030f40c540515804503688240781c2c0d000000141810703501c01c00d0388419607910102000000903024034010320344a0102035000e41d04445001c0713400f08004480c1902c03000e402a400071a880385450701810081c28940e000e04112407120041d01c031804090382c4a500b11503820b64940c030040000c403060b8207401c0382d580300001c202d0320741c0d241c00600e251081f404007070400d1152042c5d48420600303081c00d80c1304d061a41510942482499151001503014000401040e41550301e803541100d08001091a50350740484108041e00444403204104984071030b04600c2c070001c0d070103030034441c000c0c1c2d41d50031603103030842446480700302086a07a0030065820480000c02e1003021503c01c2080b540c91130b50116040343e181d82c2c104d13005502c8101d0300300824010004600c0040c0c01410010a00070020382020119100315119000c50740050088801128103620581c0d0458 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 957355494 1250 957354244 957354259
    0xf050411011413090c0c0f0c0e0109020702010f0c0204150e010e07170403121103090d120c02070303140d0e0f0106060306030b28061203080c311509050906030606 71
    0x40713800116002000c150b00503140881130307801d49440e847d0361014038250843d03400000100401c1596038400c0b1603401403407001001c504260450300080d0620190000302030030880c0703980d500e20866407580c1c0b000c4445009160440065625002007609580c000c0c0100306041c2d10400005210b1407245408100042e0a01401d0f0b0064841e40d505030b402c003018420110402c0c3d2148040d40c050040c8502842c13082c0a2000101445e0038100e001030000200e00350700c00c0d04142841c202c00015500003820704202c0c0c0c0c0c12b240240507905405002c2c001c0d40201c00940030501c0c00d00014181840000480003c0003407a00e00030800c90303503a03003000c0d400c8610328440100065820303c0002d04400d010030308461700c1c418807541130183e0b410100f03802c01226034a410503281a224002504103042e4050309481c0e008107a85040f40c606440013222113075001d40200c001c01280c001440c18454001e036042403900600040a28844107040c1d0340d03014040240c1c13030017041e0140545200143e020f260000d840d0b4043c28000c0c0000 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 957356744 1250 957355494 957355499
    0x15090618150c061119080406020702100327170a0215090a030921020402030603150f0a0606170411010203040305070b1c020a0e0616141c0207061202030a0f050411011413 74
    0x19905000c0c000d2050311842c0c1e02b4480742c009a26000140c61425000d641c00050504c01c005040c01c0c6484203000e00c0c1040f0340c021030024000746001551900c3c00d10034520b14ad071603440300f410481c50142200180903c0389680700510000c61030004035400c486219480b00090251610034458030a035800e08100403004076604481c01504140e40110703003283d800b4003652103222110b160618040c4040d20380d41c01e0821201e0401c143e6900707510505015000901c0e0510005501428441140301c0140002e4428004507440e100e1a0b8004c00881d40207580c4401503c820559881e00082c1c2c0d5080350741000442c1e001d0100f03c044d03100d401c0c42103400005441e244d0150100b0a5001d0081030b420010081040300c00609102001c10212120f10030003240050061106580c405c0c4d484010051902d10201598080c0e0018042550030501e240c0e66004030420058480e6140c400b050041c200f200c40d070b00510343c0b0380400e100034028a03642c40542c100081c4c80e00308040c4050350350600c00b403080f80618502c41143d061305 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 957357994 1250 957356744 957356747
    0x31e141c0f02070e0406020f03041a0601020c0108160c05100903021e100506130e0105041202070302100c0602090604060c0c0819020d05030c012415090618150c061119 73
    0x1c04d50050b0041c4c4005080c03802c07400300c81100d50300648003a100418680308900070144405d044a502180c2031003d000342c0d07005000060840540070342510707840400e180c00d240180b441a140060301d607402800712180080c82100400050141c82c40650050281610a080d1240005a4460001d48010040c42c0308224510460010300000d021180d110b000044118002d451a000382496900000000205810107103440004130b001000454107540012208102699601440341412071550418a285101c0c03031030410700910030303c81c03000e070300203000b08000c40d01d03c2d0f00569a40d0381611400c0c800c880b054480070741d51390301c0505024090000220f843d07180d0050400d4200410030380d220360300700c9080808581289094031000c1d2203040c003140c41d4a4554800b10b0645e501003000b40041c2c40042c849500d81440107044000c41d0141200380110010101c60240703203014140018002c02d0b41c10b64001003c203800070194a004103080e40c0d1941082410030b07140701190101e071201003000594000c0b000070081c0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 957359244 1250 957357994 957358019
    0xb16090b0901030608030309030904060801090206090d0809030d0c0b0f010b1804230f0703061505210a05090c0301020906090d0309090e0c0108130b01031e141c0f0207 73
    0x4a103041546544c80000c1d540310410203140100850740c05035842356015070a100c111003c1d40d00014541c0c0c1800d41280168032142c1c2141c404102c141d500c004005c00c10300b8140014401c0302581501441480c100300324460788034864142d4148984460034103030b110b0403034010506000703000d46140480c0800800d00300350907900c0c0726260703d140030300041210600000544220b9100d0400d500c0070180010400c601c42c4504a40643e005a290604000c060304100405113400c0b400200207041c414000340034000c0c0d0300040a020041e0100c0b5002c40c0d02e80c41c0241c1c02c4405010305503075541a601c00c00b04156001e284c18000d45114940c054241804d04005000300190746120403c2602807101ca803070085641401401340d0700340700c1100302c001c00741e4603808400100001801000308155400d244403e200094118404504513500030f141c071440d170082c5050041d503110005400805c100c141145c040f0540001042408921034007585200500000201c03d440039409040e40c0310060f00101014410040e0010 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 957360494 1250 957359244 957359257
    0x7050606190807080102031b030705040605090a15120c0c05060f0a060b0304080702030c040b010e120309130501080105010f2616030305130906050a290a0c0b16090b 72
    0x1951805455076500d4403a0400e43d0719000603126175000000c02810071005070784d4400481c485881240341d032400c032500500c0390046000e11810460001a00d129942d290807010001c3c000900704089000d81c002c00140000910786812013540b410003a0034000710b4091000c41c0c040c1c980240250444d581d490f24060300382c0f4070081115090766950390300892001c0c0410043e510480c41500c0841d0b6a1516004042ca04243c0c4003101e4032544c101501200c05036403004081d03d0303010041d5251813041106071100d50030b50103075110464000312060401801309420740c010904030707003030711000b0043d0b0307600c1e010348014079032907400382c0c5a207000001440ca80c0d0780c1c00b030101c94402e109028140d030001d00e40182d1002025840b5842600019008920141c0d0034003074040c444001c00245104102d441d1800d0046801c5040754415101c00416030810307803c036218001c2050710320400e00d46101c0d590314032403070014291030400c0d074050780e10b0210070002445d20103d40502c18440d10b00c544030400814035000d40b08006500c0350 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 957361744 1250 957360494 957360529
    0x3030f1b0a05070303140306100302130b03070306170607021c090b1207020d020d21060b130305151e090f010504030305011a0906030103020d0804030c03030512070507050606 76
    0x51500400300c10244a905182403140002d8a10903203581401481d030044c0c43c15150458a0420034052195602c51004d900056103040260f15145080040e114800c1036034814101240c0020401c084650715511400c06d41d803200822081c50f1944001d03e0b607640a007242d280f03001d07030702c4541c07882d000910107840e41d0002011442e011803c151194105007a0381c100710a40d50b0750216800030300100507014840c3c42d01c040e1144c40100800482000700500048510400e1003540d01c43c104c00e030210380c5e00e540203d00604905003481c2c0d540c068a1080c0d00704000a403205540c0380c01451020281c1d00c18200d40c80d8003804038400c0d460301075040b240d1740c5810020f010b0480f120a115103d0b03c00080b01c400e004082c819406506e000a40c0d40c1f401e030502460b0204407908883c00c0d901044160510394810050784d0541c0c3c1c0548658000d0f61051520358120721a80d040504000408203002042503841402090801110440c0081075211303010180d03950300410400401c550001d60005500e4244400c00200d0340c10103 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 957362994 1250 957361744 957361777
    0x60e062e08180a0809010813030e0405100b040f090e21030a09020301140a06060203040303170703270221030a1202091903110a06020d1209140307020a1403030f 70
    0x142c40d0352525240d0818021505a100800c1002c02581c0014100364028850003100c1030000003035071b0081012824060140c400c1c1c0d0303030344041059000f104138520f0240908100c400d80c3c543d1a03130010324120980d03100320000c00c0d061141866488402203010440f8520f0410261480100b55080e0314403504020a40300300696a110404096a0240500100d0340041d110703078005130034484031100545040381c00100c2903500030002000040d134086003140c0880c18403032601070300351901d400480c0a0034501d07220041104204812108003801540c1d9030000358403c13074032840a05015001144246000103026006030014000da09401c0e0060101c0130140a40c00c00051074915040c00050381c5007040c01d1954818034800313505108000e034849e8002811442210801000d905d42000295034221641c6550100503c50031400d09107110394001030380e0154070400021f41d0350000c103c0c60f5681d40126406a109414841c4000b42c1400301000800c080b0b40c0c0500990300c0c02d8004080005241c0c07000f07403e0091060b4 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 957364244 1250 957362994 957363031
    0xb0916061d010c06020f19081519030507031505090109020d06020c072301110c09220b160f030605010915110d020c090f06010c12050d060e062e08 64
    0x10244024800074003103540407507c9401d4580c03541890940c8078813540030300503040c090040703d0341d050503081404041200d020100760342044c08801d491009034030040c0b80b48100b041c04002c2101c5810443c200812400c01004160340c0e81212500361000c521003c0e400000f88991440070406940041c4100701b0070030f007150400c5035142c030344002942d48041c21502020071a04800d42c1036901c05124504008160000d2080249803400209500b002901003118280701c08411800e4400c070019036000755411143e240310502c0c1c9003100380c0c00021510b20200000d11003130707811100c090082c820714064a9040c1e481d0200d240c03d011221006d41c0c0c02803002c80038400002a075840302d030001c014040c034440c05075002c1c0c182d201222040c0661610050401890030700c841d010040180d9009000c1c0806c56000404c00f0b20b11500c0050580b1184603094450454a04084000c6000e030000151103010780b0080d110703001a51003d06550401b9018040380c02d0383d418001580c0c00c1c42c5c078840c95030160000b0240c550081c0000 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 957365494 1250 957364244 957364253
    0x709050d0609062c010e061b0c0703141b1f080a06050310060905060603092a060d0614060a0e06030c0903060907090518060610020c030a0b0916061d010c 67
    0x45045408039030a8074074000841084c60207004202a07883c5440041c5000c0c14180c64501c01681d003440d130f4605c1c407580496150b804030004c001c404011a0085203002280c0d00500d102c98a074100b0f60700340c41c4481d100d040860000d0402100c0504c201031000d05020059900e100b04440c0d010007d4040e1001c0c85e102c00010903660b44c140018070781070f000d288000440741c0c90140707420181c540040c07143d40700720002d004000c040e038000b00310051038810355158044100740550030441940c80013006590045004035000c2003d41d22507001d00280c4007541c5165000c60800c40c00c000700c0b44038284102001038103150065050b07050060180da0840c2c101070105040610b1000032914001084990103003ea02076039042008841e1803107019006105400d03401c0e04000c0700b18015130340d510064085030242c11034454560281d84240a4801d82460017819200502180d040c0b5110407071080d1101e02c1c50340204110000c541410191510442d0f14540303a413815030300304820051102d100450958180a0980754031030000c0e = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 957366744 1250 957365494 957365531
    0x90a0308063d020c061632070819020d0807020607030807120b060a0503130209070509040b0d030f110a06060902041806060504092004090c080709050d060906 69
    0x141031010400703081034403540b021858848408034200079900300c001d1040160302d0b840101c8040c581da50350682c1e981c007107a24080d00d200c500f01030440501500c102d141c030a02180c0c00f000b0041108650300f00c43d11140c4076403807983c4030340c072903240070030308008003008280181450b28104452030b010f00c0342641001419008140307154002c2c81d040740000c41401c200a01c1035081211001030b880020380412100c58500b0101c0c041d441918070040070300401000040c000c040c440c1a81c0303c07041c0d0281c602280e50404034009402c07130b0070080d40144103070300301030380c5124074146401040b40fa103805980351840d00190250584a04450703080c604540e000c0d0034a8000415418000c000c01012800d400598891138014109a0850000c00c040301041c00c0600030051198000c00340e402340c8010301800107201d80c540d00c1e01285054540502d4106450104000880f0304c5160301074500d407580b548030410103980c0e80700125407078035550040f030358010408184e007030224102da401400c11500c5064005101c0342080c1350400700 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 957367994 1250 957366744 957366799
    0x108180a06020a020c092d0c1608090406060c0b06010302161a01030b0f040b012d0b041e0303090308091c0c0303230f0f0403150b090708090a030806 65
    0x15070301403c640c1d6410306003040490791001e00070301c4a0001c00103504640e00d1036260541410030fa034411802058020200381d08449c600d840300422100b4a0550b40b40c4070301e0a400000410744200c0c60b003040061021300030346a0030103441d800306140c01280d0701e1b500154000d410034090400121030700e4001c280040c48100c00449082d03300b0580461542c035602e801920204001c2c80001001c40450900001544021003141502c049031003003140b45200311040f9030070010440b125465004086400210340e841d980040003507804940f42620b0b04215815100c000038110300c0010001425240100042001800035190744840100003080c005404250844481901a0240c4402004003010002c00d9040501c04400c08c401e102d850010703064105105900d8041c1d04094a86008001008e600d43c03080c100840b00a9903000c4110801c1440300700c07032000200302808500b80100714180204104602602000d0f203d21202e80042000980c1d5550440300c8400c003030005500020384001074012503101c914a802e1 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 957369244 1250 957367994 957367997
    0x8030a0204030605011d070c260c1018080d0f0c021f051308030a061d011406070c05060904090204020d020702190b090603041419020f010e0108180a06020a 68
    0xc481c0d055042c40e03011104107a2100c1e92840100a22a905070154600e51354400c81c00c0c03e00120030640c03070412411008800030b13884842c80761400c1035100d136007100e0040c016111030181154030b0303190400c1c400001c48190003440503184c0c82e407260005c0003501c84401820706008010001c1200411041d10409407451054001e0145e0480c890692a0448111845100380e11044091081c1e003064014960f18100490002c3d11040002000803140e035000c1e040900141410a0b50101040b442080d81d141d85100b0701952004402e850240380e043d00c0c0180640d0383c442d8125035400d91151601b010410103074841182c454000752250088809680c0754400b81c4001c80741658056922001441001304880201603580c1c820403183c8810320041c90024107541440c03400f641c0f1540d07030361124102102d1800f903c0510b10190300c02d00480308104030014111040403842642c0d07501100d5120b40041d600c020040c0e02030390020300d404000234010351243c444000040c40b01d0007a12410300c06611402d06030380c000da90020 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 957370494 1250 957369244 957369247
    0x80c12030318330a06150c05030906070c050108100e010e0a0e01110a1101050f01270c0c173108070e010807171c0917070e010501020106051c03020a08030a02 69
    0x3c00010300c4005640108140c4003003002d0f50078000741010301042045038000300305140c040201040b40403c125100c9540040c80039803683c4086c41c180c0e070f404900380262400541243c0200c1c1149e03c500040000b0b8401160400d01507a003483c40010380124014030101910791120085070000000b27104500c4041c001103000d0355196103440b400b0701030b590a11f20000c0f581e80360104000c1d54825803d4842d05440d90003117514482c801080360a1a02d0382c03c3c501d010100d034a08501416201d40101d0502e015070b100d9110b0898001e46031094140768054125102424010740c00d0b40d4922280a03100001c40003003000843c06c40c151a10103203031809083d5044001c905901400600c4039241c10003040c001080317003000120085441c0a030085c0c0fa90340d100b194036400700603404c0500190b4018038a10000d001e040030629410a90f00130000da55941c54881c11944110203400883c80f548103000d06000c1e04c1d005040040814019011240c03002c010002c140c00714003c00803e240003510700801940074000819026 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 957371744 1250 957370494 957370573
    0x60112020c060703240e060609061309050c0a1e02030d18110405041203090515150112051e0a0f090c0303110d17100e10080c12030318 59
    0x5000c032001706003c190307400c802d5002c0300e4401c0c041c440303440d0603100515140f0000f5221400891a10301580c3c603000d0b0b012801084002d4101c407288040d408860301c00741d0a00c015140e02007252400e10640360b00100150345008054124844002400c41c65130040c4101c9150081c000c07010340443e1340d1000080c6c1c0740100c1c030300c20304141304600f00c5440880d00300710f81c200b203542041d540390859022070200c90350906031506261028403006000d6510a07814441c1e54940b64a8002c0421440601f0000700364003241905900180e60281072003220701c0b51140070071307012280400d40307404100e4860003040c41c07040646910070580142d1090080c1005980b0a041d04c050450441c60064100801000110850b90144c142c0c12503da0b031102240c0401c400807a00d001d070f00d0700d4011080c5039416094000c410030002100c10300080b064410540381c205c401507001d5901d0202c42c1410024140b15400c2d00c041642d2007800414044146040103c0c003035000c82c0110b4218181c802c512804110b14080d0312150010400c0b240c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 957372994 1250 957371744 957371747
    0xf02100c0501020427020a1e1403070306030b100f050103110d110403140627030d0603230705150a1b0302011e0216170d18060606020a0507030b060112020c0607 70
    0x90605c0d031103202c07410750909a80e003030001e040030031095070550b48000c0c840c15500600e00500b4492118454003014503540c0c6000c43c0b01030b010304882d2004a1328220054005045103400e680740005030303040258140c111134030380001180034014414200c000c02c0c004010601d00d002d10352003103031500d1241000054440e403450070084110f20940c0c0000702d541c0c0005c001c000c140c1c000d4400100d08546000c524890004900d400645580a04030021000c549450302c0401400004070a0f40c014090b0503940004441740300c1c11440e142e0000c0d04c2020341010a0b01d5285410310241c20203001d110140c0d141804050030381c1a0403030900c6207409015000341c3d56401000e5609010301c041243d003024800019031030010001000004110184c030701402008460f2942d0f00720607010f8080716419141b168091004158809407180388541c81ca00c05c82d03000386000300c0003801e00e002103946144a6001009440050701d5038907024160b000003090241084000c900b98070800042d0701c00380010070340260050101d894150030 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 957374100 1106 957372994 957373049
    0x7051c05090a050c0109050105032e06120609060302033018090a05040b01030b07030b1302030702160b1b03041a0c16030f02100c05010204 61
    0x14001d1101001801446480c000e400b0355000038207079030041d5011a10382c800c2501054013800018100700d1031f0000c0d005d515503001030030001614401c207641010042a040390000c5403080f41d1b0081c8e030708020310a450241850b40010403107a402d64002030741c1e03012042c00000138190b6a11400301c015042d00c0c00102c3c6221210110364450040c501c050003003581001025001c4c51403c80052050344c0c4034000c60f406140c1004007580181d003103455001d01e50a00070556014940c4501c0d0b003503c2c6454403521824500c08103000107841e41094076000703003080a0b00514060410010005004080c48101201d0450054180d4104d002408108190031401240d100500e000b0030007480c0000c0c0c112103002071110400040503604543d02818044078000100e0001600740ca01102d2118014180048645812482420103507400786d07440e81d070a802e990050f0400440030314120110b40e0908440c81 = true := by decide +kernel

theorem cover : BRFrame.Cov 957194244 957374100 := by
  have h0 := BRFrame.cov_init 957194244
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957194244 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957194244 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957194244 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957194244 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957194244 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957194244 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957194244 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957194244 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957194244 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957194244 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957194244 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957194244 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957194244 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957194244 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957194244 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957194244 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957194244 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957194244 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957194244 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957194244 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957194244 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957194244 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957194244 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957194244 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957194244 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957194244 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957194244 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957194244 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957194244 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957194244 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957194244 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957194244 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957194244 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957194244 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957194244 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957194244 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957194244 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957194244 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957194244 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957194244 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957194244 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957194244 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957194244 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957194244 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957194244 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957194244 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957194244 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957194244 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957194244 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957194244 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957194244 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957194244 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957194244 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957194244 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957194244 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957194244 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957194244 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957194244 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957194244 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957194244 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957194244 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957194244 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957194244 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957194244 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957194244 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957194244 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957194244 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957194244 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957194244 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957194244 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957194244 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957194244 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957194244 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957194244 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957194244 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957194244 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957194244 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957194244 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957194244 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957194244 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957194244 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957194244 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957194244 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957194244 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957194244 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957194244 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957194244 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957194244 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957194244 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957194244 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957194244 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957194244 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957194244 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957194244 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957194244 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957194244 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957194244 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957194244 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957194244 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957194244 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957194244 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957194244 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957194244 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957194244 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957194244 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957194244 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957194244 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957194244 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957194244 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957194244 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957194244 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957194244 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957194244 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957194244 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957194244 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957194244 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957194244 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957194244 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957194244 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957194244 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957194244 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957194244 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957194244 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957194244 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957194244 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957194244 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957194244 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957194244 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957194244 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957194244 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957194244 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957194244 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957194244 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957194244 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957194244 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957194244 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957194244 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957194244 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957194244 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957194244 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957194244 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957194244 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957194244 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957194244 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 957194244 ≤ n) (h2 : n < 957374100) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
