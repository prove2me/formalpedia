-- Prove2me | solution 1 for CarryRNG.SWB.period_eq_orderOf
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-11T20:08:09.047909+00:00
-- url     : https://prove2.me/submissions/693549c3-595a-4aa2-8e5b-7952d84ec9e8

import Mathlib
import Definitions.Def_CarryRNG_SWB_step
import Definitions.Def_CarryRNG_SWB_modulus
import Definitions.Def_CarryRNG_AWC_zeroSeed
import Definitions.Def_CarryRNG_AWC_topSeed

set_option autoImplicit false

namespace CarryRNG.SWB.P647

/-- digit `i` as a natural number, zero outside the range -/
def dig {b r : ℕ} (w : CarryRNG.AWC.State b r) (i : ℕ) : ℕ :=
  if h : i < r then ((w.x ⟨i, h⟩ : Fin b) : ℕ) else 0

def X {b r : ℕ} (w : CarryRNG.AWC.State b r) : ℕ := ∑ i ∈ Finset.range r, dig w i * b ^ i

def H {b r : ℕ} (s : ℕ) (w : CarryRNG.AWC.State b r) : ℕ :=
  ∑ j ∈ Finset.range s, dig w (r - s + j) * b ^ j

def V {b r : ℕ} (s : ℕ) (w : CarryRNG.AWC.State b r) : ℕ := X w - H s w + (w.c : ℕ)

/-- generic digit sums -/
def XS (b : ℕ) (f : ℕ → ℕ) (n : ℕ) : ℕ := ∑ i ∈ Finset.range n, f i * b ^ i

lemma dig_lt {b r : ℕ} (hb : 0 < b) (w : CarryRNG.AWC.State b r) (i : ℕ) : dig w i < b := by
  unfold dig; split_ifs
  · exact (w.x _).isLt
  · exact hb

lemma dig_ge {b r : ℕ} (w : CarryRNG.AWC.State b r) (i : ℕ) (hi : r ≤ i) : dig w i = 0 := by
  unfold dig; rw [dif_neg (by omega)]

lemma X_eq {b r : ℕ} (w : CarryRNG.AWC.State b r) : X w = XS b (dig w) r := rfl

lemma H_eq {b r : ℕ} (s : ℕ) (w : CarryRNG.AWC.State b r) :
    H s w = XS b (fun j => dig w (r - s + j)) s := rfl

lemma geom (b n : ℕ) (hb : 1 ≤ b) : ∑ i ∈ Finset.range n, (b - 1) * b ^ i + 1 = b ^ n := by
  obtain ⟨c, rfl⟩ : ∃ c, b = c + 1 := ⟨b - 1, by omega⟩
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, pow_succ]
    simp only [Nat.add_sub_cancel] at ih ⊢
    rw [show ∑ i ∈ Finset.range n, c * (c + 1) ^ i + c * (c + 1) ^ n + 1 =
      (∑ i ∈ Finset.range n, c * (c + 1) ^ i + 1) + c * (c + 1) ^ n by ring, ih]
    ring

lemma compl (b n : ℕ) (hb : 1 ≤ b) (f : ℕ → ℕ) (hf : ∀ i, f i < b) :
    XS b (fun i => b - 1 - f i) n + XS b f n + 1 = b ^ n := by
  rw [← geom b n hb]
  unfold XS
  rw [← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  have := hf i
  rw [← add_mul, Nat.sub_add_cancel (by omega)]

lemma split_sum (b r s : ℕ) (f : ℕ → ℕ) (hsr : s ≤ r) :
    XS b f r = ∑ i ∈ Finset.range (r - s), f i * b ^ i +
      ∑ j ∈ Finset.range s, f (r - s + j) * b ^ (r - s + j) := by
  unfold XS
  have e := Finset.sum_range_add (fun i => f i * b ^ i) (r - s) s
  rw [Nat.sub_add_cancel hsr] at e
  exact e

lemma HS_le (b r s : ℕ) (hb : 1 ≤ b) (f : ℕ → ℕ) (hsr : s ≤ r) :
    XS b (fun j => f (r - s + j)) s ≤ XS b f r := by
  rw [split_sum b r s f hsr]
  have : XS b (fun j => f (r - s + j)) s ≤
      ∑ j ∈ Finset.range s, f (r - s + j) * b ^ (r - s + j) := by
    unfold XS
    apply Finset.sum_le_sum
    intro j _
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hb (by omega))
  omega

lemma digsum_zero (b n : ℕ) (hb : 0 < b) (f : ℕ → ℕ)
    (he : ∑ i ∈ Finset.range n, f i * b ^ i = 0) : ∀ i < n, f i = 0 := by
  intro i hi
  rw [Finset.sum_eq_zero_iff] at he
  have := he i (Finset.mem_range.mpr hi)
  rcases Nat.mul_eq_zero.mp this with h | h
  · exact h
  · exact absurd h (pow_ne_zero _ (by omega))

lemma HS_eq (b r s : ℕ) (hb : 2 ≤ b) (f : ℕ → ℕ) (hsr : s < r)
    (he : XS b f r = XS b (fun j => f (r - s + j)) s) : ∀ i < r, f i = 0 := by
  rw [split_sum b r s f hsr.le] at he
  have hle : ∀ j ∈ Finset.range s, f (r - s + j) * b ^ j ≤ f (r - s + j) * b ^ (r - s + j) :=
    fun j _ => Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega))
  have hsum := Finset.sum_le_sum hle
  unfold XS at he
  beta_reduce at he
  have hA : ∑ i ∈ Finset.range (r - s), f i * b ^ i = 0 := by omega
  have hB : ∑ j ∈ Finset.range s, f (r - s + j) * b ^ j =
      ∑ j ∈ Finset.range s, f (r - s + j) * b ^ (r - s + j) := by omega
  rw [Finset.sum_eq_sum_iff_of_le hle] at hB
  intro i hi
  by_cases h1 : i < r - s
  · exact digsum_zero b (r - s) (by omega) f hA i h1
  · have hj := hB (i - (r - s)) (Finset.mem_range.mpr (by omega))
    rw [show r - s + (i - (r - s)) = i by omega] at hj
    have hlt : b ^ (i - (r - s)) < b ^ i := Nat.pow_lt_pow_right (by omega) (by omega)
    rcases Nat.eq_zero_or_pos (f i) with h0 | hpos
    · exact h0
    · exfalso
      have := (Nat.mul_lt_mul_left hpos).mpr hlt
      omega

lemma H_le_X {b r : ℕ} (hb : 1 ≤ b) (s : ℕ) (hsr : s ≤ r) (w : CarryRNG.AWC.State b r) :
    H s w ≤ X w := by
  rw [H_eq, X_eq]; exact HS_le b r s hb (dig w) hsr

lemma state_ext {b r : ℕ} (w w' : CarryRNG.AWC.State b r) (hd : ∀ i, dig w i = dig w' i)
    (hc : (w.c : ℕ) = w'.c) : w = w' := by
  cases w with
  | mk x c =>
    cases w' with
    | mk x' c' =>
      simp only [CarryRNG.AWC.State.mk.injEq]
      refine ⟨?_, Fin.ext hc⟩
      funext i
      apply Fin.ext
      have := hd i.val
      simpa [dig, i.isLt] using this

lemma V_le {b r : ℕ} (hb : 1 ≤ b) (s : ℕ) (hsr : s ≤ r) (w : CarryRNG.AWC.State b r) :
    V s w ≤ b ^ r - b ^ s + 1 := by
  have hf : ∀ i, dig w i < b := dig_lt (by omega) w
  have c1 := compl b r hb (dig w) hf
  have c2 := compl b s hb (fun j => dig w (r - s + j)) (fun j => hf _)
  have l1 := HS_le b r s hb (dig w) hsr
  have l2 := HS_le b r s hb (fun i => b - 1 - dig w i) hsr
  have h3 := w.c.isLt
  unfold V; rw [X_eq, H_eq]
  omega

lemma V_zero {b r : ℕ} (hb : 2 ≤ b) (s : ℕ) (hsr : s < r) (w : CarryRNG.AWC.State b r)
    (h : V s w = 0) : w = CarryRNG.AWC.zeroSeed b r hb := by
  have l1 := H_le_X (by omega : 1 ≤ b) s hsr.le w
  unfold V at h
  have hX : X w = H s w := by omega
  have hc : (w.c : ℕ) = 0 := by omega
  rw [X_eq, H_eq] at hX
  have hd := HS_eq b r s hb (dig w) hsr hX
  apply state_ext
  · intro i
    by_cases hi : i < r
    · rw [hd i hi]; simp [dig, CarryRNG.AWC.zeroSeed, hi]
    · rw [dig_ge _ _ (by omega), dig_ge _ _ (by omega)]
  · rw [hc]; simp [CarryRNG.AWC.zeroSeed]

lemma V_top {b r : ℕ} (hb : 2 ≤ b) (s : ℕ) (hsr : s < r) (w : CarryRNG.AWC.State b r)
    (h : V s w = b ^ r - b ^ s + 1) : w = CarryRNG.AWC.topSeed b r hb := by
  have hb1 : 1 ≤ b := by omega
  have hf : ∀ i, dig w i < b := dig_lt (by omega) w
  have c1 := compl b r hb1 (dig w) hf
  have c2 := compl b s hb1 (fun j => dig w (r - s + j)) (fun j => hf _)
  have l1 := HS_le b r s hb1 (dig w) hsr.le
  have l2 := HS_le b r s hb1 (fun i => b - 1 - dig w i) hsr.le
  have h3 := w.c.isLt
  unfold V at h; rw [X_eq, H_eq] at h
  have hX : XS b (fun i => b - 1 - dig w i) r =
      XS b (fun j => (fun i => b - 1 - dig w i) (r - s + j)) s := by
    beta_reduce at l2 c2 ⊢; omega
  have hc : (w.c : ℕ) = 1 := by omega
  have hd := HS_eq b r s hb (fun i => b - 1 - dig w i) hsr hX
  apply state_ext
  · intro i
    by_cases hi : i < r
    · have e := hd i hi
      have := hf i
      have e2 : dig w i = b - 1 := by omega
      rw [e2]; simp [dig, CarryRNG.AWC.topSeed, hi]
    · rw [dig_ge _ _ (by omega), dig_ge _ _ (by omega)]
  · rw [hc]; simp [CarryRNG.AWC.topSeed]

lemma step_dig (b : ℕ) (L : CarryRNG.AWC.Lags) (hb : 2 ≤ b) (z : CarryRNG.AWC.State b L.r)
    (i : ℕ) (h : i + 1 < L.r) :
    dig (step b L hb z) i = dig z (i + 1) := by
  have hi : i < L.r := by omega
  simp only [dig, dif_pos hi, dif_pos h]
  simp [step, h]

lemma step_carry (b : ℕ) (L : CarryRNG.AWC.Lags) (hb : 2 ≤ b) (z : CarryRNG.AWC.State b L.r) :
    dig (step b L hb z) (L.r - 1) + dig z 0 + (z.c : ℕ) =
      dig z (L.r - L.s) + b * ((step b L hb z).c : ℕ) := by
  have hs := L.hs
  have hsr := L.hsr
  have h1 : L.r - 1 < L.r := by omega
  have h2 : ¬ (L.r - 1 + 1 < L.r) := by omega
  have h3 : L.r - L.s < L.r := by omega
  have h4 : 0 < L.r := by omega
  have hc := z.c.isLt
  have hx1 := (z.x ⟨0, h4⟩).isLt
  have hx2 := (z.x ⟨L.r - L.s, h3⟩).isLt
  simp only [dig, dif_pos h1, dif_pos h3, dif_pos h4]
  simp only [step, h2, dif_neg, not_false_eq_true]
  split_ifs with ht <;> simp_all <;> omega

lemma step_key (b : ℕ) (L : CarryRNG.AWC.Lags) (hb : 2 ≤ b) (z : CarryRNG.AWC.State b L.r) :
    b * V L.s (step b L hb z) = V L.s z + dig (step b L hb z) (L.r - 1) * modulus b L := by
  have hs := L.hs
  have hsr := L.hsr
  have hr : 1 ≤ L.r := by omega
  have hs1 : 1 ≤ L.s := by omega
  set d := dig (step b L hb z) (L.r - 1) with hd
  have hX1 : X (step b L hb z) =
      (∑ i ∈ Finset.range (L.r - 1), dig z (i + 1) * b ^ i) + d * b ^ (L.r - 1) := by
    unfold X
    have e := Finset.sum_range_succ (fun i => dig (step b L hb z) i * b ^ i) (L.r - 1)
    rw [Nat.sub_add_cancel hr] at e
    rw [e]; congr 1
    apply Finset.sum_congr rfl; intro i hi; rw [Finset.mem_range] at hi
    rw [step_dig b L hb z i (by omega)]
  have hX2 : X z = (∑ i ∈ Finset.range (L.r - 1), dig z (i + 1) * b ^ (i + 1)) + dig z 0 := by
    unfold X
    have e := Finset.sum_range_succ' (fun i => dig z i * b ^ i) (L.r - 1)
    rw [Nat.sub_add_cancel hr] at e
    rw [e]; simp
  have hH1 : H L.s (step b L hb z) =
      (∑ j ∈ Finset.range (L.s - 1), dig z (L.r - L.s + j + 1) * b ^ j) + d * b ^ (L.s - 1) := by
    unfold H
    have e := Finset.sum_range_succ
      (fun j => dig (step b L hb z) (L.r - L.s + j) * b ^ j) (L.s - 1)
    rw [Nat.sub_add_cancel hs1] at e
    rw [e]; congr 1
    · apply Finset.sum_congr rfl; intro j hj; rw [Finset.mem_range] at hj
      rw [step_dig b L hb z _ (by omega)]
    · rw [show L.r - L.s + (L.s - 1) = L.r - 1 by omega]
  have hH2 : H L.s z =
      (∑ j ∈ Finset.range (L.s - 1), dig z (L.r - L.s + j + 1) * b ^ (j + 1)) +
        dig z (L.r - L.s) := by
    unfold H
    have e := Finset.sum_range_succ' (fun j => dig z (L.r - L.s + j) * b ^ j) (L.s - 1)
    rw [Nat.sub_add_cancel hs1] at e
    rw [e]; simp only [add_zero, pow_zero, mul_one]; rfl
  have hXb : b * X (step b L hb z) + dig z 0 = X z + d * b ^ L.r := by
    rw [hX1, hX2, mul_add, Finset.mul_sum]
    have hp : b ^ L.r = b ^ (L.r - 1) * b := by rw [← pow_succ, Nat.sub_add_cancel hr]
    rw [hp]
    have hsum : ∑ i ∈ Finset.range (L.r - 1), b * (dig z (i + 1) * b ^ i) =
        ∑ i ∈ Finset.range (L.r - 1), dig z (i + 1) * b ^ (i + 1) :=
      Finset.sum_congr rfl (fun i _ => by ring)
    rw [hsum]; ring
  have hHb : b * H L.s (step b L hb z) + dig z (L.r - L.s) = H L.s z + d * b ^ L.s := by
    rw [hH1, hH2, mul_add, Finset.mul_sum]
    have hp : b ^ L.s = b ^ (L.s - 1) * b := by rw [← pow_succ, Nat.sub_add_cancel hs1]
    rw [hp]
    have hsum : ∑ j ∈ Finset.range (L.s - 1), b * (dig z (L.r - L.s + j + 1) * b ^ j) =
        ∑ j ∈ Finset.range (L.s - 1), dig z (L.r - L.s + j + 1) * b ^ (j + 1) :=
      Finset.sum_congr rfl (fun i _ => by ring)
    rw [hsum]; ring
  have hc := step_carry b L hb z
  rw [← hd] at hc
  have l1 := H_le_X (by omega : 1 ≤ b) L.s hsr.le z
  have l2 := H_le_X (by omega : 1 ≤ b) L.s hsr.le (step b L hb z)
  have hbs : b ^ L.s ≤ b ^ L.r := Nat.pow_le_pow_right (by omega) hsr.le
  unfold V modulus
  zify [l1, l2, hbs] at hXb hHb hc ⊢
  linear_combination hXb - hHb - hc

lemma cast_key (b : ℕ) (L : CarryRNG.AWC.Lags) (hb : 2 ≤ b) (z : CarryRNG.AWC.State b L.r) :
    ((b : ZMod (modulus b L)) * (V L.s (step b L hb z) : ZMod (modulus b L))) =
      (V L.s z : ZMod (modulus b L)) := by
  have hk := step_key b L hb z
  have := congrArg (fun n : ℕ => (n : ZMod (modulus b L))) hk
  simpa [Nat.cast_mul, Nat.cast_add, ZMod.natCast_self] using this

lemma iter_key (b : ℕ) (L : CarryRNG.AWC.Lags) (hb : 2 ≤ b) (k : ℕ)
    (z : CarryRNG.AWC.State b L.r) :
    ((b : ZMod (modulus b L)) ^ k * (V L.s ((step b L hb)^[k] z) : ZMod (modulus b L))) =
      (V L.s z : ZMod (modulus b L)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', pow_succ, mul_assoc, cast_key b L hb _, ih]

lemma iter_dig (b : ℕ) (L : CarryRNG.AWC.Lags) (hb : 2 ≤ b) (w : CarryRNG.AWC.State b L.r)
    (j : ℕ) :
    ∀ n i, i + n < L.r → dig ((step b L hb)^[j + n] w) i = dig ((step b L hb)^[j] w) (i + n) := by
  intro n
  induction n with
  | zero => intro i _; simp
  | succ n ih =>
    intro i hi
    rw [← Nat.add_assoc, Function.iterate_succ_apply', step_dig b L hb _ i (by omega),
      ih (i + 1) (by omega)]
    congr 1; omega

/-- backward uniqueness: a potential strictly between `0` and `m` determines its predecessor -/
lemma back (b : ℕ) (L : CarryRNG.AWC.Lags) (hb : 2 ≤ b) (w w' : CarryRNG.AWC.State b L.r)
    (hw : 0 < V L.s w ∧ V L.s w < modulus b L) (hw' : 0 < V L.s w' ∧ V L.s w' < modulus b L)
    (he : V L.s (step b L hb w) = V L.s (step b L hb w')) :
    V L.s w = V L.s w' ∧ dig (step b L hb w) (L.r - 1) = dig (step b L hb w') (L.r - 1) := by
  have k1 := step_key b L hb w
  have k2 := step_key b L hb w'
  set m := modulus b L
  set d := dig (step b L hb w) (L.r - 1)
  set d' := dig (step b L hb w') (L.r - 1)
  have e1 : b * V L.s (step b L hb w) = V L.s w + m * d := by rw [k1, mul_comm d m]
  have e2 : b * V L.s (step b L hb w') = V L.s w' + m * d' := by rw [k2, mul_comm d' m]
  rw [he] at e1
  have hmpos : 0 < m := by omega
  have em : V L.s w = V L.s w' := by
    have a1 : (V L.s w + m * d) % m = V L.s w := by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hw.2]
    have a2 : (V L.s w' + m * d') % m = V L.s w' := by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hw'.2]
    rw [← a1, ← a2, ← e1, ← e2]
  refine ⟨em, ?_⟩
  have a1 : (V L.s w + m * d) / m = d := by
    rw [Nat.add_mul_div_left _ _ hmpos, Nat.div_eq_of_lt hw.2, zero_add]
  have a2 : (V L.s w' + m * d') / m = d' := by
    rw [Nat.add_mul_div_left _ _ hmpos, Nat.div_eq_of_lt hw'.2, zero_add]
  rw [← a1, ← a2, ← e1, ← e2]

end CarryRNG.SWB.P647

open CarryRNG.SWB in
theorem solution (b : ℕ) (L : CarryRNG.AWC.Lags) (hb : 2 ≤ b)
    (hm : (modulus b L).Prime) (z : CarryRNG.AWC.State b L.r)
    (hzero : z ≠ CarryRNG.AWC.zeroSeed b L.r hb) (htop : z ≠ CarryRNG.AWC.topSeed b L.r hb) :
    Function.minimalPeriod (step b L hb) ((step b L hb)^[L.r] z) =
      orderOf (b : ZMod (modulus b L)) := by
  have hb0 : 0 < b := by omega
  have hs := L.hs
  have hsr := L.hsr
  have : Fact (modulus b L).Prime := ⟨hm⟩
  have hmdef : modulus b L = b ^ L.r - b ^ L.s + 1 := rfl
  have hbm : b < modulus b L := by
    have e1 : b ^ L.s * b ≤ b ^ L.r := by
      rw [← pow_succ]; exact Nat.pow_le_pow_right hb0 (by omega)
    have e2 : b ^ 1 ≤ b ^ L.s := Nat.pow_le_pow_right hb0 hs
    rw [pow_one] at e2
    have e3 : b ^ L.s * 2 ≤ b ^ L.s * b := Nat.mul_le_mul_left _ hb
    omega
  have hbz : (b : ZMod (modulus b L)) ≠ 0 := by
    intro h
    rw [ZMod.natCast_eq_zero_iff] at h
    exact absurd (Nat.le_of_dvd hb0 h) (by omega)
  have Vle : ∀ w : CarryRNG.AWC.State b L.r, P647.V L.s w ≤ modulus b L := by
    intro w; rw [hmdef]; exact P647.V_le (by omega) L.s hsr.le w
  have range_of : ∀ w : CarryRNG.AWC.State b L.r, (P647.V L.s w : ZMod (modulus b L)) ≠ 0 →
      0 < P647.V L.s w ∧ P647.V L.s w < modulus b L := by
    intro w hw
    have hle := Vle w
    refine ⟨Nat.pos_of_ne_zero (fun h => hw (by rw [h]; simp)), ?_⟩
    rcases lt_or_eq_of_le hle with h | h
    · exact h
    · exact absurd (by rw [h]; exact ZMod.natCast_self _) hw
  have hz : (P647.V L.s z : ZMod (modulus b L)) ≠ 0 := by
    intro h
    rw [ZMod.natCast_eq_zero_iff] at h
    obtain ⟨k, hk⟩ := h
    have hle := Vle z
    rcases Nat.lt_or_ge k 1 with hk1 | hk1
    · have hk0 : k = 0 := by omega
      subst hk0
      exact hzero (P647.V_zero hb L.s hsr z (by simpa using hk))
    · have hk2 : k = 1 := by
        by_contra hne
        have : modulus b L * 2 ≤ modulus b L * k := Nat.mul_le_mul_left _ (by omega)
        omega
      subst hk2
      exact htop (P647.V_top hb L.s hsr z (by rw [hk, mul_one, hmdef]))
  have hiter : ∀ w : CarryRNG.AWC.State b L.r, (P647.V L.s w : ZMod (modulus b L)) ≠ 0 →
      ∀ j, (P647.V L.s ((step b L hb)^[j] w) : ZMod (modulus b L)) ≠ 0 := by
    intro w hw j h
    have := P647.iter_key b L hb j w
    rw [h, mul_zero] at this
    exact hw this.symm
  have chain : ∀ u u' : CarryRNG.AWC.State b L.r, (P647.V L.s u : ZMod (modulus b L)) ≠ 0 →
      (P647.V L.s u' : ZMod (modulus b L)) ≠ 0 →
      P647.V L.s ((step b L hb)^[L.r] u) = P647.V L.s ((step b L hb)^[L.r] u') →
      (step b L hb)^[L.r] u = (step b L hb)^[L.r] u' := by
    intro u u' hu hu' he
    have hV : ∀ i ≤ L.r, P647.V L.s ((step b L hb)^[L.r - i] u) =
        P647.V L.s ((step b L hb)^[L.r - i] u') := by
      intro i
      induction i with
      | zero => intro _; simpa using he
      | succ i ih =>
        intro hi
        have e := ih (by omega)
        have hk : L.r - i = (L.r - (i + 1)) + 1 := by omega
        rw [hk, Function.iterate_succ_apply', Function.iterate_succ_apply'] at e
        exact (P647.back b L hb _ _ (range_of _ (hiter u hu _))
          (range_of _ (hiter u' hu' _)) e).1
    have hV' : ∀ j ≤ L.r, P647.V L.s ((step b L hb)^[j] u) =
        P647.V L.s ((step b L hb)^[j] u') := by
      intro j hj
      have := hV (L.r - j) (by omega)
      rwa [Nat.sub_sub_self hj] at this
    have hD : ∀ j < L.r, P647.dig ((step b L hb)^[j + 1] u) (L.r - 1) =
        P647.dig ((step b L hb)^[j + 1] u') (L.r - 1) := by
      intro j hj
      have e := hV' (j + 1) (by omega)
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply'] at e ⊢
      exact (P647.back b L hb _ _ (range_of _ (hiter u hu _))
        (range_of _ (hiter u' hu' _)) e).2
    have hdig : ∀ i, P647.dig ((step b L hb)^[L.r] u) i =
        P647.dig ((step b L hb)^[L.r] u') i := by
      intro i
      by_cases hi : i < L.r
      · have a := P647.iter_dig b L hb u (i + 1) (L.r - 1 - i) i (by omega)
        have a' := P647.iter_dig b L hb u' (i + 1) (L.r - 1 - i) i (by omega)
        rw [show i + 1 + (L.r - 1 - i) = L.r by omega,
          show i + (L.r - 1 - i) = L.r - 1 by omega] at a a'
        rw [a, a', hD i hi]
      · rw [P647.dig_ge _ _ (by omega), P647.dig_ge _ _ (by omega)]
    apply P647.state_ext _ _ hdig
    have hXe : P647.X ((step b L hb)^[L.r] u) = P647.X ((step b L hb)^[L.r] u') := by
      unfold P647.X; exact Finset.sum_congr rfl (fun i _ => by rw [hdig i])
    have hHe : P647.H L.s ((step b L hb)^[L.r] u) = P647.H L.s ((step b L hb)^[L.r] u') := by
      unfold P647.H; exact Finset.sum_congr rfl (fun i _ => by rw [hdig])
    have := hV' L.r le_rfl
    unfold P647.V at this
    omega
  have hpow1 : (b : ZMod (modulus b L)) ^ (modulus b L - 1) = 1 :=
    ZMod.pow_card_sub_one_eq_one hbz
  have hfin : IsOfFinOrder (b : ZMod (modulus b L)) :=
    isOfFinOrder_iff_pow_eq_one.mpr ⟨modulus b L - 1, by omega, hpow1⟩
  have hper : Function.IsPeriodicPt (step b L hb) (orderOf (b : ZMod (modulus b L)))
      ((step b L hb)^[L.r] z) := by
    show (step b L hb)^[orderOf (b : ZMod (modulus b L))] ((step b L hb)^[L.r] z) =
      (step b L hb)^[L.r] z
    have hcomm : (step b L hb)^[orderOf (b : ZMod (modulus b L))] ((step b L hb)^[L.r] z) =
        (step b L hb)^[L.r] ((step b L hb)^[orderOf (b : ZMod (modulus b L))] z) := by
      rw [← Function.iterate_add_apply, ← Function.iterate_add_apply, add_comm]
    have hz' := hiter z hz (orderOf (b : ZMod (modulus b L)))
    have k := P647.iter_key b L hb (orderOf (b : ZMod (modulus b L))) ((step b L hb)^[L.r] z)
    rw [pow_orderOf_eq_one, one_mul, hcomm] at k
    have r1 := range_of _ (hiter _ hz' L.r)
    have r2 := range_of _ (hiter z hz L.r)
    have hVeq := (ZMod.natCast_eq_natCast_iff' _ _ _).mp k
    rw [Nat.mod_eq_of_lt r1.2, Nat.mod_eq_of_lt r2.2] at hVeq
    rw [hcomm]
    exact chain _ _ hz' hz hVeq
  have hdvd1 := hper.minimalPeriod_dvd
  have hpp := Function.isPeriodicPt_minimalPeriod (step b L hb) ((step b L hb)^[L.r] z)
  have hdvd2 : orderOf (b : ZMod (modulus b L)) ∣
      Function.minimalPeriod (step b L hb) ((step b L hb)^[L.r] z) := by
    apply orderOf_dvd_of_pow_eq_one
    have k := P647.iter_key b L hb (Function.minimalPeriod (step b L hb) ((step b L hb)^[L.r] z))
      ((step b L hb)^[L.r] z)
    rw [hpp.eq] at k
    have hy0 := hiter z hz L.r
    have hmul : ((b : ZMod (modulus b L)) ^ Function.minimalPeriod (step b L hb)
        ((step b L hb)^[L.r] z) - 1) *
          (P647.V L.s ((step b L hb)^[L.r] z) : ZMod (modulus b L)) = 0 := by
      rw [sub_mul, k, one_mul, sub_self]
    rcases mul_eq_zero.mp hmul with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hy0
  exact Nat.dvd_antisymm hdvd1 hdvd2
