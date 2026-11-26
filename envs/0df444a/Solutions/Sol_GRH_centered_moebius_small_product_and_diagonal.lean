-- Prove2me | solution 1 for GRH.centered_moebius_small_product_and_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T08:15:09.293682+00:00
-- url     : https://prove2.me/submissions/5b16a2b8-06cc-421e-8214-32e4d8968931

import Definitions.Def_GRH_MoebiusBilinear
import Mathlib.Data.Int.CardIntervalMod
import Mathlib.Analysis.PSeries
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open Finset
open scoped BigOperators

noncomputable section

private theorem residue_count_error (M v q : ℕ) (hq : 0 < q) :
    |(((Ioc 0 M).filter (fun r => r ≡ v [MOD q])).card : ℝ) - (M : ℝ) / q| ≤ 1 := by
  let x : ℚ := ((M : ℚ) - v) / q
  let y : ℚ := (0 - (v : ℚ)) / q
  have hq' : 0 < (q : ℚ) := by exact_mod_cast hq
  have hxy : y ≤ x := by
    apply div_le_div_of_nonneg_right _ hq'.le
    exact sub_le_sub_right (Nat.cast_nonneg M) _
  have hc : ((((Ioc 0 M).filter (fun r => r ≡ v [MOD q])).card : ℕ) : ℤ)
      = ⌊x⌋ - ⌊y⌋ := by
    rw [Nat.Ioc_filter_modEq_card 0 M hq v]
    simpa [x, y] using max_eq_left (sub_nonneg.mpr (Int.floor_le_floor hxy))
  have hc' : (((Ioc 0 M).filter (fun r => r ≡ v [MOD q])).card : ℚ)
      = (⌊x⌋ : ℚ) - (⌊y⌋ : ℚ) := by exact_mod_cast hc
  have hdiff : x - y = (M : ℚ) / q := by dsimp [x,y]; ring
  have hrat : |(((Ioc 0 M).filter (fun r => r ≡ v [MOD q])).card : ℚ)
      - (M : ℚ) / q| ≤ 1 := by
    rw [hc', ← hdiff, abs_le]
    constructor <;> linarith [Int.floor_le x, Int.floor_le y,
      Int.lt_floor_add_one x, Int.lt_floor_add_one y]
  simpa only [Rat.cast_abs, Rat.cast_sub, Rat.cast_natCast, Rat.cast_div, Rat.cast_one]
    using ((Rat.cast_le (K := ℝ)).mpr hrat)

private theorem progression_error (q : ℕ) [NeZero q] (a : ZMod q) (ha : IsUnit a)
    (N d e : ℕ) (hd : 0 < d) (he : 0 < e) :
    |GRH.moebiusProgressionCount q a N d e -
      (if IsUnit (d : ZMod q) ∧ IsUnit (e : ZMod q) then
         (1 / (q : ℝ)) * N / ((d : ℝ) * e) else 0)| ≤ 2 := by
  classical
  by_cases hu : IsUnit (d : ZMod q) ∧ IsUnit (e : ZMod q)
  · rw [if_pos hu]
    let u := (hu.1.mul hu.2).unit
    let b : ZMod q := (↑u⁻¹ : ZMod q) * a
    have hres (r : ℕ) : ((d * e * r : ℕ) : ZMod q) = a ↔ r ≡ b.val [MOD q] := by
      rw [← ZMod.natCast_eq_natCast_iff, ZMod.natCast_zmod_val, Nat.cast_mul, Nat.cast_mul]
      change (↑u : ZMod q) * r = a ↔ (r : ZMod q) = ↑u⁻¹ * a
      constructor
      · intro h
        rw [← h, ← mul_assoc]
        simp
      · intro h
        rw [h, ← mul_assoc]
        simp
    let m := N / (d * e)
    have hcount : |GRH.moebiusProgressionCount q a N d e - (m : ℝ) / q| ≤ 1 := by
      simpa only [GRH.moebiusProgressionCount, hres, m] using
        residue_count_error m b.val q (NeZero.pos q)
    have hk : 0 < d * e := Nat.mul_pos hd he
    have hk' : 0 < ((d * e : ℕ) : ℝ) := by exact_mod_cast hk
    have hq : 0 < (q : ℝ) := Nat.cast_pos.mpr (NeZero.pos q)
    have hq1 : 1 ≤ (q : ℝ) := by exact_mod_cast (NeZero.pos q)
    have hlo : (m : ℝ) ≤ (N : ℝ) / ((d * e : ℕ) : ℝ) := Nat.cast_div_le
    have hhi : (N : ℝ) / ((d * e : ℕ) : ℝ) ≤ (m : ℝ) + 1 := by
      apply (div_le_iff₀ hk').mpr
      rw [mul_comm]
      exact_mod_cast (Nat.lt_mul_div_succ N hk).le
    have heq : (1 / (q : ℝ)) * N / ((d : ℝ) * e) =
        ((N : ℝ) / ((d * e : ℕ) : ℝ)) / q := by push_cast; ring
    rw [heq, abs_le]
    rcases abs_le.mp hcount with ⟨hl, hh⟩
    have hi := div_le_div_of_nonneg_right hhi hq.le
    have lo := div_le_div_of_nonneg_right hlo hq.le
    rw [add_div] at hi
    have hrec : 1 / (q : ℝ) ≤ 1 := (div_le_one hq).2 hq1
    constructor <;> linarith
  · rw [if_neg hu]
    have hempty : ((Ioc 0 (N / (d * e))).filter (fun r => ((d * e * r : ℕ) : ZMod q) = a)) = ∅ := by
      apply filter_eq_empty_iff.mpr
      intro r _ hr
      have hunit : IsUnit (((d : ZMod q) * e) * r) := by simpa only [← Nat.cast_mul, hr] using ha
      exact hu (IsUnit.mul_iff.mp (isUnit_of_mul_isUnit_left hunit))
    rw [GRH.moebiusProgressionCount, hempty]
    norm_num

private def summand (q : ℕ) [NeZero q] (a : ZMod q) (N d e : ℕ) : ℝ :=
  (ArithmeticFunction.moebius d : ℝ) * (ArithmeticFunction.moebius e : ℝ) *
    (GRH.moebiusProgressionCount q a N d e -
      if IsUnit (d : ZMod q) ∧ IsUnit (e : ZMod q) then
        (1 / (q : ℝ)) * N / ((d : ℝ) * e) else 0)

private theorem summand_bound (q : ℕ) [NeZero q] (a : ZMod q) (ha : IsUnit a)
    (N d e : ℕ) (hd : 0 < d) (he : 0 < e) : |summand q a N d e| ≤ 2 := by
  have hmu (k : ℕ) : |(ArithmeticFunction.moebius k : ℝ)| ≤ 1 := by
    exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := k))
  unfold summand
  rw [abs_mul, abs_mul]
  calc
    _ ≤ (1 * 1 : ℝ) * 2 :=
      mul_le_mul (mul_le_mul (hmu d) (hmu e) (abs_nonneg _) zero_le_one)
        (progression_error q a ha N d e hd he) (abs_nonneg _) (by norm_num)
    _ = 2 := by norm_num


theorem solution (σ : ℝ) (hhalf : (1/2 : ℝ) < σ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (q : ℕ) [NeZero q] (a : ZMod q), IsUnit a → ∀ N : ℕ,
      (∑ d ∈ Ioc 0 N.sqrt,
        ∑ e ∈ (Ioc 0 N.sqrt).filter (fun e => d * e ≤ N.sqrt ∨ d = e),
          |(ArithmeticFunction.moebius d : ℝ) * (ArithmeticFunction.moebius e : ℝ) *
          (GRH.moebiusProgressionCount q a N d e -
            if IsUnit (d : ZMod q) ∧ IsUnit (e : ZMod q) then
              (1 / (q : ℝ)) * N / ((d : ℝ) * e) else 0)|) ≤ K * ((N : ℝ) + 1) ^ σ := by 
  classical
  let w (d : ℕ) := ((d : ℝ) ^ (2 * σ))⁻¹
  have hw (d : ℕ) : 0 ≤ w d := inv_nonneg.mpr (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hs : Summable w := Real.summable_nat_rpow_inv.mpr (by linarith)
  refine ⟨4 * ∑' d, w d, mul_nonneg (by norm_num) (tsum_nonneg hw), ?_⟩
  intro q _ a ha N
  let U := N.sqrt
  let S := Ioc 0 U
  let B := ((N : ℝ) + 1) ^ σ
  have hB : 0 ≤ B := Real.rpow_nonneg (by positivity) _
  change (∑ d ∈ S, ∑ e ∈ S.filter (fun e => d * e ≤ U ∨ d = e),
    |summand q a N d e|) ≤ (4 * ∑' d, w d) * B
  have hpow : (U : ℝ) ^ (2 * σ) ≤ B := by
    rw [← Nat.cast_ofNat (R := ℝ) (n := 2), Real.rpow_natCast_mul (Nat.cast_nonneg U)]
    apply Real.rpow_le_rpow (sq_nonneg _) _ (by linarith)
    have hn : (U : ℝ)^2 ≤ (N : ℝ) := by exact_mod_cast (Nat.sqrt_le' N)
    linarith
  have hrow (d : ℕ) (hd : d ∈ S) :
      (∑ e ∈ S.filter (fun e => d * e ≤ U ∨ d = e), |summand q a N d e|)
        ≤ (4 * B) * w d := by
    obtain ⟨hd0, hdu⟩ := mem_Ioc.mp hd
    have hsub : S.filter (fun e => d * e ≤ U ∨ d = e) ⊆ Ioc 0 (U / d) ∪ {d} := by
      intro e he
      obtain ⟨heS, h⟩ := mem_filter.mp he
      rcases h with h | rfl
      · exact mem_union_left _ (mem_Ioc.mpr ⟨(mem_Ioc.mp heS).1,
          (Nat.le_div_iff_mul_le hd0).mpr (by simpa [Nat.mul_comm] using h)⟩)
      · exact mem_union_right _ (mem_singleton_self d)
    have hcard : (S.filter (fun e => d * e ≤ U ∨ d = e)).card ≤ U / d + 1 := by
      simpa using (card_le_card hsub).trans (card_union_le _ _)
    have hd' : 0 < (d : ℝ) := by exact_mod_cast hd0
    have hone : (1 : ℝ) ≤ (U : ℝ) / d := (one_le_div hd').mpr (by exact_mod_cast hdu)
    have hdiv : ((U / d : ℕ) : ℝ) ≤ (U : ℝ) / d := Nat.cast_div_le
    have hweight : (U : ℝ) / d ≤ B * w d := calc
      _ ≤ ((U : ℝ) / d) ^ (2 * σ) := Real.self_le_rpow_of_one_le hone (by linarith)
      _ = (U : ℝ) ^ (2 * σ) * w d := by rw [Real.div_rpow (Nat.cast_nonneg U) hd'.le, div_eq_mul_inv]
      _ ≤ B * w d := mul_le_mul_of_nonneg_right hpow (hw d)
    calc
      _ ≤ ∑ e ∈ S.filter (fun e => d * e ≤ U ∨ d = e), (2 : ℝ) := by
        apply sum_le_sum
        intro e he
        exact summand_bound q a ha N d e hd0 (mem_Ioc.mp (mem_filter.mp he).1).1
      _ = ((S.filter (fun e => d * e ≤ U ∨ d = e)).card : ℝ) * 2 := by simp
      _ ≤ (((U / d : ℕ) : ℝ) + 1) * 2 := by
        apply mul_le_mul_of_nonneg_right _ (by norm_num)
        exact_mod_cast hcard
      _ ≤ (4 * B) * w d := by linarith
  calc
    _ ≤ ∑ d ∈ S, (4 * B) * w d := sum_le_sum hrow
    _ = (4 * B) * ∑ d ∈ S, w d := (mul_sum ..).symm
    _ ≤ (4 * B) * ∑' d, w d :=
      mul_le_mul_of_nonneg_left (hs.sum_le_tsum S (fun d _ => hw d)) (by positivity)
    _ = _ := by ring
