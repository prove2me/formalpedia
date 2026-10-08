-- Prove2me | solution 1 for ConvexOptimization.leindler_supremal_integral_real_line
-- status  : ACCEPTED   (prove)
-- author  : @Yifan Hong
-- created : 2026-08-15T05:12:31.140328+00:00
-- url     : https://prove2.me/submissions/7e830a42-3a66-4ec7-906b-d8c34a35eeed

import Mathlib
import Theorems.Thm_ConvexOptimization_leindler_supremal_integral_real_line_compact_bounded

open scoped RealInnerProductSpace ENNReal
open MeasureTheory Filter Topology Set

theorem solution
    (l : ℝ) (hl0 : 0 < l) (hl1 : l < 1)
    (f g : ℝ → ℝ≥0∞)
    (hf : Measurable f) (hg : Measurable g) :
    (∫⁻ x, f x) ^ (1 - l) * (∫⁻ x, g x) ^ l ≤
      ∫⁻ z, sSup {q : ℝ≥0∞ | ∃ x y : ℝ,
        (1 - l) • x + l • y = z ∧
          q = f x ^ (1 - l) * g y ^ l} := by
  let fn : ℕ → ℝ → ℝ≥0∞ := fun n x ↦
    if x ∈ Icc (-(n : ℝ)) (n : ℝ) then min (f x) (n : ℝ≥0∞) else 0
  let gn : ℕ → ℝ → ℝ≥0∞ := fun n x ↦
    if x ∈ Icc (-(n : ℝ)) (n : ℝ) then min (g x) (n : ℝ≥0∞) else 0

  have hfn_meas : ∀ n, Measurable (fn n) := by
    intro n
    exact Measurable.ite measurableSet_Icc (hf.min measurable_const) measurable_const
  have hgn_meas : ∀ n, Measurable (gn n) := by
    intro n
    exact Measurable.ite measurableSet_Icc (hg.min measurable_const) measurable_const

  have hfn_compact : ∀ n, HasCompactSupport (fn n) := by
    intro n
    apply HasCompactSupport.intro (K := Icc (-(n : ℝ)) (n : ℝ)) isCompact_Icc
    intro x hx
    simp only [fn, if_neg hx]
  have hgn_compact : ∀ n, HasCompactSupport (gn n) := by
    intro n
    apply HasCompactSupport.intro (K := Icc (-(n : ℝ)) (n : ℝ)) isCompact_Icc
    intro x hx
    simp only [gn, if_neg hx]

  have hfn_bound : ∀ n x, fn n x ≤ ((n : NNReal) : ENNReal) := by
    intro n x
    simp only [fn]
    split_ifs
    · exact min_le_right _ _
    · exact bot_le
  have hgn_bound : ∀ n x, gn n x ≤ ((n : NNReal) : ENNReal) := by
    intro n x
    simp only [gn]
    split_ifs
    · exact min_le_right _ _
    · exact bot_le

  have hfn_le : ∀ n x, fn n x ≤ f x := by
    intro n x
    simp only [fn]
    split_ifs
    · exact min_le_left _ _
    · exact bot_le
  have hgn_le : ∀ n x, gn n x ≤ g x := by
    intro n x
    simp only [gn]
    split_ifs
    · exact min_le_left _ _
    · exact bot_le

  have hfn_mono : ∀ᵐ x ∂volume, Monotone fun n ↦ fn n x := by
    filter_upwards [] with x
    intro i j hij
    have hijR : (i : ℝ) ≤ (j : ℝ) := Nat.cast_le.2 hij
    simp only [fn]
    split_ifs with hxi hxj
    · exact min_le_min le_rfl (Nat.cast_le.2 hij)
    · exfalso
      apply hxj
      constructor
      · exact (neg_le_neg hijR).trans hxi.1
      · exact hxi.2.trans hijR
    · exact bot_le
    · exact le_rfl
  have hgn_mono : ∀ᵐ x ∂volume, Monotone fun n ↦ gn n x := by
    filter_upwards [] with x
    intro i j hij
    have hijR : (i : ℝ) ≤ (j : ℝ) := Nat.cast_le.2 hij
    simp only [gn]
    split_ifs with hxi hxj
    · exact min_le_min le_rfl (Nat.cast_le.2 hij)
    · exfalso
      apply hxj
      constructor
      · exact (neg_le_neg hijR).trans hxi.1
      · exact hxi.2.trans hijR
    · exact bot_le
    · exact le_rfl

  have hfn_lim : ∀ᵐ x ∂volume,
      Tendsto (fun n ↦ fn n x) atTop (𝓝 (f x)) := by
    filter_upwards [] with x
    obtain ⟨N, hN⟩ := exists_nat_ge |x|
    have heq : (fun n ↦ fn n x) =ᶠ[atTop]
        (fun n ↦ min (f x) (n : ℝ≥0∞)) := by
      filter_upwards [eventually_ge_atTop N] with n hn
      have habs : |x| ≤ (n : ℝ) := hN.trans (Nat.cast_le.2 hn)
      have hxI : x ∈ Icc (-(n : ℝ)) (n : ℝ) := abs_le.mp habs
      simp only [fn, if_pos hxI]
    apply Tendsto.congr' heq.symm
    simpa using Tendsto.min tendsto_const_nhds ENNReal.tendsto_nat_nhds_top
  have hgn_lim : ∀ᵐ x ∂volume,
      Tendsto (fun n ↦ gn n x) atTop (𝓝 (g x)) := by
    filter_upwards [] with x
    obtain ⟨N, hN⟩ := exists_nat_ge |x|
    have heq : (fun n ↦ gn n x) =ᶠ[atTop]
        (fun n ↦ min (g x) (n : ℝ≥0∞)) := by
      filter_upwards [eventually_ge_atTop N] with n hn
      have habs : |x| ≤ (n : ℝ) := hN.trans (Nat.cast_le.2 hn)
      have hxI : x ∈ Icc (-(n : ℝ)) (n : ℝ) := abs_le.mp habs
      simp only [gn, if_pos hxI]
    apply Tendsto.congr' heq.symm
    simpa using Tendsto.min tendsto_const_nhds ENNReal.tendsto_nat_nhds_top

  have hfint_lim : Tendsto (fun n ↦ ∫⁻ x, fn n x) atTop (𝓝 (∫⁻ x, f x)) :=
    lintegral_tendsto_of_tendsto_of_monotone
      (fun n ↦ (hfn_meas n).aemeasurable) hfn_mono hfn_lim
  have hgint_lim : Tendsto (fun n ↦ ∫⁻ x, gn n x) atTop (𝓝 (∫⁻ x, g x)) :=
    lintegral_tendsto_of_tendsto_of_monotone
      (fun n ↦ (hgn_meas n).aemeasurable) hgn_mono hgn_lim

  by_cases hfint_zero : (∫⁻ x, f x) = 0
  · simp [hfint_zero, ENNReal.zero_rpow_of_pos (sub_pos.mpr hl1)]
  by_cases hgint_zero : (∫⁻ x, g x) = 0
  · simp [hgint_zero, ENNReal.zero_rpow_of_pos hl0]

  have hf_rpow_ne : (∫⁻ x, f x) ^ (1 - l) ≠ 0 := by
    intro hzero
    exact hfint_zero ((ENNReal.rpow_eq_zero_iff_of_pos (sub_pos.mpr hl1)).mp hzero)
  have hg_rpow_ne : (∫⁻ x, g x) ^ l ≠ 0 := by
    intro hzero
    exact hgint_zero ((ENNReal.rpow_eq_zero_iff_of_pos hl0).mp hzero)
  have hlhs_lim : Tendsto
      (fun n ↦ (∫⁻ x, fn n x) ^ (1 - l) * (∫⁻ x, gn n x) ^ l)
      atTop
      (𝓝 ((∫⁻ x, f x) ^ (1 - l) * (∫⁻ x, g x) ^ l)) := by
    apply ENNReal.Tendsto.mul
    · exact (ENNReal.continuous_rpow_const.tendsto _).comp hfint_lim
    · exact Or.inl hf_rpow_ne
    · exact (ENNReal.continuous_rpow_const.tendsto _).comp hgint_lim
    · exact Or.inl hg_rpow_ne

  apply le_of_tendsto hlhs_lim
  filter_upwards [] with n
  refine (ConvexOptimization.leindler_supremal_integral_real_line_compact_bounded
    l hl0 hl1 (fn n) (gn n) (hfn_meas n) (hgn_meas n)
    (hfn_compact n) (hgn_compact n) n n (hfn_bound n) (hgn_bound n)).trans ?_
  apply lintegral_mono
  intro z
  apply sSup_le
  intro q hq
  rcases hq with ⟨x, y, hxy, rfl⟩
  refine (mul_le_mul'
    (ENNReal.rpow_le_rpow (hfn_le n x) (sub_nonneg.mpr hl1.le))
    (ENNReal.rpow_le_rpow (hgn_le n y) hl0.le)).trans ?_
  apply le_sSup
  exact ⟨x, y, hxy, rfl⟩
