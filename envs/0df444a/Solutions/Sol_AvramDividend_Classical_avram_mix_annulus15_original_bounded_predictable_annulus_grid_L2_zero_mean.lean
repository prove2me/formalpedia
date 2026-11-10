-- Prove2me | solution 1 for AvramDividend.Classical.avram_mix_annulus15_original_bounded_predictable_annulus_grid_L2_zero_mean
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T18:02:53.660779+00:00
-- url     : https://prove2.me/submissions/e6ecef6d-939a-4e10-a887-00098d3c4bff

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_interval_h_original_full_cutoff_predictable_finite_grid_L2_zero_mean
import Theorems.Thm_AvramDividend_Classical_avram_mixed_source13_original_annulus_levy_rate_difference
import Theorems.Thm_AvramDividend_Classical_avram_mix_annulus15_original_real_window_count_additive
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped ENNReal NNReal BigOperators
noncomputable section
/-- Original bounded predictable negative-annulus compensated physical grid L² sum. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (n m : ℕ) (hnm : n ≤ m)
    (grid : ℕ → ℝ≥0) (hGrid : ∀ i, grid i ≤ grid (i + 1)) (H : ℕ → Ω → ℝ)
    (hH : ∀ i, StronglyMeasurable[𝓕.rightCont (grid i)] (H i))
    (L : ℝ) (hBound : ∀ i ω, |H i ω| ≤ L) (k : ℕ) :
    let B : Set ℝ := Ioc (-(1 / ((n : ℝ) + 1)))
      (-(1 / ((m : ℝ) + 1)))
    let N : ℕ → Ω → ℝ≥0∞ := fun i ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc (grid i) (grid (i + 1)) ×ˢ B)
    let r : ℕ → ℝ := fun i =>
      (((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) * X.ν B).toReal
    let Z : ℕ → Ω → ℝ := fun i ω =>
      H i ω * ((N i ω).toReal - r i)
    MemLp (fun ω => ∑ i ∈ Finset.range k, Z i ω) 2 P ∧
      (∫ ω, ∑ i ∈ Finset.range k, Z i ω ∂P) = 0 := by
  classical
  let c : ℝ := -(1 / ((n : ℝ) + 1))
  let d : ℝ := -(1 / ((m : ℝ) + 1))
  let B : Set ℝ := Ioc c d
  let J : ℕ → Set ℝ → Ω → ℝ≥0∞ := fun i E ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc (grid i) (grid (i + 1)) ×ˢ E)
  let rate : ℕ → Set ℝ → ℝ := fun i E =>
    (((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) * X.ν E).toReal
  let Z : ℕ → Set ℝ → Ω → ℝ := fun i E ω =>
    H i ω * ((J i E ω).toReal - rate i E)
  change MemLp (fun ω => ∑ i ∈ Finset.range k, Z i B ω) 2 P ∧
    (∫ ω, ∑ i ∈ Finset.range k, Z i B ω ∂P) = 0
  have hN := avram_p4_s3_interval_h_original_full_cutoff_predictable_finite_grid_L2_zero_mean X n grid hGrid H hH L hBound k
  have hM := avram_p4_s3_interval_h_original_full_cutoff_predictable_finite_grid_L2_zero_mean X m grid hGrid H hH L hBound k
  change MemLp (fun ω => ∑ i ∈ Finset.range k, Z i (Iic c) ω) 2 P ∧ (∫ ω, ∑ i ∈ Finset.range k, Z i (Iic c) ω ∂P) = 0 at hN
  change MemLp (fun ω => ∑ i ∈ Finset.range k, Z i (Iic d) ω) 2 P ∧ (∫ ω, ∑ i ∈ Finset.range k, Z i (Iic d) ω ∂P) = 0 at hM
  have hCell (i : ℕ) (ω : Ω) :
      Z i B ω = Z i (Iic d) ω - Z i (Iic c) ω := by
    have hCount := avram_mix_annulus15_original_real_window_count_additive X ω (grid i) (grid (i + 1)) (hGrid i) n m hnm
    change (J i (Iic d) ω).toReal = (J i (Iic c) ω).toReal + (J i B ω).toReal at hCount
    have hRate := avram_mixed_source13_original_annulus_levy_rate_difference X (grid (i + 1) - grid i) n m hnm
    change rate i (Iic d) = rate i (Iic c) + rate i B at hRate
    dsimp [Z]; rw [hCount, hRate]; ring
  have hSum (ω : Ω) :
      (∑ i ∈ Finset.range k, Z i B ω) =
        (∑ i ∈ Finset.range k, Z i (Iic d) ω) -
          (∑ i ∈ Finset.range k, Z i (Iic c) ω) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun i hi => hCell i ω)
  constructor
  · have hEq : (fun ω => ∑ i ∈ Finset.range k, Z i B ω) =
        (fun ω => (∑ i ∈ Finset.range k, Z i (Iic d) ω) -
          (∑ i ∈ Finset.range k, Z i (Iic c) ω)) := by
      funext ω
      exact hSum ω
    rw [hEq]
    exact hM.1.sub hN.1
  · calc
      (∫ ω, ∑ i ∈ Finset.range k, Z i B ω ∂P) =
        (∫ ω, (∑ i ∈ Finset.range k, Z i (Iic d) ω) -
          (∑ i ∈ Finset.range k, Z i (Iic c) ω) ∂P) := by
            exact integral_congr_ae (Filter.Eventually.of_forall hSum)
      _ = (∫ ω, ∑ i ∈ Finset.range k, Z i (Iic d) ω ∂P) -
          (∫ ω, ∑ i ∈ Finset.range k, Z i (Iic c) ω ∂P) :=
            integral_sub (hM.1.integrable (by norm_num))
              (hN.1.integrable (by norm_num))
      _ = 0 := by rw [hM.2, hN.2]; ring
