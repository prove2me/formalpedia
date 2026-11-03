-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_06_original_ordered_predictable_weighted_cells_covariance_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T18:37:20.995205+00:00
-- url     : https://prove2.me/submissions/e054973c-f12d-4c87-9a12-1e748442e296

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_predictable_weight_centered_future_increment_L1_orthogonal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal

/-- Orthogonality of disjoint source centred predictable weighted cells,
including any gap between the two cells. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s₀ t₀ s₁ t₁ : ℝ≥0) (hOrder : s₀ + t₀ ≤ s₁)
    (W₀ W₁ : Ω → ℝ)
    (hW₀ : Measurable[𝓕 s₀] W₀)
    (hW₁ : Measurable[𝓕 s₁] W₁)
    (hXI : Integrable (X.X t₁) P)
    (hProduct : Integrable (fun ω =>
      (W₀ ω * (X.X (s₀ + t₀) ω - X.X s₀ ω -
        (∫ η, X.X t₀ η ∂P))) * W₁ ω) P) :
    (∫ ω, (W₀ ω * (X.X (s₀ + t₀) ω - X.X s₀ ω -
      (∫ η, X.X t₀ η ∂P))) *
      (W₁ ω * (X.X (s₁ + t₁) ω - X.X s₁ ω -
        (∫ η, X.X t₁ η ∂P))) ∂P) = 0 := by
  let W : Ω → ℝ := fun ω =>
    (W₀ ω * (X.X (s₀ + t₀) ω - X.X s₀ ω -
      (∫ η, X.X t₀ η ∂P))) * W₁ ω
  have hEarly : s₀ ≤ s₁ :=
    le_trans (by simp : s₀ ≤ s₀ + t₀) hOrder
  have hW₀Later : Measurable[𝓕 s₁] W₀ :=
    hW₀.mono (𝓕.mono hEarly) le_rfl
  have hEnd : Measurable[𝓕 s₁] (X.X (s₀ + t₀)) :=
    X.adapted.measurable_le hOrder
  have hStart : Measurable[𝓕 s₁] (X.X s₀) :=
    X.adapted.measurable_le hEarly
  have hW : Measurable[𝓕 s₁] W := by
    letI : MeasurableSpace Ω := 𝓕 s₁
    exact (hW₀Later.mul ((hEnd.sub hStart).sub measurable_const)).mul hW₁
  have hWI : Integrable W P := hProduct
  have hz :=
    avram_wave7_06_original_predictable_weight_centered_future_increment_L1_orthogonal
      X s₁ t₁ W hW hWI hXI
  convert hz using 1
  congr 1
  funext ω
  dsimp [W]
  ring
