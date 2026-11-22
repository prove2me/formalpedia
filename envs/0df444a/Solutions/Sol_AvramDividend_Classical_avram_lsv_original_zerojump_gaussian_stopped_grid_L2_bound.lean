-- Prove2me | solution 1 for AvramDividend.Classical.avram_lsv_original_zerojump_gaussian_stopped_grid_L2_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T12:49:10.706849+00:00
-- url     : https://prove2.me/submissions/7679199d-a694-4c16-ade2-7acbee5fdedf

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_zerojump_centered_source_martingale
import Theorems.Thm_AvramDividend_Classical_avram_a21_original_zero_jump_process_fixed_time_square_moment_20261113
import Theorems.Thm_AvramDividend_Classical_avram_lsv_finite_grid_stopping_square_le

open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false
noncomputable section

/- This is the original-process instantiation of the countable-grid stopping
   contraction adapted from dufeteller/lean-lsv, LSV/LocalizedStoppingL2Convergence,
   commit a5f604de2e1ae431de4cbecde23e5694a12ba719, CC BY 4.0.
   Original-process martingale and moment inputs are already Proved in Prove2Me. -/

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (T : ℝ≥0) (τ : Ω → WithTop ℝ≥0)
    (hτ : IsStoppingTime 𝓕.rightCont τ)
    (hτle : ∀ ω, τ ω ≤ (T : WithTop ℝ≥0))
    (hτcount : (Set.range τ).Countable) :
    let M : ℝ≥0 → Ω → ℝ := fun s ω => X.X s ω - (s : ℝ) * X.c
    MemLp (stoppedValue M τ) 2 P ∧
      (∫ ω, (stoppedValue M τ ω)^2 ∂P) ≤ (T : ℝ) * X.σ ^ 2 := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  let M : ℝ≥0 → Ω → ℝ := fun s ω => X.X s ω - (s : ℝ) * X.c
  change MemLp (stoppedValue M τ) 2 P ∧
    (∫ ω, (stoppedValue M τ ω)^2 ∂P) ≤ (T : ℝ) * X.σ ^ 2
  have hM : Martingale M 𝓕.rightCont P :=
    avram_wave6_03_original_rightCont_zerojump_centered_source_martingale X hν
  have hMom :=
    avram_a21_original_zero_jump_process_fixed_time_square_moment_20261113 X hν T
  have hMMeas : Measurable (M T) := by
    change Measurable (fun ω => X.X T ω - (T : ℝ) * X.c)
    exact ((X.adapted T).mono (𝓕.le T) le_rfl).sub_const _
  have hM2 : MemLp (M T) 2 P :=
    (memLp_two_iff_integrable_sq (μ := P)
      hMMeas.aestronglyMeasurable).2 hMom.1
  have hStop :=
    avram_lsv_finite_grid_stopping_square_le P 𝓕.rightCont
      M hM T hM2 τ hτ hτle hτcount
  refine ⟨hStop.1, ?_⟩
  calc
    (∫ ω, (stoppedValue M τ ω)^2 ∂P) ≤
        ∫ ω, (M T ω)^2 ∂P := hStop.2
    _ = (T : ℝ) * X.σ ^ 2 := hMom.2

