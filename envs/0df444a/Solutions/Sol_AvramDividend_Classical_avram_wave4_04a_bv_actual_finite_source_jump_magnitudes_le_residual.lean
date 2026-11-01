-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_04a_bv_actual_finite_source_jump_magnitudes_le_residual
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T11:22:32.320047+00:00
-- url     : https://prove2.me/submissions/3acea2ed-8812-4bb0-a464-9aaac6d4c5b0

import Mathlib.MeasureTheory.Measure.Stieltjes
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_residual_stieltjes_atom_is_source_jump

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∀ (T : ℝ≥0) (S : Finset ℝ≥0),
      (∀ u ∈ S, 0 < u ∧ u ≤ T) →
      (∑ u ∈ S, ENNReal.ofReal
        (Function.leftLim (fun v : ℝ≥0 => X.X v ω) u - X.X u ω)) ≤
      ENNReal.ofReal ((T : ℝ) * X.drift - X.X T ω) := by
  filter_upwards
    [avram_wave4_04a_bv_actual_residual_stieltjes_atom_is_source_jump X hBV]
    with ω hω
  obtain ⟨F, hF, hAtoms⟩ := hω
  intro T S hS
  have hsub : (S : Set ℝ≥0) ⊆ Ioc 0 T := by
    intro u hu
    exact hS u hu
  calc
    (∑ u ∈ S, ENNReal.ofReal
      (Function.leftLim (fun v : ℝ≥0 => X.X v ω) u - X.X u ω)) =
        ∑ u ∈ S, F.measure {u} := by
          apply Finset.sum_congr rfl
          intro u hu
          exact (hAtoms u (hS u hu).1).symm
    _ = F.measure (S : Set ℝ≥0) := by
          exact sum_measure_singleton
    _ ≤ F.measure (Ioc 0 T) := measure_mono hsub
    _ = ENNReal.ofReal ((T : ℝ) * X.drift - X.X T ω) := by
          rw [StieltjesFunction.measure_Ioc]
          rw [hF T, hF 0]
          simp [X.X_zero ω]
