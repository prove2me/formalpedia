-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_04a_bv_actual_jump_atomic_domination_all_measurable_time_sets
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T12:21:39.106387+00:00
-- url     : https://prove2.me/submissions/73c1ad63-c339-4e05-8f85-ea80eead0ff1

import Mathlib.MeasureTheory.Measure.Stieltjes
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_residual_stieltjes_atom_is_source_jump

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Classical

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∃ F : StieltjesFunction ℝ≥0,
      (∀ t : ℝ≥0, (F t : ℝ) = (t : ℝ) * X.drift - X.X t ω) ∧
      (∀ (B : Set ℝ≥0), MeasurableSet B →
        (∑' (u : ℝ≥0),
          if 0 < u ∧ u ∈ B then
            ENNReal.ofReal (Function.leftLim
              (fun v : ℝ≥0 => X.X v ω) u - X.X u ω)
          else 0) ≤ F.measure B) := by
  filter_upwards
    [avram_wave4_04a_bv_actual_residual_stieltjes_atom_is_source_jump X hBV]
    with ω hω
  obtain ⟨F, hF, hAtoms⟩ := hω
  refine ⟨F, hF, ?_⟩
  intro B hB
  classical
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun S => ?_
  let Q : Finset ℝ≥0 := S.filter (fun u => 0 < u ∧ u ∈ B)
  have hQ : ∀ u ∈ Q, 0 < u ∧ u ∈ B := by
    intro u hu
    exact (Finset.mem_filter.mp hu).2
  have hsub : (Q : Set ℝ≥0) ⊆ B := by
    intro u hu
    exact (hQ u hu).2
  calc
    (∑ u ∈ S,
      if 0 < u ∧ u ∈ B then ENNReal.ofReal
        (Function.leftLim (fun v : ℝ≥0 => X.X v ω) u - X.X u ω)
      else 0) =
      ∑ u ∈ Q, ENNReal.ofReal
        (Function.leftLim (fun v : ℝ≥0 => X.X v ω) u - X.X u ω) := by
        simp only [Q, Finset.sum_filter]
    _ = ∑ u ∈ Q, F.measure {u} := by
      apply Finset.sum_congr rfl
      intro u hu
      exact (hAtoms u (hQ u hu).1).symm
    _ = F.measure (Q : Set ℝ≥0) := by
      exact sum_measure_singleton
    _ ≤ F.measure B := measure_mono hsub
