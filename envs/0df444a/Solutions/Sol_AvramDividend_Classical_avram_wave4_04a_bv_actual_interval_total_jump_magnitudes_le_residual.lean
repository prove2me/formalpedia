-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_04a_bv_actual_interval_total_jump_magnitudes_le_residual
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T12:01:49.237555+00:00
-- url     : https://prove2.me/submissions/082eea1b-9d94-4bc2-acb0-954a022b704f

import Mathlib.MeasureTheory.Measure.Stieltjes
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
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
    ∀ᵐ ω ∂P, ∀ (s t : ℝ≥0), s ≤ t →
      (∑' (u : ℝ≥0),
        if s < u ∧ u ≤ t then
          ENNReal.ofReal (Function.leftLim
            (fun v : ℝ≥0 => X.X v ω) u - X.X u ω)
        else 0) ≤
      ENNReal.ofReal
        (((t : ℝ) * X.drift - X.X t ω) -
          ((s : ℝ) * X.drift - X.X s ω)) := by
  filter_upwards
    [avram_wave4_04a_bv_actual_residual_stieltjes_atom_is_source_jump X hBV]
    with ω hω
  obtain ⟨F, hF, hAtoms⟩ := hω
  intro s t hst
  classical
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun S => ?_
  let Q : Finset ℝ≥0 := S.filter (fun u => s < u ∧ u ≤ t)
  have hQ : ∀ u ∈ Q, s < u ∧ u ≤ t := by
    intro u hu
    exact (Finset.mem_filter.mp hu).2
  have hsub : (Q : Set ℝ≥0) ⊆ Ioc s t := by
    intro u hu
    exact hQ u hu
  calc
    (∑ u ∈ S,
      if s < u ∧ u ≤ t then ENNReal.ofReal
        (Function.leftLim (fun v : ℝ≥0 => X.X v ω) u - X.X u ω)
      else 0) =
      ∑ u ∈ Q, ENNReal.ofReal
        (Function.leftLim (fun v : ℝ≥0 => X.X v ω) u - X.X u ω) := by
        simp only [Q, Finset.sum_filter]
    _ = ∑ u ∈ Q, F.measure {u} := by
      apply Finset.sum_congr rfl
      intro u hu
      have hupos : 0 < u :=
        lt_of_le_of_lt (show (0 : ℝ≥0) ≤ s from zero_le) (hQ u hu).1
      exact (hAtoms u hupos).symm
    _ = F.measure (Q : Set ℝ≥0) := by
      exact sum_measure_singleton
    _ ≤ F.measure (Ioc s t) := measure_mono hsub
    _ = ENNReal.ofReal
      (((t : ℝ) * X.drift - X.X t ω) -
        ((s : ℝ) * X.drift - X.X s ω)) := by
      rw [StieltjesFunction.measure_Ioc]
      rw [hF t, hF s]
