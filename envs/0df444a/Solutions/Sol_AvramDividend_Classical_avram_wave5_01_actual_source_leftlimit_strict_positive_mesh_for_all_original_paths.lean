-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_01_actual_source_leftlimit_strict_positive_mesh_for_all_original_paths
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T13:23:31.200192+00:00
-- url     : https://prove2.me/submissions/e4715564-5394-48ad-a739-423d2120a733

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- An actual source Levy left-limit is reached along a deterministic
strictly increasing positive-time grid shared by every source sample path. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (t : ℝ≥0) (ht : 0 < t) :
    ∃ grid : ℕ → ℝ≥0,
      StrictMono grid ∧
      (∀ n, 0 < grid n ∧ grid n < t) ∧
      Tendsto grid atTop (𝓝[<] t) ∧
      ∀ ω : Ω,
        Tendsto (fun n => X.X (grid n) ω) atTop
          (𝓝 (Function.leftLim (fun u : ℝ≥0 => X.X u ω) t)) := by
  classical
  obtain ⟨grid, hstrict, hmem, hgt⟩ :=
    (dense_univ : Dense (Set.univ : Set ℝ≥0)).exists_seq_strictMono_tendsto_of_lt ht
  have hlt : ∀ n, 0 < grid n ∧ grid n < t := by
    intro n
    exact (hmem n).1
  have hwithin : Tendsto grid atTop (𝓝[<] t) := by
    exact tendsto_nhdsWithin_iff.mpr
      ⟨hgt, Filter.Eventually.of_forall (fun n => (hlt n).2)⟩
  refine ⟨grid, hstrict, hlt, hwithin, ?_⟩
  intro ω
  exact (tendsto_leftLim_of_tendsto (X.leftLim ω t ht)).comp hwithin
