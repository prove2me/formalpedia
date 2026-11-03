-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_06_original_frozen_prefix_cadlag_all_horizons
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T00:12:09.591753+00:00
-- url     : https://prove2.me/submissions/ae0774cc-9138-4344-a76e-e2f700ec808f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_frozen_prefix_right_continuous

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Every original Lévy path remains càdlàg after freezing at a deterministic time. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (T : ℝ≥0) :
    (∀ u : ℝ≥0,
      ContinuousWithinAt (fun v : ℝ≥0 => X.X (min v T) ω) (Ici u) u) ∧
    (∀ u : ℝ≥0, 0 < u →
      ∃ l : ℝ, Tendsto (fun v : ℝ≥0 => X.X (min v T) ω)
        (𝓝[<] u) (𝓝 l)) := by
  constructor
  · exact avram_wave7_06_original_frozen_prefix_right_continuous X ω T
  · intro u hu
    by_cases huT : u ≤ T
    · obtain ⟨l, hl⟩ := X.leftLim ω u hu
      have hEq :
          (fun v : ℝ≥0 => X.X (min v T) ω) =ᶠ[𝓝[<] u]
            (fun v : ℝ≥0 => X.X v ω) := by
        filter_upwards [self_mem_nhdsWithin] with v hv
        have hvT : v ≤ T := le_trans (le_of_lt hv) huT
        simp only [min_eq_left hvT]
      exact ⟨l, hl.congr' hEq.symm⟩
    · have hTu : T < u := lt_of_not_ge huT
      have hOpen : Ioi T ∈ (𝓝 u : Filter ℝ≥0) :=
        isOpen_Ioi.mem_nhds hTu
      have hNear : Ioi T ∈ (𝓝[<] u : Filter ℝ≥0) :=
        nhdsWithin_le_nhds hOpen
      have hEq :
          (fun v : ℝ≥0 => X.X (min v T) ω) =ᶠ[𝓝[<] u]
            (fun _ : ℝ≥0 => X.X T ω) := by
        filter_upwards [hNear] with v hv
        change T < v at hv
        simp only [min_eq_right (le_of_lt hv)]
      exact ⟨X.X T ω, tendsto_const_nhds.congr' hEq.symm⟩
