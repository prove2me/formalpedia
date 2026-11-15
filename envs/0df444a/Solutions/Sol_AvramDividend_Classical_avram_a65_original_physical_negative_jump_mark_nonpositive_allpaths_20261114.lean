-- Prove2me | solution 1 for AvramDividend.Classical.avram_a65_original_physical_negative_jump_mark_nonpositive_allpaths_20261114
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T12:37:01.539106+00:00
-- url     : https://prove2.me/submissions/382be0db-2a7e-4d76-bdde-846003090f1d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Every actual original physical positive-time Lévy jump mark is nonpositive, on every path. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) :
    ∀ ω : Ω, ∀ t : ℝ≥0, 0 < t →
      X.X t ω - Function.leftLim (fun u : ℝ≥0 => X.X u ω) t ≤ 0 := by
  intro ω t ht
  obtain ⟨l, hl⟩ := X.leftLim ω t ht
  have hCanonical :
      Tendsto (fun u : ℝ≥0 => X.X u ω)
        (𝓝[<] t)
        (𝓝 (Function.leftLim (fun u : ℝ≥0 => X.X u ω) t)) :=
    tendsto_leftLim_of_tendsto ⟨l, hl⟩
  have hNonpos : X.X t ω ≤
      Function.leftLim (fun u : ℝ≥0 => X.X u ω) t :=
    X.noPosJumps ω t _ ht hCanonical
  linarith
