-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04_source_rightCont_levy_lift
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T01:14:31.57794+00:00
-- url     : https://prove2.me/submissions/76f4076f-3a2d-40f0-b313-71ccff395dba

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_indepIncrements_rightCont

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) :
    ∃ Y : SpectrallyNegativeLevy P 𝓕.rightCont,
      Y.X = X.X ∧ Y.c = X.c ∧ Y.σ = X.σ ∧ Y.ν = X.ν := by
  let Y : SpectrallyNegativeLevy P 𝓕.rightCont :=
    { X := X.X
      c := X.c
      σ := X.σ
      ν := X.ν
      isProbability := X.isProbability
      σ_nonneg := X.σ_nonneg
      ν_Ici := X.ν_Ici
      ν_integrable := X.ν_integrable
      X_zero := X.X_zero
      rightCont := X.rightCont
      leftLim := X.leftLim
      noPosJumps := X.noPosJumps
      adapted := by
        intro t
        exact (X.adapted t).mono (𝓕.le_rightCont t) le_rfl
      indepIncrements := by
        intro s t hst
        exact levy_indepIncrements_rightCont X s t hst
      stationaryIncrements := X.stationaryIncrements
      laplace := X.laplace }
  exact ⟨Y, rfl, rfl, rfl, rfl⟩
