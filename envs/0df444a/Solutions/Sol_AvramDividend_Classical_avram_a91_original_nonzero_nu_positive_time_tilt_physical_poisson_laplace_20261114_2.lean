-- Prove2me | solution 2 for AvramDividend.Classical.avram_a91_original_nonzero_nu_positive_time_tilt_physical_poisson_laplace_20261114
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T18:06:41.148905+00:00
-- url     : https://prove2.me/submissions/9fde0680-f1d8-4f5b-86b5-565305c184e8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a20_original_negative_borel_count_poisson_law
import Theorems.Thm_AvramDividend_Classical_avram_a85_original_physical_negative_jump_exponential_integrable_20261114
import Theorems.Thm_AvramDividend_Classical_avram_a30_poisson_count_conditional_mark_Laplace_20261116
import Theorems.Thm_AvramDividend_Classical_avram_a30_original_physical_negative_mark_conditional_Poisson_cell_Laplace_20261116
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) (hNu : X.ν ≠ 0)
    (t : ℝ≥0) (ht : 0 < t) (θ : ℝ) (hθ : 0 < θ)
    (J : Ω → ℝ) (hJMeas : Measurable J)
    (hJEq : J =ᵐ[P] fun ω =>
      ∑' u : ℝ≥0,
        if 0 < u ∧ u ≤ t then
          X.X u ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) u
        else 0) :
    (∫ ω, Real.exp (θ * J ω) ∂P) =
      Real.exp ((t : ℝ) *
        (∫ y in Iio (0 : ℝ), Real.exp (θ * y) - 1 ∂X.ν)) := by
  classical
  obtain ⟨K, r, hKm, hLaw, hCount, hRate⟩ :=
    avram_a20_original_negative_borel_count_poisson_law
      X hFinite t (Iio (0 : ℝ)) measurableSet_Iio (Subset.rfl)
  obtain ⟨m, hmInt, hCells, hRateM⟩ :=
    avram_a30_original_physical_negative_mark_conditional_Poisson_cell_Laplace_20261116
      X hFinite hNu t ht θ hθ J hJMeas hJEq
      K r hKm hLaw hCount hRate
  have hExpInt :=
    (avram_a85_original_physical_negative_jump_exponential_integrable_20261114
      X hFinite t θ (le_of_lt hθ) J hJMeas hJEq).1
  have hLap :=
    avram_a30_poisson_count_conditional_mark_Laplace_20261116
      P K hKm r m (fun ω : Ω => Real.exp (θ * J ω))
      hExpInt hmInt hCells
  exact hLap.trans (congrArg Real.exp hRateM)
