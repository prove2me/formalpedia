-- Prove2me | solution 1 for AvramDividend.Classical.avram_f6_purejump_UBV_zero_discount_scale_exists
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T18:55:45.314727+00:00
-- url     : https://prove2.me/submissions/bd8efee2-bfb0-4c28-9434-2c48b00cbd68
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_avram_p4_f6_renewal_cdf_atomless_continuous
import Theorems.Thm_AvramDividend_Classical_avram_p4_f6_renewal_cdf_monotone
import Theorems.Thm_AvramDividend_Classical_renewal_cdf_exponential_tonelli_any_levy
import Theorems.Thm_AvramDividend_Classical_avram_f6_purejump_UBV_zero_ladder_renewal_measure_exists
set_option autoImplicit false
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hσ : X.σ = 0) :
    ∃ W₀ : ℝ → ℝ, IsScaleFunction X 0 W₀ := by
  obtain ⟨ν, hSupp, hAtom, hFin, hLap⟩ :=
    avram_f6_purejump_UBV_zero_ladder_renewal_measure_exists X hX hBV hσ
  let W : ℝ → ℝ :=
    fun y => if 0 ≤ y then (ν (Ioc (0 : ℝ) y)).toReal else 0
  refine ⟨W, ?_⟩
  dsimp [IsScaleFunction]
  constructor
  · intro y hy
    simp [W, not_le.mpr hy]
  constructor
  · intro y hy
    simp only [W, if_pos hy]
    exact ENNReal.toReal_nonneg
  constructor
  · exact avram_p4_f6_renewal_cdf_atomless_continuous ν hAtom hFin
  constructor
  · exact avram_p4_f6_renewal_cdf_monotone ν hFin
  · intro θ hθ hψ
    simpa only [W, sub_zero] using
      (renewal_cdf_exponential_tonelli_any_levy
        X ν hSupp hFin hLap θ hθ hψ)
