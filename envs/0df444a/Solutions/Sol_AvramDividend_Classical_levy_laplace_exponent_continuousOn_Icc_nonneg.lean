-- Prove2me | solution 1 for AvramDividend.Classical.levy_laplace_exponent_continuousOn_Icc_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T06:25:36.224809+00:00
-- url     : https://prove2.me/submissions/ffee2752-bc82-42ef-b194-223cad906f5c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_psi_compensated_uniform_envelope
import Theorems.Thm_AvramDividend_Classical_psi_continuousOn_Icc_of_compensated_envelope

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (B : ℝ) (hB : 0 ≤ B) :
    ContinuousOn X.ψ (Icc (0 : ℝ) B) := by
  have hminMeas : Measurable (fun y : ℝ => min 1 (y ^ 2)) := by
    fun_prop
  have hminNonneg :
      0 ≤ᵐ[X.ν] (fun y : ℝ => min 1 (y ^ 2)) :=
    Filter.Eventually.of_forall (fun y =>
      le_min (by norm_num) (sq_nonneg y))
  have hminInt :
      Integrable (fun y : ℝ => min 1 (y ^ 2)) X.ν :=
    (lintegral_ofReal_ne_top_iff_integrable
      hminMeas.aestronglyMeasurable hminNonneg).mp
        (ne_of_lt X.ν_integrable)
  have hboundInt :
      Integrable (fun y : ℝ => (1 + B ^ 2) * min 1 (y ^ 2))
        (X.ν.restrict (Iio (0 : ℝ))) :=
    (hminInt.const_mul _).restrict
  exact psi_continuousOn_Icc_of_compensated_envelope X B hB
    (fun y : ℝ => (1 + B ^ 2) * min 1 (y ^ 2))
    hboundInt (psi_compensated_uniform_envelope X B hB)
