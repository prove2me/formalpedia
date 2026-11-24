-- Prove2me | solution 1 for Formalism.L2.Th1.C.lGHalf_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:49:42.679438+00:00
-- url     : https://prove2.me/submissions/4f801e67-40cb-4cda-b69e-fdaabce1e685

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_IntBinomScalar
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_DegreeLeOfMemAntidiagonal
import Theorems.Thm_Formalism_L2_Th1_C_IntegralMvPolynomialLemmas_intMv_of_sq
import Theorems.Thm_Formalism_L2_Th1_C_IntegralMvPolynomialLemmas_constantCoeff_mvExp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PowerSeries
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.C
open IntegralMvPolynomialLemmas
namespace Formalism.L2.Th1.C
theorem _root_.solution (hE : MvExpLaws) : LGHalf := by
  intro K _ _ R σ h2 f hf
  obtain ⟨-, -, hadd, -⟩ := hE K σ
  have hf0 : MvPowerSeries.constantCoeff f = 0 := by
    have h := hf.1
    rw [map_add, ← two_mul] at h
    exact (mul_eq_zero.mp h).resolve_left two_ne_zero
  refine ⟨hf0, intMv_of_sq h2 two_ne_zero (constantCoeff_mvExp hf0) ?_⟩
  rw [← hadd f f hf0 hf0]
  exact hf.2
end Formalism.L2.Th1.C
