-- Prove2me | solution 1 for Formalism.L2.Th1.C.JetSubstitutionLemmas.intPS_derivative_of_LG
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:33:36.303131+00:00
-- url     : https://prove2.me/submissions/2891354b-70b2-466a-8ce5-d751e2ecf3da

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_JetExpShape
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_CoeffPowEqZeroOfCc
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_DegreeLeOfMemAntidiagonal
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_IntPSDerivativeOfLG
import Theorems.Thm_Formalism_L2_Th1_C_JetSubstitutionLemmas_intPS_of_intMv
import Theorems.Thm_Formalism_L2_Th1_C_JetSubstitutionLemmas_intPS_mul
import Theorems.Thm_Formalism_L2_Th1_C_JetSubstitutionLemmas_intPS_derivative
import Theorems.Thm_Formalism_L2_Th1_C_JetSubstitutionLemmas_intPS_of_mul_eq_one
import Theorems.Thm_Formalism_L2_Th1_C_IntegralMvPolynomialLemmas_constantCoeff_mvExp
import Theorems.Thm_Formalism_L2_Th1_C_constantCoeff_mvExp
import Theorems.Thm_Formalism_L2_Th1_C_derivative_mvExp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.C
open Formalism.L2.Th1.C.JetSubstitutionLemmas
variable {K : Type} [Field K] [CharZero K] {R : Subring K}
namespace Formalism.L2.Th1.C.JetSubstitutionLemmas
theorem _root_.solution {f : PowerSeries K} (hf : LG R f) :
    IntPS R (PowerSeries.derivative K f) := by
  obtain ⟨hf0, hE⟩ := hf
  have hEi : IntPS R (mvExp f : PowerSeries K) := intPS_of_intMv hE
  have hE0 : PowerSeries.constantCoeff (mvExp f : PowerSeries K) = 1 := IntegralMvPolynomialLemmas.constantCoeff_mvExp hf0
  have hd := derivative_mvExp (K := K) (f := f) hf0
  have hinv := PowerSeries.mul_inv_cancel (mvExp f : PowerSeries K) (by rw [hE0]; exact one_ne_zero)
  have e : PowerSeries.derivative K f =
      PowerSeries.derivative K (mvExp f : PowerSeries K) * (mvExp f : PowerSeries K)⁻¹ := by
    rw [hd, mul_assoc, hinv, mul_one]
  rw [e]
  exact intPS_mul (intPS_derivative hEi) (intPS_of_mul_eq_one hEi hE0 hinv)
end Formalism.L2.Th1.C.JetSubstitutionLemmas
