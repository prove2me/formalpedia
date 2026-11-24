-- Prove2me | solution 1 for Formalism.L2.Th1.C.JetSubstitutionLemmas.intPS_Dinv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:22:13.336022+00:00
-- url     : https://prove2.me/submissions/4ba6f7f5-f620-4874-bf77-4302535d9558

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_JetExpShape
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_CoeffPowEqZeroOfCc
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_DegreeLeOfMemAntidiagonal
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_IntPSDerivativeOfLG
import Theorems.Thm_Formalism_L2_Th1_C_JetSubstitutionLemmas_intPS_mul
import Theorems.Thm_Formalism_L2_Th1_C_JetSubstitutionLemmas_intPS_of_mul_eq_one

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
variable {K : Type} [Field K]
variable {R : Subring K}
namespace Formalism.L2.Th1.C.JetSubstitutionLemmas
theorem _root_.solution {l f : PowerSeries K} (hl : IsOneUnit R (PowerSeries.derivative K l))
    (hf : IntPS R (PowerSeries.derivative K f)) : IntPS R (Dinv l f) := by
  unfold Dinv
  exact intPS_mul (intPS_of_mul_eq_one hl.2 hl.1
    (PowerSeries.mul_inv_cancel _ (by rw [hl.1]; exact one_ne_zero))) hf
end Formalism.L2.Th1.C.JetSubstitutionLemmas
