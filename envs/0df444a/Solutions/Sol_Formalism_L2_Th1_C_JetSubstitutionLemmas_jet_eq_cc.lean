-- Prove2me | solution 1 for Formalism.L2.Th1.C.JetSubstitutionLemmas.jet_eq_cc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:47:41.511877+00:00
-- url     : https://prove2.me/submissions/640c41bf-beae-4feb-b347-c5f114b0a0b3

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_JetExpShape
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_CoeffPowEqZeroOfCc
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_DegreeLeOfMemAntidiagonal
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_IntPSDerivativeOfLG
import Theorems.Thm_Formalism_L2_Th1_C_JetSubstitutionLemmas_cc_subst1
import Theorems.Thm_Formalism_L2_Th1_C_JetSubstitutionLemmas_subst_Dinv_iterate

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
namespace Formalism.L2.Th1.C.JetSubstitutionLemmas
theorem _root_.solution {l linv : PowerSeries K} (h : IsLogPair l linv) (g : PowerSeries K) (i : ℕ) :
    jet l g i =
      PowerSeries.constantCoeff ((PowerSeries.derivative K)^[i] (PowerSeries.subst linv g)) := by
  unfold jet
  rw [← subst_Dinv_iterate h g i, cc_subst1 h.2.2.1]
end Formalism.L2.Th1.C.JetSubstitutionLemmas
