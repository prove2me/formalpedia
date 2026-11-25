-- Prove2me | solution 1 for Formalism.L2.Th1.C.FormalGroupJetIntegrality.ph_fadd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:42:38.876804+00:00
-- url     : https://prove2.me/submissions/8d5d34e4-5eb0-4add-a176-aa24d0970baf

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_ThirdJetIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_SigmaConstantAgrees
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_IntegralThirdInvariantDerivative
import Theorems.Thm_Formalism_L2_Th1_C_Clo_CoeffCont_subst
import Theorems.Thm_Formalism_L2_Th1_C_JetSubstitutionLemmas_subst_ph_linv
import Theorems.Thm_Formalism_L2_Th1_C_Pts_constantCoeff_add_l


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
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.C
open Formalism.L2.Th1.C.FormalGroupJetIntegrality
open JetSubstitutionLemmas
variable {K : Type} [Field K] [CharZero K] {R : Subring K}
namespace Formalism.L2.Th1.C.FormalGroupJetIntegrality
theorem _root_.solution {σ : Type} {l linv : PowerSeries K} (h : IsLogPair l linv) (ph : PowerSeries K)
    {a b : MvPowerSeries σ K} (ha : MvPowerSeries.constantCoeff a = 0)
    (hb : MvPowerSeries.constantCoeff b = 0) :
    PowerSeries.subst (fadd l linv a b) ph =
      PowerSeries.subst (PowerSeries.subst a l + PowerSeries.subst b l)
        (PowerSeries.subst linv ph) :=
  subst_ph_linv h ph (Pts.constantCoeff_add_l h ha hb)
end Formalism.L2.Th1.C.FormalGroupJetIntegrality
