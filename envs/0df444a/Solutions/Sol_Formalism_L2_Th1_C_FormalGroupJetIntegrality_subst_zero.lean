-- Prove2me | solution 1 for Formalism.L2.Th1.C.FormalGroupJetIntegrality.subst_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:10:24.206332+00:00
-- url     : https://prove2.me/submissions/053fb81e-fe77-48cf-b38a-9ea1ef339884

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_ThirdJetIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_SigmaConstantAgrees
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_IntegralThirdInvariantDerivative
import Theorems.Thm_Formalism_L2_Th1_C_Clo_CoeffCont_subst


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
variable {K : Type} [Field K]
namespace Formalism.L2.Th1.C.FormalGroupJetIntegrality
theorem _root_.solution {τ : Type} (g : PowerSeries K) :
    PowerSeries.subst (0 : MvPowerSeries τ K) g =
      MvPowerSeries.C (PowerSeries.constantCoeff g) := by
  classical
  ext e
  rw [PowerSeries.coeff_subst PowerSeries.HasSubst.zero]
  rw [finsum_eq_single _ 0 (fun d hd => by simp [zero_pow hd])]
  by_cases he : e = 0 <;> simp [he, MvPowerSeries.coeff_C, MvPowerSeries.coeff_one]
end Formalism.L2.Th1.C.FormalGroupJetIntegrality
