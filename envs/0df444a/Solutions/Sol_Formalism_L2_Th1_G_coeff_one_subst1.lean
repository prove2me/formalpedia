-- Prove2me | solution 1 for Formalism.L2.Th1.G.coeff_one_subst1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:40:49.279678+00:00
-- url     : https://prove2.me/submissions/4aba1718-2c9c-48d2-a77e-0083029bca2e

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_StatementR
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_FirstLevelFromUniversalLaw
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_PairedSquareJets_Hurwitz
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_PairedSquareJets_HurwitzB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_PairedSquareJets_InverseEndoIntegralHolds
import Theorems.Thm_Formalism_ELL_FormalGroupPointsTorsion_key
import Theorems.Thm_Formalism_FG_FormalGroupCoefficients_key
import Theorems.Thm_Formalism_L2_Th1_C_Clo_CoeffCont_subst
import Theorems.Thm_Formalism_L2_Th1_C_JetSubstitutionLemmas_cc_subst1
import Theorems.Thm_Formalism_L2_Th1_C_JetSubstitutionLemmas_hs1
import Theorems.Thm_Formalism_LT_InvIntP_key


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
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.G
open Formalism.L2.Th1.C
open Formalism.G (unitBall)
variable {K : Type} [Field K]
namespace Formalism.L2.Th1.G
theorem _root_.solution (g : PowerSeries K) {a : PowerSeries K}
    (ha : PowerSeries.constantCoeff a = 0) :
    PowerSeries.coeff 1 (PowerSeries.subst a g : PowerSeries K) =
      PowerSeries.coeff 1 g * PowerSeries.coeff 1 a := by
  have key : ∀ f : PowerSeries K, PowerSeries.coeff 1 f =
      PowerSeries.constantCoeff (PowerSeries.derivative K f) := by
    intro f
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_derivative]
    simp
  rw [key, PowerSeries.derivative_subst (JetSubstitutionLemmas.hs1 ha), map_mul, JetSubstitutionLemmas.cc_subst1 ha, ← key, ← key]
end Formalism.L2.Th1.G
