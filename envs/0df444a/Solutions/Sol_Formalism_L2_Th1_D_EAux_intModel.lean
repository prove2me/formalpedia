-- Prove2me | solution 1 for Formalism.L2.Th1.D.EAux.intModel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:14:21.097303+00:00
-- url     : https://prove2.me/submissions/64a975f4-f092-48b9-a253-6a54e8fee212

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KurComplete
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_StatementE
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_FlowDouble
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_FinalB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_LubinTateLogIsArtinHasse
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_toDerivation_apply
import Theorems.Thm_Formalism_L2_Th1_A_dLDR_apply
import Theorems.Thm_Formalism_L2_Th1_A_dLD_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] Formalism.L2.Th1.A.IsDer.toDerivation_apply
attribute [local simp] Formalism.L2.Th1.A.dLDR_apply
attribute [local simp] Formalism.L2.Th1.A.dLD_apply



set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.D
open Formalism.DworkPowerSeriesWeights (Integral mvExp BHyp)
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq cob UnrOK IsLawOfLog BetaHyp)
open Formalism.L2.Th1.A (shortW logSer expSer fgl wpReg iSer xS IntModel)
open Formalism.L2.Th1.B (fLog lU sigS phO)
open EAux
open Formalism.L2.Th1.D.EAux
namespace Formalism.L2.Th1.D.EAux
theorem _root_.solution {K : Type} [NormedField K] {g2 g3 : K} (h2 : ‖g2‖ ≤ 1) (h3 : ‖g3‖ ≤ 1)
    (ht : ‖(2 : K)‖ = 1) : IntModel (shortW g2 g3) := by
  have h4 : ‖(4 : K)‖ = 1 := by
    have : (4 : K) = 2 * 2 := by norm_num
    rw [this, norm_mul, ht, mul_one]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [shortW]
  · simp [shortW]
  · simp [shortW]
  · simpa [shortW, h4] using h2
  · simpa [shortW, h4] using h3
end Formalism.L2.Th1.D.EAux
