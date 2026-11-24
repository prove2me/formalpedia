-- Prove2me | solution 1 for Formalism.L2.Th1.D.Pair.exp_log
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:00:10.705816+00:00
-- url     : https://prove2.me/submissions/93f7e2f9-74c6-4401-ab0e-43004153ed50

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_LetterShift
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FinalS
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_SubstFirstCoboundaryThree
import Theorems.Thm_Formalism_L2_Th1_D_Pair_ps_comp
import Theorems.Thm_Formalism_L2_Th1_D_Pair_cc_lgF

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
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.D
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq DivAB d1 swap2 in3 cob UnrOK IsLawOfLog SimeqRules)
open MvPowerSeries
open Formalism.L2.Th1.D.Pair
variable {K : Type} [Field K]
namespace Formalism.L2.Th1.D.Pair
theorem _root_.solution (hE : ExpSpec) {l : ℕ} (hl : 2 ≤ l) {τ : Type} {a : MvPowerSeries τ K}
    (ha : constantCoeff a = 0) :
    PowerSeries.subst (PowerSeries.subst a (lgF K l)) (expF K l) = a := by
  rw [ps_comp ha (cc_lgF hl) (expF K l), (hE K l hl).2.2.1]
  first
  | exact PowerSeries.subst_X (PowerSeries.HasSubst.of_constantCoeff_zero ha)
  | simp [PowerSeries.subst_X, PowerSeries.HasSubst.of_constantCoeff_zero ha]
end Formalism.L2.Th1.D.Pair
