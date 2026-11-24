-- Prove2me | solution 1 for Formalism.L2.Th1.D.Pair.addC_log
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:26:40.728812+00:00
-- url     : https://prove2.me/submissions/693e92dd-36f6-482c-b283-c0b3b896b8f0

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_LetterShift
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FinalS
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_SubstFirstCoboundaryThree
import Theorems.Thm_Formalism_L2_Th1_D_Pair_hs2
import Theorems.Thm_Formalism_L2_Th1_D_Pair_subst_single_var
import Theorems.Thm_Formalism_L2_Th1_D_Pair_constantCoeff_inVar_eq_zero
import Theorems.Thm_Formalism_L2_Th1_D_Pair_cc_ps
import Theorems.Thm_Formalism_L2_Th1_D_Pair_cc_lgF
import Theorems.Thm_Formalism_L2_Th1_D_Pair_exp_log
import Theorems.Thm_Formalism_G_LogP_hs2
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_CoboundarySeries_subst_single_var
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_FormalGroupLaws_subst_single_var
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_FrobeniusSubstitution_subst_single_var
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_GramFrameCompositionLinFacts_hs2


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
theorem _root_.solution (hE : ExpSpec) {l : ℕ} (hl : 2 ≤ l) {τ : Type} {a b : MvPowerSeries τ K}
    (ha : constantCoeff a = 0) (hb : constantCoeff b = 0) (be0 : MvPowerSeries (Fin 2) K) :
    subst ![PowerSeries.subst a (lgF K l), PowerSeries.subst b (lgF K l)] (addC l be0) =
      subst ![a, b] be0 := by
  have hA : constantCoeff (PowerSeries.subst a (lgF K l)) = 0 := cc_ps ha (cc_lgF hl)
  have hB : constantCoeff (PowerSeries.subst b (lgF K l)) = 0 := cc_ps hb (cc_lgF hl)
  have hE0 := (hE K l hl).1
  have h2 := hs2 hA hB
  unfold addC
  rw [subst_comp_subst_apply (hs2 (constantCoeff_inVar_eq_zero (0 : Fin 2) hE0) (constantCoeff_inVar_eq_zero (1 : Fin 2) hE0)) h2]
  congr 1
  funext i
  fin_cases i
  · exact (subst_single_var h2 0 (expF K l)).trans (exp_log hE hl ha)
  · exact (subst_single_var h2 1 (expF K l)).trans (exp_log hE hl hb)
end Formalism.L2.Th1.D.Pair
