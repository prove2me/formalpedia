-- Prove2me | solution 1 for Formalism.L2.Th1.B.ParO.ParO_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:36:42.864211+00:00
-- url     : https://prove2.me/submissions/f9fc746c-7219-4773-8dfd-22df771e3ccb

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementA
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_OneAddMulDerivLogSubst
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_InVarAddInVarNeZero
import Theorems.Thm_Formalism_L2_Th1_B_ParO_par_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B Formalism.L2.Th1.B.ParO
open Formalism.DworkPowerSeriesWeights (Integral)
open Formalism.InvariantFactorPaths.G7 (Simeq at1 cob)
namespace Formalism.L2.Th1.B.ParO
theorem _root_.solution (hA : AddSgStar) (hD : PhODef) (hL : SimeqLog) : ParO := by
  intro K _ _ _ g2 g3 s2 c0 P l i ep F hP hF hi hCC
  obtain ⟨-, -, h3, c, hcI, hc1, hc⟩ := hCC
  rw [par_eq hA hD hP hF hi h3 hc]
  have h1 : MvPowerSeries.constantCoeff (-c) = 1 := by rw [map_neg, hc1, neg_neg]
  have hI : Formalism.DworkPowerSeriesWeights.Integral (-c) := by
    intro n
    rw [map_neg, norm_neg]
    exact hcI n
  exact (hL K (Fin 2) (-c) h1 hI).2
end Formalism.L2.Th1.B.ParO
