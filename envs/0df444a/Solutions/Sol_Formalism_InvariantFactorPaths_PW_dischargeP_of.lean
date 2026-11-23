-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.PW.dischargeP_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:05:56.266853+00:00
-- url     : https://prove2.me/submissions/27454031-71fd-4252-842f-43398c8da11a

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_StatementF
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_Discharge
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_kapC_mono
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_pow_smul_mem_of_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.PW
open MvPolynomial Finset Formalism.GM.M Formalism.GM
namespace Formalism.InvariantFactorPaths.PW
theorem _root_.solution (h1 : ProjP) (h2 : CommP) (h3 : IntP) : DischargeP := by
  intro p _ N r LL ρ e1 he
  unfold Formalism.GM.M.HypP
  refine ⟨fun j _ Cs _ T hT => ?_, fun j j' Cs Cs' T T' P P' hj hC _ _ hP hP' =>
    h2 p N r LL j j' Cs Cs' T T' P P' hj hC hP hP'⟩
  obtain ⟨P, hP, hsym⟩ := h1 p N r LL j Cs T hT
  refine ⟨P, hP, hsym, fun F hF => ?_⟩
  have hcard : Cs.card ≤ r := by simpa using Finset.card_le_univ Cs
  exact pow_smul_mem_of_le _ ((kapC_mono hcard le_rfl).trans he) (h3 p N r LL j Cs T P hT hP F hF)
end Formalism.InvariantFactorPaths.PW
