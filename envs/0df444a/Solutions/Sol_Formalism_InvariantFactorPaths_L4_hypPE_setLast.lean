-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.hypPE_setLast
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:14:49.799209+00:00
-- url     : https://prove2.me/submissions/6c15ca56-4afe-48c4-a1df-f1d10cf7ca70

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementG
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementF
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_MulEarlyModP
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_DischargeHeightBound
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_FinalM
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_GramBoundUnconditionalOfSat
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_setLast_total_le
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_kapC_mono
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_Top_dischargeE
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_Top_dischargeP
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_kapC_mono


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.MeanGammaLemmas Formalism.CountingSumsFrames Formalism.InvariantFactorPaths.PW MvPolynomial Finset
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution {p : ℕ} [Fact p.Prime] {K r : ℕ} (LLw : Letters (K + 1)) (ρ : Fin r) :
    ∀ o ≤ LLw.deg (Fin.last K),
      HypP p (setLast LLw o) ρ (kapC p r LLw.total) ∧ HypE p (setLast LLw o) ρ (kapC p r LLw.total) :=
  fun o ho =>
    ⟨Formalism.InvariantFactorPaths.PW.Top.dischargeP p (K + 1) r (setLast LLw o) ρ _ (kapC_mono p r (setLast_total_le LLw o ho)),
      Formalism.InvariantFactorPaths.PW.Top.dischargeE p (K + 1) r (setLast LLw o) ρ _ (kapC_mono p r (setLast_total_le LLw o ho))⟩
end Formalism.InvariantFactorPaths.L4
