-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.raising_divided_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:11:56.016039+00:00
-- url     : https://prove2.me/submissions/9feda32c-b660-4d1c-9652-773bd2f814bd

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementG
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_RaisingKeepsEarlyLetters
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_DerivativeDividedIntegral
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_udiv_map
import Theorems.Thm_Formalism_GM_FrozenVariableLemmas_intPol_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.MeanGammaLemmas Formalism.CountingSumsFrames MvPolynomial Finset
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution : UDivInt := by
  intro p _ K r LL c Cs a k ha x hx
  obtain ⟨P, rfl⟩ := (FrozenVariableLemmas.intPol_iff p x).mp hx
  exact udiv_map LL Cs a ha P c k
end Formalism.InvariantFactorPaths.L4
