-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.castSucc_mem_erase
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T02:01:42.945798+00:00
-- url     : https://prove2.me/submissions/15a95cb7-4390-47bb-9480-9f4d6bd4730a

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_LatDefs
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_MulEarlyModP
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_Vanish
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_DischargeHeightBound
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_DerivativeKillsDegreeZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.MeanGammaLemmas Formalism.GM.DimensionMonotonicity Formalism.CountingSumsFrames Formalism.InvariantFactorPaths.PW MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {K s : ℕ}
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution (i : Fin s) : Fin.castSucc i ∈ (univ : Finset (Fin (s + 1))).erase (Fin.last s) :=
  Finset.mem_erase.2 ⟨(Fin.castSucc_lt_last i).ne, Finset.mem_univ _⟩
end Formalism.InvariantFactorPaths.L4
