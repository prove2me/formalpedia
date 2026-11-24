-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.typesLE_le_ycondC
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:52:51.203654+00:00
-- url     : https://prove2.me/submissions/547ea4e5-7d39-4c08-94e8-ae4f084db658

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_FirstWeightLeOfSupport
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_TypesLELeYcondC
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_isoC_le_ycondC

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.CountingSumsFrames MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution [NeZero r] (LL : Letters N) (j : ℕ) (Cs : Finset (Fin r)) (h0 : (0 : Fin r) ∈ Cs)
    (Mt : WithTop ℤ) : TypesLE p LL j Cs Mt ≤ YCondC p LL j Cs Mt :=
  iSup_le fun la => iSup_le fun hla => isoC_le_ycondC LL j Cs h0 la Mt hla
end Formalism.InvariantFactorPaths.L4
