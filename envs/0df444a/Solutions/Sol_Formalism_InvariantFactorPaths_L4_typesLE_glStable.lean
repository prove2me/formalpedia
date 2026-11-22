-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.typesLE_glStable
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:43:51.803831+00:00
-- url     : https://prove2.me/submissions/2b2f9a66-a751-4ac2-b944-6a0fc020c67b

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementD
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_RaisingKeepsEarlyLetters
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_Sl2RaisePowSuccLowerApplyEq
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_EArith
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_TypesLELeYcondC
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_OmegaInjectiveHolds
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_isoC_glStableC


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
variable {p : ℕ} [Fact p.Prime] {K r : ℕ}
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution {N : ℕ} [NeZero r] (LL : Letters N) (j : ℕ) (Cs : Finset (Fin r)) (M : WithTop ℤ) (s t : Fin r)
    (hs : s ∈ Cs) (ht : t ∈ Cs) : ∀ z ∈ TypesLE p LL j Cs M, glAct p LL j s t z ∈ TypesLE p LL j Cs M := by
  have : TypesLE p LL j Cs M ≤ (TypesLE p LL j Cs M).comap (glAct p LL j s t) :=
    iSup_le fun la => iSup_le fun hla => fun z hz =>
      Submodule.mem_iSup_of_mem la (Submodule.mem_iSup_of_mem hla (isoC_glStableC LL j Cs la s hs t ht z hz))
  exact fun z hz => this hz
end Formalism.InvariantFactorPaths.L4
