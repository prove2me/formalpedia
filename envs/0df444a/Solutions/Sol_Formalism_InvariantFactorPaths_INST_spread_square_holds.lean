-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.INST.spread_square_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T09:57:40.476472+00:00
-- url     : https://prove2.me/submissions/ea5c27ce-928c-40a8-89a6-3557b0cc1a1f

import Definitions.Def_Formalism_ThetaLogCoordinates_SandwichModelDomains_SpreadSquare
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LDbasisLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LDrowLemmas
import Definitions.Def_Formalism_ThetaLogCoordinates_SandwichModelDomains_SandwichModelProofs_Spread
import Theorems.Thm_Formalism_InvariantFactorPaths_INST_spr_upper
import Theorems.Thm_Formalism_InvariantFactorPaths_INST_spr_lower

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.INST
open Formalism.GradedWeylDivisibility
namespace Formalism.InvariantFactorPaths.INST
theorem _root_.solution : SpreadSquare := by
  intro R _ _ n ν l hl f hf g hg m hm m' hm' a
  have : Nonempty (Fin n) := ⟨a⟩
  obtain ⟨s, hs⟩ := Finite.exists_max ν
  obtain ⟨t, ht⟩ := Finite.exists_min ν
  have h1 := spr_upper R n n ν (ν s) hs f hf m hm a
  have h2 := spr_lower R n ν (ν t) ht g hg m' hm' a
  have h3 := hl s t
  omega
end Formalism.InvariantFactorPaths.INST
