-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.highestWeightVectorRaising
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:37:05.19136+00:00
-- url     : https://prove2.me/submissions/23453b97-d0cf-464a-a3fe-a9b3c18f4839

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LRowdivLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_HWRaise
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowGen_hw

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
open Formalism Formalism.GradedWeylDivisibility
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution : HWRaise := by
  intro R _ r n hn ν a b k hab hk
  unfold rowDiv
  rw [rowGen_hw R hn ν a b hab, Polynomial.coeff_C, if_neg (by omega)]
end Formalism.GradedWeylDivisibility
