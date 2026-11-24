-- Prove2me | solution 1 for Formalism.CyclotomicNorms.irreducibility_of_restriction
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:40:38.694438+00:00
-- url     : https://prove2.me/submissions/c4ef520a-97a8-4dbc-9bd1-433d16235d8c

import Definitions.Def_Formalism_CyclotomicNorms_StatementT
import Definitions.Def_Formalism_GaloisIrreducibility_NoSolvableTransitive
import Definitions.Def_Lemmata_GeneralBFactSecondBis_Imports
import Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_IrreducibilityOfRestriction
import Theorems.Thm_Formalism_CyclotomicNorms_CycleTypeFiniteOrder_t1

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
noncomputable section
namespace Formalism.CyclotomicNorms
theorem _root_.solution (hR : Formalism.CyclotomicNorms.Restriction) : Formalism.CyclotomicNorms.IrreducibilityCriterion :=
  Formalism.CyclotomicNorms.CycleTypeFiniteOrder.t1 hR
end Formalism.CyclotomicNorms
