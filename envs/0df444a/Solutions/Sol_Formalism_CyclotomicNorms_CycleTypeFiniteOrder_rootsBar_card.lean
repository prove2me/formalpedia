-- Prove2me | solution 1 for Formalism.CyclotomicNorms.CycleTypeFiniteOrder.rootsBar_card
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:58:37.302692+00:00
-- url     : https://prove2.me/submissions/ea3c3b8c-eda9-4311-a6ce-59eeb1b8a6ab

import Definitions.Def_Formalism_CyclotomicNorms_StatementT
import Definitions.Def_Formalism_GaloisIrreducibility_NoSolvableTransitive
import Definitions.Def_Lemmata_GeneralBFactSecondBis_Imports
import Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_IrreducibilityOfRestriction

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
open Formalism Formalism.CyclotomicNorms Formalism.CyclotomicNorms.CycleTypeFiniteOrder
variable {g : ℕ} [hg : Fact g.Prime]
variable {N : ℕ} {f : (ZMod g)[X]}
namespace Formalism.CyclotomicNorms.CycleTypeFiniteOrder
theorem _root_.solution (hf : GoodPoly N f) : (rootsBar f).card = N := by
  unfold rootsBar; rw [IsAlgClosed.card_roots_eq_natDegree, natDegree_map, hf.deg]
end Formalism.CyclotomicNorms.CycleTypeFiniteOrder
