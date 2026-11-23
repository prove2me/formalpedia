-- Prove2me | solution 1 for Formalism.CyclotomicNorms.CycleTypeFiniteOrder.mem_rootsBar
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:06:59.13865+00:00
-- url     : https://prove2.me/submissions/878b7346-db13-4ac2-b8b9-03c4cd80270d

import Definitions.Def_Formalism_CyclotomicNorms_StatementT
import Definitions.Def_Formalism_GaloisIrreducibility_NoSolvableTransitive
import Definitions.Def_Lemmata_GeneralBFactSecondBis_Imports
import Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_IrreducibilityOfRestriction
import Theorems.Thm_P2M_Formalism_CyclotomicNorms_CycleTypeFiniteOrder_map_ne_zero__0cc604524e09

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
theorem _root_.solution (hf : GoodPoly N f) {x : Fbar g} :
    x ∈ rootsBar f ↔ (f.map (algebraMap (ZMod g) (Fbar g))).eval x = 0 := by
  unfold rootsBar; rw [mem_roots (map_ne_zero' hf)]; rfl
end Formalism.CyclotomicNorms.CycleTypeFiniteOrder
