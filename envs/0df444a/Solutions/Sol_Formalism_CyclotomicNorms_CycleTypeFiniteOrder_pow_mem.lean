-- Prove2me | solution 1 for Formalism.CyclotomicNorms.CycleTypeFiniteOrder.pow_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:06:39.690989+00:00
-- url     : https://prove2.me/submissions/ad69f558-acac-4f1b-af57-19851a478efa

import Definitions.Def_Formalism_CyclotomicNorms_StatementT
import Definitions.Def_Formalism_GaloisIrreducibility_NoSolvableTransitive
import Definitions.Def_Lemmata_GeneralBFactSecondBis_Imports
import Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_IrreducibilityOfRestriction
import Theorems.Thm_Formalism_CyclotomicNorms_CycleTypeFiniteOrder_eval_pow_map
import Theorems.Thm_Formalism_CyclotomicNorms_CycleTypeFiniteOrder_mem_rootsBar

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
theorem _root_.solution (hf : GoodPoly N f) {x : Fbar g} (hx : x ∈ rootsBar f) : x ^ g ∈ rootsBar f := by
  rw [mem_rootsBar hf, eval_pow_map, (mem_rootsBar hf).mp hx, zero_pow hg.out.ne_zero]
end Formalism.CyclotomicNorms.CycleTypeFiniteOrder
