-- Prove2me | solution 1 for Formalism.CyclotomicNorms.CycleTypeFiniteOrder.ne_zero_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:10:47.978016+00:00
-- url     : https://prove2.me/submissions/834561d7-1520-4625-a3cf-0e6e01eeb21f

import Definitions.Def_Formalism_CyclotomicNorms_StatementT
import Definitions.Def_Formalism_GaloisIrreducibility_NoSolvableTransitive
import Definitions.Def_Lemmata_GeneralBFactSecondBis_Imports
import Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_IrreducibilityOfRestriction
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
theorem _root_.solution (hf : GoodPoly N f) {x : Fbar g} (hx : x ∈ rootsBar f) : x ≠ 0 := by
  rintro rfl
  have h := (mem_rootsBar hf).mp hx
  rw [← coeff_zero_eq_eval_zero, coeff_map] at h
  exact hf.coeff0 ((map_eq_zero_iff _ (algebraMap (ZMod g) (Fbar g)).injective).mp h)
end Formalism.CyclotomicNorms.CycleTypeFiniteOrder
