-- Prove2me | solution 1 for Formalism.MainNotions.G.Inhab.one_mem_dualWeyl
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:44:57.998641+00:00
-- url     : https://prove2.me/submissions/f5bfd5bb-8d20-4c82-8f7c-81fe6e65790b

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TensorLatticeBounds_DataLoc
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TensorLatticeBounds_DataForm
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.G.Inhab
open Formalism.MainNotions.G Formalism.GradedWeylDivisibility MvPolynomial
variable (R K : Type*) [CommRing R] [Field K] [Algebra R K]
namespace Formalism.MainNotions.G.Inhab
theorem _root_.solution (r n : ℕ) : (1 : MvPolynomial (Fin r × Fin n) R) ∈ dualWeyl R r n 0 := by
  refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
  · apply isWeightedHomogeneous_one
  · simp only [Submodule.mem_iInf, LinearMap.mem_ker]
    intro l j _
    simp
end Formalism.MainNotions.G.Inhab
