-- Prove2me | solution 1 for Formalism.MainNotions.G.Inhab.one_mem_weyl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:40:14.213808+00:00
-- url     : https://prove2.me/submissions/c6e3fea8-d16e-48d2-bc51-6afb3d00bc9a

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
theorem _root_.solution (k : ℕ) : (1 : MvPolynomial (Fin k × Fin k) R) ∈ weyl R k k le_rfl 0 := by
  have h1 : hw R (le_refl k) (0 : Fin k → ℕ) = 1 := by
    simp [hw]
  exact Submodule.subset_span ⟨[], by simp [applyWord, h1]⟩
end Formalism.MainNotions.G.Inhab
