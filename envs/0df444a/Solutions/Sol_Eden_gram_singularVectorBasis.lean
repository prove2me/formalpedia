-- Prove2me | solution 1 for Eden.gram_singularVectorBasis
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:46:08.556101+00:00
-- url     : https://prove2.me/submissions/f1a26faa-0a29-4018-93c8-e70defa9ff26

import Definitions.Def_Eden_ExteriorOperatorNorm
import Definitions.Def_Eden_ExteriorGram

set_option autoImplicit true
noncomputable section
open scoped RealInnerProductSpace
open Eden
namespace Eden
theorem _root_.solution (A : PhaseSpace →ₗ[ℝ] PhaseSpace) (i : Fin 5) :
    (A.adjoint ∘ₗ A) (singularVectorBasis A i) =
      A.singularValues i ^ 2 • singularVectorBasis A i := by
  rw [A.sq_singularValues_fin finrank_euclideanSpace_fin i]
  exact A.isSymmetric_adjoint_comp_self.apply_eigenvectorBasis _ i
end Eden
