-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.majDual_mat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:53:55.027556+00:00
-- url     : https://prove2.me/submissions/53904ef7-8b12-43db-9a56-e0b35e8f9afe

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementMaj
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_MajLattice
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_MajDual

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open scoped nonZeroDivisors
noncomputable section
open Formalism Formalism.HermitianLatticesTheory
variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Fintype ι] [DecidableEq ι]
namespace Formalism.HermitianLatticesTheory
theorem _root_.solution (G X : Matrix ι ι ℂ) (hX : IsUnit X.det) (a c : ι → ℂ) :
    dotProduct (star (X⁻¹.mulVec a)) (((X.conjTranspose * G * X)).mulVec (X⁻¹.mulVec c)) =
      dotProduct (star a) (G.mulVec c) := by
  have h1 : X * X⁻¹ = 1 := Matrix.mul_nonsing_inv X hX
  have e1 : (X.conjTranspose * G * X).mulVec (X⁻¹.mulVec c) = X.conjTranspose.mulVec (G.mulVec c) := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, h1, Matrix.mul_one, Matrix.mulVec_mulVec]
  rw [e1, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec, Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
end Formalism.HermitianLatticesTheory
