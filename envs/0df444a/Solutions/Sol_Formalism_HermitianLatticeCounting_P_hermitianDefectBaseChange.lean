-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.hermitianDefectBaseChange
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:00:48.758077+00:00
-- url     : https://prove2.me/submissions/3cb73ad2-5195-4315-863a-e9ed9481b9dc

import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubmodulesAndLinearEquivBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeSumBounds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Matrix Formalism.HermitianLatticeCounting.LatticeSumBounds
open scoped BigOperators ComplexConjugate
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : PhiBaseChange := by
  intro n R _ _ _ _ S Y g hg
  have h1 : ∀ X : Matrix n n R, g⁻¹ * (g * X) = X := by
    intro X; rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul g hg, Matrix.one_mul]
  have h2 : ∀ X : Matrix n n R, gᴴ * ((g⁻¹)ᴴ * X) = X := by
    intro X
    rw [← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, Matrix.nonsing_inv_mul g hg,
      Matrix.conjTranspose_one, Matrix.one_mul]
  unfold Formalism.HermitianLatticeCounting.LatticeSumBounds.Phi
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc, h1, h2]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
end Formalism.HermitianLatticeCounting.P
