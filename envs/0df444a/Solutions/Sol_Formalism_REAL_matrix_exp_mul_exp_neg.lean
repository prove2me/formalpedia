-- Prove2me | solution 1 for Formalism.REAL.matrix_exp_mul_exp_neg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:12:11.246014+00:00
-- url     : https://prove2.me/submissions/d6776247-3c52-45c6-a163-4b0e92480a71

import Definitions.Def_Formalism_RealPlaceAnalysis_Complexify
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_IndefiniteUnitaryPreservesForm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder
noncomputable section
open Formalism Formalism.REAL
variable {n : ℕ}
namespace Formalism.REAL
theorem _root_.solution (A : Matrix (Fin n) (Fin n) ℂ) :
    NormedSpace.exp A * NormedSpace.exp (-A) = 1 := by
  rw [← Matrix.exp_add_of_commute _ _ (Commute.neg_right (Commute.refl A)), add_neg_cancel]
  first | exact Matrix.exp_zero | exact NormedSpace.exp_zero
end Formalism.REAL
