-- Prove2me | solution 1 for Formalism.MainNotions.flipOneThree.Pf.ShapeCovering.signed_minors_cofactor_transform
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:33:19.991684+00:00
-- url     : https://prove2.me/submissions/1ab95d44-03f0-442f-b1b0-248228750ad5

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_HermitianTensor_ShapeCovering_StatementY
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_HermitianTensor_ShapeCovering_CovDet
import Theorems.Thm_Formalism_MainNotions_flipOneThree_Pf_ShapeCovering_signed_minors_cofactor_adjugate

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.flipOneThree Formalism.MainNotions.flipOneThree.Pf Formalism.MainNotions.flipOneThree.Pf.ShapeCovering
open MvPolynomial Formalism.GradedWeylDivisibility
namespace Formalism.MainNotions.flipOneThree.Pf.ShapeCovering
theorem _root_.solution : SignedMinorsCofactorTransform := by
  intro K _ m g i hg
  rw [signed_minors_cofactor_adjugate K m g i, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← mul_assoc, ← C_mul, Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, ← mul_assoc,
    Ring.mul_inverse_cancel _ hg, one_mul]
end Formalism.MainNotions.flipOneThree.Pf.ShapeCovering
