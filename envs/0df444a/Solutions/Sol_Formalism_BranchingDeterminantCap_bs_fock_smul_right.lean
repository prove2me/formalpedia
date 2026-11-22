-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.bs_fock_smul_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:04:24.362157+00:00
-- url     : https://prove2.me/submissions/13c14cd4-5f6a-47ee-80d1-dcd506d846bd

import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchScale
import Theorems.Thm_Formalism_GradedWeylDivisibility_LFocks_C_mul_right


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Formalism.GradedWeylDivisibility
open Formalism.REAL
noncomputable section
open Formalism Formalism.BranchingDeterminantCap
namespace Formalism.BranchingDeterminantCap
theorem _root_.solution {σ : Type*} (c : ℂ) (f g : MvPolynomial σ ℂ) :
    fockF f (c • g) = star c * fockF f g := by
  rw [smul_eq_C_mul, LFocks_C_mul_right]
end Formalism.BranchingDeterminantCap
