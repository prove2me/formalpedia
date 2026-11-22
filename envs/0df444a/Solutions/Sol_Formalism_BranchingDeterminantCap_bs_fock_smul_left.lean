-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.bs_fock_smul_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:04:24.294845+00:00
-- url     : https://prove2.me/submissions/5fb8f856-86aa-4d27-a79d-85c82f84093e

import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchScale
import Theorems.Thm_Formalism_GradedWeylDivisibility_LFocks_C_mul_left


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
    fockF (c • f) g = c * fockF f g := by
  rw [smul_eq_C_mul, LFocks_C_mul_left]
end Formalism.BranchingDeterminantCap
