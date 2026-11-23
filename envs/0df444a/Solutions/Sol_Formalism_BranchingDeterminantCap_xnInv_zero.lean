-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.xnInv_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:35:41.247304+00:00
-- url     : https://prove2.me/submissions/a76c9e02-0fa6-4f8f-a862-bc22f7af83cc

import Mathlib
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ProdFactorialSupportSubSingle
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LFocksLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LFockbLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LBidetMinor
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LBidetLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_DualWeylNonDom
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_XiNorm
import Theorems.Thm_Formalism_BranchingDeterminantCap_xnW_zero
import Theorems.Thm_Formalism_GradedWeylDivisibility_one_mem_dualWeyl


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Formalism.GradedWeylDivisibility Formalism.REAL
noncomputable section
open Formalism Formalism.BranchingDeterminantCap
variable {r n : ℕ}
namespace Formalism.BranchingDeterminantCap
theorem _root_.solution : xnInv 0 (fun _ => 0) (1 : MvPolynomial (Fin r × Fin n) ℂ) 1 := by
  have h1 : (1 : MvPolynomial (Fin r × Fin n) ℂ) ∈ dualWeyl ℂ r n (fun q => (fun _ => 0) q.val) :=
    one_mem_dualWeyl
  exact ⟨fun q _ => rfl, h1, h1, one_mem _, le_of_eq (by rw [xnW_zero, one_mul])⟩
end Formalism.BranchingDeterminantCap
