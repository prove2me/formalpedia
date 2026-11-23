-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.xnW_weylProd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:30:45.859161+00:00
-- url     : https://prove2.me/submissions/5e7e0e9a-6d89-448d-bc2e-30276f4ad4e6

import Mathlib
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ProdFactorialSupportSubSingle
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LFocksLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LFockbLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LBidetMinor
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LBidetLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_DualWeylNonDom
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_XiNorm

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
namespace Formalism.BranchingDeterminantCap
theorem _root_.solution (n : ℕ) (μ : ℕ → ℕ) :
    weylProd (fun a : Fin (n + 1) => ((μ a.val : ℕ) : ℤ)) = xnW (n + 1) μ := by
  unfold weylProd xnW
  rw [Finset.prod_filter, Fintype.prod_prod_type]
  simp only [Finset.prod_range]
  refine Finset.prod_congr rfl fun a _ => Finset.prod_congr rfl fun b _ => ?_
  simp only [xnT, Fin.lt_iff_val_lt_val]
  split_ifs <;> push_cast <;> ring
end Formalism.BranchingDeterminantCap
