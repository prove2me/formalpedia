-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.xnC_ite
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:30:12.89101+00:00
-- url     : https://prove2.me/submissions/b0e2329f-e030-44c3-9382-606c780fbc22

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
theorem _root_.solution (M : ℕ) (m : ℕ → ℕ) (p N : ℕ) (hp : p ≤ N) :
    xnC M m p = ∏ i ∈ Finset.range N, if i < p then ((M : ℝ) - i + m i) else 1 := by
  unfold xnC
  rw [← Finset.prod_filter]
  congr 1
  ext i
  simp only [Finset.mem_range, Finset.mem_filter]
  omega
end Formalism.BranchingDeterminantCap
