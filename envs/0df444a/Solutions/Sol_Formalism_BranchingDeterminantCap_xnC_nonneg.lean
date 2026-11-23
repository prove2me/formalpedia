-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.xnC_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:30:29.264948+00:00
-- url     : https://prove2.me/submissions/1af10a1c-989e-4360-a40c-7e5a4beb9b6a

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
theorem _root_.solution (M : ℕ) (m : ℕ → ℕ) (p : ℕ) (hp : p ≤ M) : 0 ≤ xnC M m p := by
  unfold xnC
  refine Finset.prod_nonneg fun q hq => ?_
  have hq' : q < p := Finset.mem_range.1 hq
  have h1 : (q : ℝ) ≤ M := by exact_mod_cast (by omega : q ≤ M)
  have h2 : (0 : ℝ) ≤ m q := Nat.cast_nonneg _
  linarith
end Formalism.BranchingDeterminantCap
