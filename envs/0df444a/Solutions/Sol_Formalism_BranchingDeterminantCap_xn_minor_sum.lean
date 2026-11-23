-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.xn_minor_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:31:33.88097+00:00
-- url     : https://prove2.me/submissions/b7dda486-2b74-4fca-8f19-efbbee40b5ae

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
variable {r n : ℕ} {κ : Type} [Fintype κ] [DecidableEq κ]
namespace Formalism.BranchingDeterminantCap
theorem _root_.solution (ι : κ → Fin r) {p : ℕ} (hp : p ≤ n) (a : Fin p → κ) :
    initMinor ℂ (ι ∘ a) hp = ∑ π : Equiv.Perm (Fin p), C (xnSg π) * xnMono ι hp (a ∘ π) := by
  unfold initMinor xnMono xnSg
  rw [Matrix.det_apply']
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [map_intCast]
  rfl
end Formalism.BranchingDeterminantCap
