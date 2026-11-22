-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.xn_det_supported
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:26:59.604566+00:00
-- url     : https://prove2.me/submissions/7552d386-4657-4a5c-ba72-714a62a7f59f

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
theorem _root_.solution {σ m : Type*} [Fintype m] [DecidableEq m] (s : Set σ)
    (A : Matrix m m (MvPolynomial σ ℂ)) (h : ∀ i j, A i j ∈ supported ℂ s) :
    A.det ∈ supported ℂ s := by
  rw [Matrix.det_apply']
  refine sum_mem fun τ _ => mul_mem ?_ (prod_mem fun i _ => h _ _)
  first
  | exact intCast_mem _ _
  | exact Subalgebra.intCast_mem _ _
  | (rw [← map_intCast (algebraMap ℂ (MvPolynomial σ ℂ))]; exact Subalgebra.algebraMap_mem _ _)
end Formalism.BranchingDeterminantCap
