-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.LFocks_sub_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:00:51.59094+00:00
-- url     : https://prove2.me/submissions/9e065057-b67f-446c-b4fe-36998e4f90e9

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ProdFactorialSupportSubSingle
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LFocksLemmas
import Theorems.Thm_Formalism_GradedWeylDivisibility_LFocks_sub_X

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Formalism.REAL
noncomputable section
open Formalism Formalism.GradedWeylDivisibility
variable {σ : Type*} [Fintype σ]
variable [DecidableEq σ]
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution : sub (1 : Matrix σ σ ℂ) = AlgHom.id ℂ (MvPolynomial σ ℂ) := by
  refine MvPolynomial.algHom_ext fun i => ?_
  simp [LFocks_sub_X, Matrix.one_apply]
end Formalism.GradedWeylDivisibility
