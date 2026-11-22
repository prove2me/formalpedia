-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.xn_pderiv_supported
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:03:13.923424+00:00
-- url     : https://prove2.me/submissions/72082ea4-d889-4387-a482-07ca8bafa322

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
theorem _root_.solution {σ : Type*} (s : Set σ) (v : σ) (hv : v ∉ s) (f : MvPolynomial σ ℂ)
    (hf : f ∈ supported ℂ s) : pderiv v f = 0 := by
  rw [MvPolynomial.mem_supported] at hf
  first
  | exact MvPolynomial.pderiv_eq_zero_of_notMem_vars fun hv' => hv (hf hv')
  | exact MvPolynomial.pderiv_eq_zero_of_not_mem_vars fun hv' => hv (hf hv')
end Formalism.BranchingDeterminantCap
