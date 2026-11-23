-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.xn_E_X
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:30:46.129723+00:00
-- url     : https://prove2.me/submissions/68040ab3-225a-406c-8fec-60de36d898a7

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
variable {r n : ℕ}
namespace Formalism.BranchingDeterminantCap
theorem _root_.solution (t s : Fin n) (v : Fin r × Fin n) :
    ∑ b : Fin r, (X (b, t) : MvPolynomial (Fin r × Fin n) ℂ) * pderiv (b, s) (X v) =
      if v.2 = s then X (v.1, t) else 0 := by
  simp only [MvPolynomial.pderiv_X, Pi.single_apply, mul_ite, mul_one, mul_zero]
  obtain ⟨v1, v2⟩ := v
  by_cases h : v2 = s
  · subst h
    simp
  · simp [h]
end Formalism.BranchingDeterminantCap
