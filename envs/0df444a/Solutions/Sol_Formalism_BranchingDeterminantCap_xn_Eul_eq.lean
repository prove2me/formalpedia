-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.xn_Eul_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:31:02.026729+00:00
-- url     : https://prove2.me/submissions/298e2242-313d-4fa8-b865-5284d7ad6ba1

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
theorem _root_.solution (s : Fin n) : ndEul ℂ r n s = ndE ℂ r n s s := by
  apply MvPolynomial.derivation_ext
  intro v
  simp only [ndEul, ndE, MvPolynomial.mkDerivation_X, colW]
  obtain ⟨v1, v2⟩ := v
  by_cases h : v2 = s
  · subst h
    simp
  · simp [h, Pi.single_apply, Ne.symm h]
end Formalism.BranchingDeterminantCap
