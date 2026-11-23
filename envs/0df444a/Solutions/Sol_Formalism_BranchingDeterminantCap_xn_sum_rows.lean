-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.xn_sum_rows
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:35:41.914704+00:00
-- url     : https://prove2.me/submissions/d4af8be0-0238-40f6-ab26-997e0abefb28

import Mathlib
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ProdFactorialSupportSubSingle
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LFocksLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LFockbLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LBidetMinor
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LBidetLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_DualWeylNonDom
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_XiNorm
import Theorems.Thm_Formalism_BranchingDeterminantCap_xn_pderiv_supported
import Theorems.Thm_Formalism_BranchingDeterminantCap_xn_sum_castLE

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
theorem _root_.solution {k : ℕ} (hk : k ≤ r) {f : MvPolynomial (Fin r × Fin n) ℂ}
    (hs : f ∈ supported ℂ {v : Fin r × Fin n | v.1.val < k}) (t s : Fin n) :
    ∑ b : Fin k, X (Fin.castLE hk b, t) * pderiv (Fin.castLE hk b, s) f =
      ∑ b : Fin r, X (b, t) * pderiv (b, s) f := by
  refine xn_sum_castLE hk (fun b => X (b, t) * pderiv (b, s) f) ?_
  intro b hb
  show X (b, t) * pderiv (b, s) f = 0
  rw [xn_pderiv_supported _ (b, s) (by intro h; simp only [Set.mem_setOf_eq] at h; omega) f hs, mul_zero]
end Formalism.BranchingDeterminantCap
