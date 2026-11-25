-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.xn_W_ratio
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:39:06.099315+00:00
-- url     : https://prove2.me/submissions/b6bbdf4f-dc37-4f8d-a8e1-a7c0d2ee6ec9

import Mathlib
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ProdFactorialSupportSubSingle
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LFocksLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LFockbLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LBidetMinor
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LBidetLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_DualWeylNonDom
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_XiNorm
import Theorems.Thm_Formalism_BranchingDeterminantCap_xn_R
import Theorems.Thm_P2M_Formalism_BranchingDeterminantCap_xn_R__615355f130ba
import Theorems.Thm_Formalism_BranchingDeterminantCap_xnC_ite

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
theorem _root_.solution (N : ℕ) (μ : ℕ → ℕ) (p : ℕ) (hp : p ≤ N) (h0 : ∀ j, p ≤ j → μ j = 0) :
    xnW N (xnAdd μ p) * xnC p μ p = xnW N μ * xnC N μ p := by
  rw [xnC_ite p μ p N hp, xnC_ite N μ p N hp]
  unfold xnW
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases hi : i < p
  · simp only [if_pos hi]
    exact xn_R μ p i hi h0 N hp
  · simp only [if_neg hi, mul_one]
    exact xn_R' μ p i (by omega) N
end Formalism.BranchingDeterminantCap
