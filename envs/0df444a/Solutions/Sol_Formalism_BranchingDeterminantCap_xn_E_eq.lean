-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.xn_E_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:35:26.664506+00:00
-- url     : https://prove2.me/submissions/27ce3b3d-2a90-4847-9f68-2a4a6f80c996

import Mathlib
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ProdFactorialSupportSubSingle
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LFocksLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LFockbLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LBidetMinor
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LBidetLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_DualWeylNonDom
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_XiNorm
import Theorems.Thm_Formalism_BranchingDeterminantCap_xn_E_X

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
theorem _root_.solution (t s : Fin n) (f : MvPolynomial (Fin r × Fin n) ℂ) :
    ∑ b : Fin r, X (b, t) * pderiv (b, s) f = ndE ℂ r n t s f := by
  induction f using MvPolynomial.induction_on
  next a =>
    simp [MvPolynomial.derivation_C]
  next p q hp hq =>
    simp only [map_add, mul_add, Finset.sum_add_distrib, hp, hq]
  next p v hp =>
    have e := xn_E_X t s v
    simp only [Derivation.leibniz, smul_eq_mul, mul_add, Finset.sum_add_distrib, ← hp]
    simp only [ndE, MvPolynomial.mkDerivation_X]
    rw [← e, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun b _ => by ring
end Formalism.BranchingDeterminantCap
