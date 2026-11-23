-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.bm_aeval_monomial_WH
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:28:56.570525+00:00
-- url     : https://prove2.me/submissions/46ae162f-079a-47df-942c-e666928af7d1

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MemBranchRangeOfDefectEq
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchMap
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_pow
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_prod


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Formalism.GradedWeylDivisibility
noncomputable section
open Formalism Formalism.BranchingDeterminantCap
namespace Formalism.BranchingDeterminantCap
theorem _root_.solution {R σ B : Type*} [CommRing R] [AddCommMonoid B] (w : σ → B)
    (h : σ → MvPolynomial σ R) (hh : ∀ v, IsWeightedHomogeneous w (h v) (w v)) (m : σ →₀ ℕ) :
    IsWeightedHomogeneous w (aeval h (monomial m (1 : R))) (Finsupp.weight w m) := by
  rw [aeval_monomial, map_one, one_mul, Finsupp.prod, Finsupp.weight_apply, Finsupp.sum]
  exact IsWeightedHomogeneous.prod _ _ _ fun i _ => (hh i).pow (m i)
end Formalism.BranchingDeterminantCap
