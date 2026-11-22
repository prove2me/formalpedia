-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.glAct_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:27:02.688281+00:00
-- url     : https://prove2.me/submissions/e2b4c657-192b-4d3e-af42-e04dff7e56a7

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementB
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_MulEarlyLettersHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4
open Formalism.GM.M MvPolynomial Finset Formalism.CountingSumsFrames
variable (p : ℕ) [Fact p.Prime] {N r : ℕ}
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution (LL : Letters N) (j : ℕ) (a b : Fin r) (f g : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    glAct p LL j a b (f * g) = glAct p LL j a b f * g + f * glAct p LL j a b g := by
  simp only [glAct, LinearMap.sum_apply]
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp [Derivation.leibniz] <;> ring
end Formalism.InvariantFactorPaths.L4
