-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.fact_choose_succ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:08:19.273617+00:00
-- url     : https://prove2.me/submissions/15b3c223-31d4-443f-92cf-5f5983325071

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementG
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_RaisingKeepsEarlyLetters
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_DerivativeDividedIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.MeanGammaLemmas Formalism.CountingSumsFrames MvPolynomial Finset
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution (c : ℤ) (k : ℕ) :
    ((k + 1).factorial : ℤ) * Ring.choose c (k + 1) = c * ((k.factorial : ℤ) * Ring.choose (c - 1) k) := by
  have e1 := Ring.descPochhammer_eq_factorial_smul_choose c (k + 1)
  have e2 := Ring.descPochhammer_eq_factorial_smul_choose (c - 1) k
  rw [← Polynomial.eval_eq_smeval, nsmul_eq_mul] at e1 e2
  rw [← e1, ← e2, descPochhammer_succ_left, Polynomial.eval_mul, Polynomial.eval_comp, Polynomial.eval_X,
    Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_one]
end Formalism.InvariantFactorPaths.L4
