-- Prove2me | solution 1 for Formalism.CountingSumsFrames.coeff_eulX
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:44:19.021352+00:00
-- url     : https://prove2.me/submissions/ca0893e8-d019-413f-8e99-b8625f91e8a3

import Definitions.Def_Formalism_PolynomialDimension_StatementHar
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PairingAdjointLaplacianHolds
import Theorems.Thm_Formalism_CountingSumsFrames_coeff_X_mul_pderiv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
open scoped BigOperators
open Finset MvPolynomial
open Formalism Formalism.CountingSumsFrames
variable (K : Type) [Field K] (k : ℕ)
variable {K k}
namespace Formalism.CountingSumsFrames
theorem _root_.solution (f : PolXY K k) (m : XY k →₀ ℕ) :
    coeff m (eulX_har K k f) = (xDeg m : K) * coeff m f := by
  simp [eulX_har, coeff_sum, coeff_X_mul_pderiv, xDeg, Finset.sum_mul]
end Formalism.CountingSumsFrames
