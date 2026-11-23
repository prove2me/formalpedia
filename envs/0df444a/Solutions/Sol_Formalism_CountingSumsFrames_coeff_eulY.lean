-- Prove2me | solution 1 for Formalism.CountingSumsFrames.coeff_eulY
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:44:19.779163+00:00
-- url     : https://prove2.me/submissions/fd84c2df-580f-4681-ac18-5ad9ea5568be

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
    coeff m (eulY K k f) = (yDeg m : K) * coeff m f := by
  simp [eulY, coeff_sum, coeff_X_mul_pderiv, yDeg, Finset.sum_mul]
end Formalism.CountingSumsFrames
