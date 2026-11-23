-- Prove2me | solution 1 for Formalism.CountingSumsFrames.pderiv_inl_h
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:52:24.792805+00:00
-- url     : https://prove2.me/submissions/4ac6a0fd-899e-4601-999e-7b58f467bf0e

import Definitions.Def_Formalism_PolynomialDimension_StatementHar
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PairingAdjointLaplacianHolds

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
theorem _root_.solution (i : Fin k) : pderiv (Sum.inl i) (hXY K k) = X (Sum.inr i) := by
  classical
  simp [hXY, pderiv_X, Pi.single_apply, Finset.sum_ite_eq']
end Formalism.CountingSumsFrames
