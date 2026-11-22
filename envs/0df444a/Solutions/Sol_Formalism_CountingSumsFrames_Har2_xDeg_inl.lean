-- Prove2me | solution 1 for Formalism.CountingSumsFrames.Har2.xDeg_inl
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:35:22.847799+00:00
-- url     : https://prove2.me/submissions/c6159b0e-a720-46c4-be5b-75816a522f16

import Definitions.Def_Formalism_PolynomialDimension_StatementHar
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_HarmonicDecompositionHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset MvPolynomial
open Formalism Formalism.CountingSumsFrames
open Formalism.CountingSumsFrames.Har2
variable {K : Type} [Field K] {k : ℕ}
namespace Formalism.CountingSumsFrames.Har2
theorem _root_.solution (i : Fin k) : xDeg (Finsupp.single (Sum.inl i : XY k) 1) = 1 := by
  simp [xDeg, Finsupp.single_apply]
end Formalism.CountingSumsFrames.Har2
