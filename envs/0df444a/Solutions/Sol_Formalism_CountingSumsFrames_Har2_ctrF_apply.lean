-- Prove2me | solution 1 for Formalism.CountingSumsFrames.Har2.ctrF_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:15:58.267629+00:00
-- url     : https://prove2.me/submissions/0a2befb1-9f35-420c-bb87-76b6b4453d74

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
theorem _root_.solution (f : PolXY K k) :
    ctrF K k f = ∑ i : Fin k, pderiv (Sum.inl i) (pderiv (Sum.inr i) f) := by
  unfold ctrF
  rw [LinearMap.sum_apply]
  rfl
end Formalism.CountingSumsFrames.Har2
