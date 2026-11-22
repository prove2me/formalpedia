-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qc_card_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:37:42.491489+00:00
-- url     : https://prove2.me/submissions/4ce52621-a8f1-4143-a143-c52d951061da

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QcEvGLDetUZpow
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QcEvGLGenPtInt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
variable {n : ℕ} [NeZero n] {M : GLMod n} {mu : Fin n → ℤ} {β : M.ι → GLCoord ℤ n}
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution (hS : SBasis) (hmu : Dominant mu) (hβ : IsSMu M mu β) : Fintype.card M.ι = dMu mu := by
  classical
  have : Fintype {I : TIdx mu // StdT I} := Fintype.ofFinite _
  have h1 := finrank_span_eq_card hβ.1
  have h2 := finrank_span_eq_card (hS n mu hmu).1
  rw [hβ.2.1] at h1
  rw [(hS n mu hmu).2] at h2
  rw [dMu, Nat.card_eq_fintype_card, ← h1, ← h2]
end Formalism.InvariantFactorPaths.ColumnFamilies
