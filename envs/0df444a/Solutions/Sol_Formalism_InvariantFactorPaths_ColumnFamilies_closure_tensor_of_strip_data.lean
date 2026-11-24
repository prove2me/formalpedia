-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.closure_tensor_of_strip_data
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:39:15.355263+00:00
-- url     : https://prove2.me/submissions/f3d91b47-c9e4-40ff-a423-00bc98be0284

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_StatementC
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_StripDataTensorColumnFamilies

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
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution (h : StripDataTensorColumnFamilies) (h1 : SymStrip) (h2 : SymDStrip) (h3 : LamStrip) : ClosureTensorPowers := by
  intro n _ M M' b hM
  refine ⟨fun e he => ?_, fun e he => ?_, fun e he => ?_⟩
  · obtain ⟨be, ps, hd⟩ := h1 n b
    exact h n _ _ be _ ps hd M M' e he hM
  · obtain ⟨be, ps, hd⟩ := h2 n b
    exact h n _ _ be _ ps hd M M' e he hM
  · obtain ⟨be, ps, hd⟩ := h3 n b
    exact h n _ _ be _ ps hd M M' e he hM
end Formalism.InvariantFactorPaths.ColumnFamilies
