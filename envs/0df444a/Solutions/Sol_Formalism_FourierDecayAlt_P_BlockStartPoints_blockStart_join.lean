-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.BlockStartPoints.blockStart_join
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:01:56.621181+00:00
-- url     : https://prove2.me/submissions/db0e83f1-cf32-4c71-9e63-7a0bd8cdd0a2

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementTB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockStartPoints

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.BlockStartPoints
open Finset Formalism.FourierDecayAlt.TB Formalism.FourierDecayAlt.TB.Data
open scoped ComplexOrder
open Classical
noncomputable section
variable {E W : Type} [Field E]
namespace Formalism.FourierDecayAlt.P.BlockStartPoints
theorem _root_.solution (h : Pt E) (s : ℕ) (t : E) (k : ℕ) (hk : k ≤ h.length) :
    blockStart (join h s t) k = blockStart h k := by
  simp [blockStart, join, List.take_append_of_le_length hk]
end Formalism.FourierDecayAlt.P.BlockStartPoints
