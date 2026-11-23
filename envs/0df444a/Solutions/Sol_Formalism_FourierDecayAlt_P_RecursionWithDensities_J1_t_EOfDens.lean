-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.RecursionWithDensities.J1.t_EOfDens
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:42:03.731657+00:00
-- url     : https://prove2.me/submissions/34535443-089c-40b0-9dff-c575a4c5e29f

import Definitions.Def_Formalism_HermitianCurvature_StatementTC
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OneLevelInequality
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OneLevelInequalitySplitBySize
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AntidiagMulDiagonal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RecursionWithDensities

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.RecursionWithDensities Formalism.FourierDecayAlt.P.RecursionWithDensities.J1
open Finset Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TC
open scoped ComplexOrder ComplexConjugate
namespace Formalism.FourierDecayAlt.P.RecursionWithDensities.J1
theorem _root_.solution : EOfDens := by
  intro r e sd h0 h1 h2 i hi1 hi2
  rcases Nat.lt_or_ge i (r + 1) with h | h
  · have := h0 i (Finset.mem_Icc.mpr ⟨hi1, by omega⟩)
    constructor <;> linarith
  · have hi : i = r + 1 := by omega
    subst hi
    constructor <;> linarith [le_max_right sd 1, max_le h2 (one_le_two : (1 : ℝ) ≤ 2)]
end Formalism.FourierDecayAlt.P.RecursionWithDensities.J1
