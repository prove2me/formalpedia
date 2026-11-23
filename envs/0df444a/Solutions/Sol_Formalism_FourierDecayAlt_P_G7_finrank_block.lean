-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G7.finrank_block
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:45:10.423027+00:00
-- url     : https://prove2.me/submissions/2cf6d0f2-d9d0-4778-b91d-66a712eaf3b3

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionCriticalPoints
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdditiveCharacterPsi
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AffineChangeOfVariables
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralConvergesAbs
import Theorems.Thm_Formalism_FourierDecayAlt_P_G7_finrank_pi
import Theorems.Thm_Formalism_FourierDecayAlt_P_dimension_count


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.G7
open Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P.G2
namespace Formalism.FourierDecayAlt.P.G7
theorem _root_.solution (n : ℕ) : Module.finrank ℝ (BlockCoord n) = n * (n + 3) := by
  rw [Module.finrank_prod, Module.finrank_prod, finrank_pi, finrank_pi, (dimension_count n).1, Fintype.card_fin]
  cases n with
  | zero => rfl
  | succ k => simp only [Nat.add_sub_cancel]; ring
end Formalism.FourierDecayAlt.P.G7
