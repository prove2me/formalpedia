-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G7.continuous_blk
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:44:10.727182+00:00
-- url     : https://prove2.me/submissions/d5723fb1-c5c6-4c58-8f97-ea1b0152626a

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionCriticalPoints
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdditiveCharacterPsi
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AffineChangeOfVariables
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralConvergesAbs

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
theorem _root_.solution {α : Type} [TopologicalSpace α] {n : ℕ} {A : α → Matrix (Fin n) (Fin n) ℂ}
    {b a : α → Fin n → ℂ} {e : α → ℂ} (hA : Continuous A) (hb : Continuous b) (ha : Continuous a)
    (he : Continuous e) : Continuous fun p => blk (A p) (b p) (a p) (e p) := by
  unfold blk
  refine Continuous.matrix_reindex (Continuous.matrix_fromBlocks hA ?_ ?_ ?_) _ _
  · exact continuous_matrix fun i _ => (continuous_apply i).comp hb
  · exact continuous_matrix fun _ j => (continuous_apply j).comp ha
  · exact continuous_matrix fun _ _ => he
end Formalism.FourierDecayAlt.P.G7
