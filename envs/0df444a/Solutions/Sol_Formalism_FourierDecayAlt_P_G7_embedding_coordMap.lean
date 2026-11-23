-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G7.embedding_coordMap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:07:20.19064+00:00
-- url     : https://prove2.me/submissions/d009ac0d-2abf-4a7c-83f8-c66e931f0d5f

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionCriticalPoints
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdditiveCharacterPsi
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AffineChangeOfVariables
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralConvergesAbs
import Theorems.Thm_Formalism_FourierDecayAlt_P_G7_continuous_coordMap
import Theorems.Thm_Formalism_FourierDecayAlt_P_G7_injective_coordMap

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
theorem _root_.solution (n : ℕ) (t : ℂ) (ht : t ≠ 0) : MeasurableEmbedding (coordMap n t) := by
  have h1 : TopologicalSpace.SeparableSpace (BlockCoord n) := inferInstance
  have h2 : TopologicalSpace.IsCompletelyMetrizableSpace (BlockCoord n) := inferInstance
  have h3 : PolishSpace (BlockCoord n) := inferInstance
  exact (continuous_coordMap n t).measurableEmbedding (injective_coordMap n t ht)
end Formalism.FourierDecayAlt.P.G7
