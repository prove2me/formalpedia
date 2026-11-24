-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts.bkb_Bd_mono
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:53:08.312817+00:00
-- url     : https://prove2.me/submissions/6102364f-b7c9-4045-b0e0-d6a792647957

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WirtingerIntegrationByParts

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts
open Formalism.FourierDecayAlt.G MeasureTheory
namespace Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts
theorem _root_.solution {E W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup W] [NormedSpace ℝ W]
    {f : E → W} {s : Set E} {x : E} {n : ℕ} {A A' P : ℝ} (hP : 0 ≤ P) (hA : A ≤ A') (b : Bd f s x n A P) :
    Bd f s x n A' P := fun j hj =>
  (b j hj).trans (mul_le_mul_of_nonneg_right hA (pow_nonneg hP j))
end Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts
