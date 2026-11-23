-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.OrbitTailEstimates.norm_blockIntegrand
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:28:30.403192+00:00
-- url     : https://prove2.me/submissions/dfef0f8f-4c6d-4f37-b2ec-ed1ffb2f158a

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionCriticalPoints
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdditiveCharacterPsi
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AffineChangeOfVariables
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralConvergesAbs
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitTailEstimates
import Theorems.Thm_Formalism_FourierDecayAlt_P_additive_character_psi


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.OrbitTailEstimates
open Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P.G2 Formalism.FourierDecayAlt.P.G7
namespace Formalism.FourierDecayAlt.P.OrbitTailEstimates
theorem _root_.solution {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (β : ℂ) (n : ℕ)
    (Φ : Mat (n + 1) → V) (t c : ℂ) (p : BlockCoord n) :
    ‖blockIntegrand β n Φ t c p‖ = ‖Φ (orbM n t c p)‖ := by
  unfold blockIntegrand orbM
  rw [norm_smul, norm_mul, (additive_character_psi β _ 0).2.1, (additive_character_psi β _ 0).2.1, one_mul, one_mul]
end Formalism.FourierDecayAlt.P.OrbitTailEstimates
