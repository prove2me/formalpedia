-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.EtaleIntegralityFacts.DB.subQ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:56:29.627144+00:00
-- url     : https://prove2.me/submissions/51d62818-b7e5-45de-9283-86382ef76792

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionCriticalPoints
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdditiveCharacterPsi
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AffineChangeOfVariables
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RemainderNormLeStrictUpper
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralConvergesAbs
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StandardCharacterExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FourierUniquenessMirabolic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeakApproximationGL
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WhittakerVanishingImpliesZero
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CuspidalIrreducibleSubrep
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionDerivatives
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EtaleIntegralityFacts
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_DB_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_DB_sub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.EtaleIntegralityFacts
open Formalism.FourierDecayAlt.G Matrix Filter Topology
noncomputable section
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
namespace Formalism.FourierDecayAlt.P.EtaleIntegralityFacts
namespace DB
theorem _root_.solution {q : ℕ} {f g : E → F} {u : E} {Q P : ℝ} {a : ℕ} (hf : DB q f u (Q ^ a) P)
    (hg : DB q g u (Q ^ a) P) (hP : 0 ≤ P) (h2 : (2 : ℝ) ≤ Q) :
    DB q (fun v => f v - g v) u (Q ^ (a + 1)) P := by
  have hQ0 : 0 ≤ Q := le_trans (by positivity) h2
  refine (hf.sub hg).mono ?_ hP le_rfl
  calc Q ^ a + Q ^ a = 2 * Q ^ a := by ring
    _ ≤ Q * Q ^ a := by gcongr
    _ = Q ^ (a + 1) := by ring
end DB
end Formalism.FourierDecayAlt.P.EtaleIntegralityFacts
