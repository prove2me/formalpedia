-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.EtaleIntegralityFacts.sm_DB
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:59:45.008209+00:00
-- url     : https://prove2.me/submissions/9e009e08-7189-4565-a471-fba6b049fdbd

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
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_sm_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_tri_DB

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
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {m q : ℕ} {tt : E → ℂ}
  {xx : E → Fin (m + 1) → ℂ} {yy : E → UT (m + 2) → ℂ} {u : E} {Q : ℝ}
namespace Formalism.FourierDecayAlt.P.EtaleIntegralityFacts
theorem _root_.solution (hQ0 : 0 ≤ Q) (hx : ∀ k, DB q (fun v => xx v k) u Q 1) (hy : ∀ e, DB q (fun v => yy v e) u Q 1) :
    DB q (fun v => sm m (xx v, yy v)) u (Q ^ 1) 1 := by
  simp only [sm_apply]
  exact tri_DB hQ0 hx hy _ _
end Formalism.FourierDecayAlt.P.EtaleIntegralityFacts
