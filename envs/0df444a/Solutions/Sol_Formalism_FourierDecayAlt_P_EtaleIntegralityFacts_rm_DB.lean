-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.EtaleIntegralityFacts.rm_DB
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:59:03.576819+00:00
-- url     : https://prove2.me/submissions/8ecf1088-bd7d-4157-b32b-041fcd5a890a

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
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_rm_apply
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
theorem _root_.solution (hQ0 : 0 ≤ Q) (hx : ∀ k, DB q (fun v => xx v k) u Q 1) (hy : ∀ e, DB q (fun v => yy v e) u Q 1)
    (k : Fin m) : DB q (fun v => rm m (xx v, yy v) k) u (Q ^ 1) 1 := by
  simp only [rm_apply]
  exact tri_DB hQ0 hx hy _ _
end Formalism.FourierDecayAlt.P.EtaleIntegralityFacts
