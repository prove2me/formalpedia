-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.EtaleIntegralityFacts.Lim.min_le_max
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:56:30.240579+00:00
-- url     : https://prove2.me/submissions/c03b615c-dc4d-4970-9a8c-d73ab8e364fe

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

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.EtaleIntegralityFacts Formalism.FourierDecayAlt.P.EtaleIntegralityFacts.Lim
open Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.EtaleIntegralityFacts Matrix Filter Topology MeasureTheory
noncomputable section
namespace Formalism.FourierDecayAlt.P.EtaleIntegralityFacts.Lim
theorem _root_.solution {A : ℝ} (hA : 0 ≤ A) {a b : ℝ} (hab : b ≤ a) :
    min 1 (a ^ (-A)) ≤ (max 1 b) ^ (-A) := by
  by_cases h : b ≤ 1
  · rw [max_eq_left h, Real.one_rpow]
    exact min_le_left _ _
  · push Not at h
    rw [max_eq_right h.le]
    refine (min_le_right _ _).trans ?_
    exact Real.rpow_le_rpow_of_nonpos (by linarith) hab (by linarith)
end Formalism.FourierDecayAlt.P.EtaleIntegralityFacts.Lim
