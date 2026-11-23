-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.EtaleIntegralityFacts.Lim.z_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:57:11.489821+00:00
-- url     : https://prove2.me/submissions/863b8131-66cb-4243-b37f-af1b1895ad41

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
theorem _root_.solution (m : ℕ) {z : ℂ} {d r R : ℝ} (h : ‖z‖ ^ (m + 2) = d) (hr : r ≤ d) (hR : d ≤ R) :
    min 1 r ≤ ‖z‖ ∧ ‖z‖ ≤ max 1 R := by
  constructor
  · by_cases h1 : 1 ≤ ‖z‖
    · exact (min_le_left _ _).trans h1
    · push Not at h1
      refine (min_le_right _ _).trans (hr.trans ?_)
      rw [← h]
      exact pow_le_of_le_one (norm_nonneg _) h1.le (by omega)
  · by_cases h1 : ‖z‖ ≤ 1
    · exact h1.trans (le_max_left _ _)
    · push Not at h1
      refine le_trans ?_ (hR.trans (le_max_right _ _))
      rw [← h]
      exact le_self_pow₀ h1.le (by omega)
end Formalism.FourierDecayAlt.P.EtaleIntegralityFacts.Lim
