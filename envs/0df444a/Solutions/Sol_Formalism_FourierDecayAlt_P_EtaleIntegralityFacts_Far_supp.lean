-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.EtaleIntegralityFacts.Far.supp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:03:11.845575+00:00
-- url     : https://prove2.me/submissions/89909721-9876-474a-b390-f2734badbeaf

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
import Theorems.Thm_Formalism_FourierDecayAlt_P_matrix_cutoff_spec


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.EtaleIntegralityFacts Formalism.FourierDecayAlt.P.EtaleIntegralityFacts.Far
open Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.EtaleIntegralityFacts Matrix Filter Topology
noncomputable section
namespace Formalism.FourierDecayAlt.P.EtaleIntegralityFacts.Far
theorem _root_.solution {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (β : ℂ) (m : ℕ) (ε : ℝ)
    (Φ : Mat (m + 1 + 1) → V) (D t : ℂ) (p : XY m) (ht : t ≠ 0) (h : ampIn β m ε Φ D t p ≠ 0) :
    cofXY m t p ≠ 0 ∧ ‖MXY m D t p‖ < 2 * ‖t‖ ^ (-ε) := by
  have hτ : 0 < ‖t‖ ^ (-ε) := Real.rpow_pos_of_pos (norm_pos_iff.2 ht) _
  constructor
  · intro hc
    apply h
    simp [ampIn, amp, hc]
  · by_contra hM
    apply h
    have := ((matrix_cutoff_spec (m + 1 + 1)).1 (‖t‖ ^ (-ε)) (MXY m D t p) hτ).2.2.2 (not_lt.1 hM)
    simp [ampIn, amp, cutPhi, this]
end Formalism.FourierDecayAlt.P.EtaleIntegralityFacts.Far
