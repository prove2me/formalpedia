-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.EtaleIntegralityFacts.Lim.cof_lower
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:36:41.719328+00:00
-- url     : https://prove2.me/submissions/b08f649a-9c79-43ac-a85e-c2eadc2f3ccb

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
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_cofXY_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_first_cofactor_norm_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_cofXY_at_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_cofXY_zero

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
theorem _root_.solution (m : ℕ) (z τ' : ℂ) (y : UT (m + 2) → ℂ) {R c : ℝ} (hR : 1 ≤ R) (hτ : ‖τ'‖ ≤ 1) (hz : ‖z‖ ≤ R)
    (hy : ‖y‖ ≤ R) (hc : c ≤ ‖z‖ ^ (m + 1)) (hs : ‖τ'‖ * (((m : ℝ) + 1) ^ (m + 1) * R ^ m) ≤ c / 2) :
    c / 2 ≤ ‖cofXY m τ' (fun _ => z, y)‖ := by
  have h1 := first_cofactor_norm_le m τ' (fun _ => z, y) hR hτ (fun _ => hz) hy
  have h0 : ‖cof0XY m (fun _ => z, y)‖ = ‖z‖ ^ (m + 1) := by
    rw [← cofXY_at_zero, cofXY_zero]
  have h2 : ‖τ' * cof1XY m τ' (fun _ => z, y)‖ ≤ c / 2 := by
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left h1 (norm_nonneg _)).trans hs
  rw [cofXY_eq]
  have h3 := norm_sub_le_norm_add (cof0XY m (fun _ => z, y)) (τ' * cof1XY m τ' (fun _ => z, y))
  linarith [h3]
end Formalism.FourierDecayAlt.P.EtaleIntegralityFacts.Lim
