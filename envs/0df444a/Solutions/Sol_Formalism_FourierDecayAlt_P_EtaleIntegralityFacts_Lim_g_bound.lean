-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.EtaleIntegralityFacts.Lim.g_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:36:41.850077+00:00
-- url     : https://prove2.me/submissions/b42d72d5-c609-4d4a-8c1f-0f5f36933c6b

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
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_cofXY_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_Lim_norm_psi

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
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
namespace Formalism.FourierDecayAlt.P.EtaleIntegralityFacts.Lim
theorem _root_.solution (m : ℕ) (β : ℂ) (Φ : Mat (m + 1 + 1) → V) (D z : ℂ) (y : UT (m + 2) → ℂ) {c K' : ℝ} (hc : 0 < c)
    (hcz : c ≤ ‖z‖ ^ (m + 1)) (hΦ : ‖Φ (MXY m D 0 (fun _ => z, y))‖ ≤ K') :
    ‖ampE β m Φ D 0 (fun _ => z, y)‖ ≤ (2 / c) ^ 2 * K' := by
  rw [ampE, norm_smul, norm_mul, norm_psi, one_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity), cofXY_zero]
  have e1 : ((‖z‖ ^ (m + 1)) ^ 2)⁻¹ ≤ (2 / c) ^ 2 := by
    rw [← inv_pow]
    refine pow_le_pow_left₀ (by positivity) ?_ 2
    rw [inv_le_comm₀ (by linarith) (by positivity), inv_div]
    linarith
  exact mul_le_mul e1 hΦ (norm_nonneg _) (by positivity)
end Formalism.FourierDecayAlt.P.EtaleIntegralityFacts.Lim
