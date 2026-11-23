-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.EtaleIntegralityFacts.Lim.Tpow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:56:50.913935+00:00
-- url     : https://prove2.me/submissions/e79041fd-04b6-4d61-bc70-9785f53abc3a

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
import Theorems.Thm_Formalism_FourierDecayAlt_P_G6_rpow_bound


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
theorem _root_.solution (m : ℕ) {τ ε : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hε0 : 0 < ε) (hε : ε ≤ 1 / (2 * ((m : ℝ) + 2))) {i : ℕ}
    (hi : i ≤ m + 2) : (τ ^ (-ε)) ^ i * τ ≤ Real.sqrt τ := by
  have hT : 1 ≤ τ ^ (-ε) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hτ hτ1 (by linarith)
  refine le_trans ?_ (G6.rpow_bound m hτ hτ1 hε)
  exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hT hi) hτ.le
end Formalism.FourierDecayAlt.P.EtaleIntegralityFacts.Lim
