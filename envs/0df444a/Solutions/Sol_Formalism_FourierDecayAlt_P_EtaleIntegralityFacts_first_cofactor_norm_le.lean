-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.EtaleIntegralityFacts.first_cofactor_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:13:02.835613+00:00
-- url     : https://prove2.me/submissions/fa2835a4-209f-41f7-82b4-c6aa97938d62

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
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_Xm_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_Bm_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_G6_norm_pow_mulVec_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.EtaleIntegralityFacts
open Formalism.FourierDecayAlt.G Matrix
noncomputable section
namespace Formalism.FourierDecayAlt.P.EtaleIntegralityFacts
theorem _root_.solution (m : ℕ) (t : ℂ) (p : XY m) {R : ℝ} (hR : 1 ≤ R) (ht : ‖t‖ ≤ 1) (hx : ∀ k, ‖p.1 k‖ ≤ R)
    (hy : ‖p.2‖ ≤ R) : ‖cof1XY m t p‖ ≤ ((m : ℝ) + 1) ^ (m + 1) * R ^ m := by
  have hR0 : 0 ≤ R := zero_le_one.trans hR
  have hm1 : (1 : ℝ) ≤ (m : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have term : ∀ j ∈ Finset.range m, ‖((-Xm m p) ^ j *ᵥ Bm m p) 0 * t ^ (m - 1 - j)‖ ≤
      ((m : ℝ) + 1) ^ m * R ^ m := by
    intro j hj
    have hj' := Finset.mem_range.mp hj
    rw [norm_mul, norm_pow]
    calc ‖((-Xm m p) ^ j *ᵥ Bm m p) 0‖ * ‖t‖ ^ (m - 1 - j)
        ≤ (((m : ℝ) + 1) ^ j * R ^ (j + 1)) * 1 :=
          mul_le_mul (G6.norm_pow_mulVec_le hR0 (Xm_le m p hR0 hx hy) (Bm_le m p hR0 hx hy) j 0)
            (pow_le_one₀ (norm_nonneg _) ht) (by positivity) (by positivity)
      _ ≤ ((m : ℝ) + 1) ^ m * R ^ m := by
          rw [mul_one]
          exact mul_le_mul (pow_le_pow_right₀ hm1 hj'.le) (pow_le_pow_right₀ hR (by omega)) (by positivity)
            (by positivity)
  calc ‖cof1XY m t p‖ ≤ ∑ j ∈ Finset.range m, ‖((-Xm m p) ^ j *ᵥ Bm m p) 0 * t ^ (m - 1 - j)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _j ∈ Finset.range m, ((m : ℝ) + 1) ^ m * R ^ m := Finset.sum_le_sum term
    _ = (m : ℝ) * (((m : ℝ) + 1) ^ m * R ^ m) := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ ((m : ℝ) + 1) * (((m : ℝ) + 1) ^ m * R ^ m) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = _ := by ring
end Formalism.FourierDecayAlt.P.EtaleIntegralityFacts
