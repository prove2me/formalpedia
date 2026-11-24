-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.WhittakerVanishingImpliesZero.norm_cof_rest_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:53:05.955959+00:00
-- url     : https://prove2.me/submissions/219172d6-20f5-405c-ae3d-a5e2d92f8463

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RemainderNormLeStrictUpper
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WhittakerVanishingImpliesZero
import Theorems.Thm_Formalism_FourierDecayAlt_P_G6_norm_pow_mulVec_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.WhittakerVanishingImpliesZero
open Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P.G6
namespace Formalism.FourierDecayAlt.P.WhittakerVanishingImpliesZero
theorem _root_.solution {m : ℕ} {X : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ} {B : Fin (m + 1) → ℂ}
    {t : ℂ} {L : ℝ} (hL : 1 ≤ L) (ht : ‖t‖ ≤ 1) (hX : ∀ i j, ‖X i j‖ ≤ L) (hB : ∀ i, ‖B i‖ ≤ L) :
    ‖∑ j ∈ Finset.range m, ((-X) ^ j *ᵥ B) 0 * t ^ (m - j)‖ ≤
      ((m : ℝ) * ((m : ℝ) + 1) ^ m) * (L ^ (m + 1) * ‖t‖) := by
  have hL0 : 0 ≤ L := le_trans zero_le_one hL
  have hm1 : (1 : ℝ) ≤ (m : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  calc ‖∑ j ∈ Finset.range m, ((-X) ^ j *ᵥ B) 0 * t ^ (m - j)‖
      ≤ ∑ j ∈ Finset.range m, ‖((-X) ^ j *ᵥ B) 0 * t ^ (m - j)‖ := norm_sum_le _ _
    _ ≤ ∑ _j ∈ Finset.range m, (((m : ℝ) + 1) ^ m * L ^ (m + 1)) * ‖t‖ := by
        refine Finset.sum_le_sum fun j hj => ?_
        have hj' := Finset.mem_range.mp hj
        rw [norm_mul, norm_pow]
        refine mul_le_mul ((norm_pow_mulVec_le hL0 hX hB j 0).trans ?_)
          (pow_le_of_le_one (norm_nonneg _) ht (by omega)) (by positivity) (by positivity)
        exact mul_le_mul (pow_le_pow_right₀ hm1 hj'.le) (pow_le_pow_right₀ hL (by omega))
          (by positivity) (by positivity)
    _ = _ := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        ring
end Formalism.FourierDecayAlt.P.WhittakerVanishingImpliesZero
