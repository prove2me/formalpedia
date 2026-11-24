-- Prove2me | solution 1 for Formalism.L2.Th1.D.TraceNormBounds.norm_le_inv_of_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:47:12.431977+00:00
-- url     : https://prove2.me/submissions/bb86620c-5d93-4f3b-b7f2-718ec253bd15

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_BiextensionHypothesesOfLevelOne
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_StatementC
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FinalS
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_NormLeInvOfLtOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.D
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq DivAB d1 swap2 in3 cob UnrOK IsLawOfLog frobVar)
open Formalism.L2.Th1.D.TraceNormBounds
variable {K : Type} [NormedField K] [IsUltrametricDist K]
namespace Formalism.L2.Th1.D.TraceNormBounds
theorem _root_.solution {l : ℕ} (hl : 1 < l)
    (hval : ∀ a : K, a ≠ 0 → ∃ k : ℤ, ‖a‖ = (l : ℝ) ^ k) {y : K} (hy : ‖y‖ < 1) :
    ‖y‖ ≤ (l : ℝ)⁻¹ := by
  rcases eq_or_ne y 0 with rfl | hy0
  · simp
  obtain ⟨k, hk⟩ := hval y hy0
  rw [hk] at hy ⊢
  have hl' : (1 : ℝ) < l := by exact_mod_cast hl
  have hk' : k < 0 := by
    by_contra hc
    push_neg at hc
    have h1 : (1 : ℝ) ≤ (l : ℝ) ^ k := by
      first
      | exact one_le_zpow₀ hl'.le hc
      | exact one_le_zpow_of_nonneg₀ hl'.le hc
    linarith
  have h2 : (l : ℝ) ^ k ≤ (l : ℝ) ^ (-1 : ℤ) := by
    first
    | exact zpow_le_zpow_right₀ hl'.le (by omega)
    | exact zpow_le_of_le hl'.le (by omega)
  simpa using h2
end Formalism.L2.Th1.D.TraceNormBounds
