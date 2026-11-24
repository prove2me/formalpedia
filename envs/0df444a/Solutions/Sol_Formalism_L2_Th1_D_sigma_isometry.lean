-- Prove2me | solution 1 for Formalism.L2.Th1.D.sigma_isometry
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:51:51.293381+00:00
-- url     : https://prove2.me/submissions/bad594a2-829a-4d43-99ac-14d54d246ed8

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
open TraceNormBounds
namespace Formalism.L2.Th1.D
theorem _root_.solution : SigmaIsom := by
  unfold SigmaIsom
  intro K _ _ _ l σ hU a
  obtain ⟨hp, h2, hnp, hval, hfr⟩ := hU
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  have hl : (1 : ℝ) < l := by exact_mod_cast (by omega : 1 < l)
  have hl0 : (l : K) ≠ 0 := by exact_mod_cast hp.ne_zero
  have unit : ∀ u : K, ‖u‖ = 1 → ‖σ u‖ = 1 := by
    intro u hu
    have h1 := hfr u hu.le
    have h3 : ‖u ^ l‖ = 1 := by rw [norm_pow, hu, one_pow]
    have h4 : ‖σ u - u ^ l‖ < ‖u ^ l‖ := by
      rw [h3]
      exact lt_of_le_of_lt h1 (inv_lt_one_of_one_lt₀ hl)
    have e : σ u = (σ u - u ^ l) + u ^ l := by ring
    rw [e, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h4.ne, h3]
    exact max_eq_right (h4.trans_eq h3).le
  obtain ⟨k, hk⟩ := hval a ha
  have hnu : ‖a * (l : K) ^ k‖ = 1 := by
    rw [norm_mul, norm_zpow, hnp, hk, inv_zpow, mul_inv_cancel₀ (zpow_ne_zero k (by positivity))]
  have ha' : a = (a * (l : K) ^ k) * (l : K) ^ (-k) := by
    rw [mul_assoc, ← zpow_add₀ hl0, add_neg_cancel, zpow_zero, mul_one]
  rw [ha', map_mul, map_zpow₀, map_natCast, norm_mul, norm_mul, unit _ hnu, hnu]
end Formalism.L2.Th1.D
