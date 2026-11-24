-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.LemOne.cob_rem_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T09:41:19.101849+00:00
-- url     : https://prove2.me/submissions/5c9ecc0e-4d0f-466c-8b0f-e4fc08effb13

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FirstDeriv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_NotDvdChoosePowMul
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_LemOne_norm_sub_le_max
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_LemOne_cob_comb

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
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.G7
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7.LemOne
variable {K : Type} [NormedField K] [IsUltrametricDist K]
namespace Formalism.InvariantFactorPaths.G7.LemOne
theorem _root_.solution {p : ℕ} {F : MvPowerSeries (Fin 2) K}
    (hF0 : MvPowerSeries.constantCoeff F = 0) (hFl : cob F (lgF K p) = 0)
    (hde : Integral (cob F (g0F K p))) {f : PowerSeries K} (hcob : Integral (cob F f))
    {a : K} (ha : ‖a‖ ≤ 1) (b : K) : Integral (cob F (rem p f a b)) := by
  intro n
  unfold rem
  rw [cob_comb hF0, hFl, mul_zero, sub_zero, map_sub, MvPowerSeries.coeff_C_mul]
  refine (norm_sub_le_max _ _).trans (max_le (hcob n) ?_)
  rw [norm_mul]
  exact mul_le_one₀ ha (norm_nonneg _) (hde n)
end Formalism.InvariantFactorPaths.G7.LemOne
