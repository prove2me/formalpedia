-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.LemOne.norm_coeff_of_not_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:02:16.340827+00:00
-- url     : https://prove2.me/submissions/d94f5293-a2ca-4a2a-b4e1-b689698ca1c5

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FirstDeriv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_NotDvdChoosePowMul
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_LemOne_exists_not_dvd_choose
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_LemOne_norm_coeff_mul_choose
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_LemOne_norm_p_lt_one
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_norm_natCast_eq_one_of_not_dvd
import Theorems.Thm_GlobalTheory_NatCastUnitNorm_norm_natCast_eq_one_of_not_dvd


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
theorem _root_.solution {p : ℕ} (hp : p.Prime) (hnp : ‖(p : K)‖ = (p : ℝ)⁻¹)
    {F : MvPowerSeries (Fin 2) K}
    (hF0 : MvPowerSeries.constantCoeff F = 0) (hFi : Integral F)
    (hF1 : ∀ n : Fin 2 →₀ ℕ, n.degree = 1 → MvPowerSeries.coeff n F = 1)
    {h : PowerSeries K} (hcob : Integral (cob F h)) {n : ℕ} (hn : 2 ≤ n)
    (hpow : ∀ k, n ≠ p ^ k) (hlow : ∀ d < n, ‖PowerSeries.coeff d h‖ ≤ 1) :
    ‖PowerSeries.coeff n h‖ ≤ 1 := by
  obtain ⟨i, hi0, hin, hnd⟩ := exists_not_dvd_choose hp hn hpow
  have := norm_coeff_mul_choose hF0 hFi hF1 hcob hlow hi0 hin
  rwa [norm_mul, Formalism.DworkPowerSeriesWeights.norm_natCast_eq_one_of_not_dvd hp (norm_p_lt_one hp hnp) hnd,
    mul_one] at this
end Formalism.InvariantFactorPaths.G7.LemOne
