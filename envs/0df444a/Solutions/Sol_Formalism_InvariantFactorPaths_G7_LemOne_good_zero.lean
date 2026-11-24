-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.LemOne.good_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:12:51.336854+00:00
-- url     : https://prove2.me/submissions/a3ca2451-f91f-49fe-b522-bc88c547259f

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FirstDeriv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_NotDvdChoosePowMul
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_LemOne_low_up
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_LemOne_coeff_rem
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_LemOne_cob_rem_integral
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_coeff_lgF_ne_zero
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_coeff_lgF_pow


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
    (hFl : cob F (lgF K p) = 0) (hde : Integral (cob F (g0F K p)))
    {f : PowerSeries K} (hf0 : PowerSeries.constantCoeff f = 0) (hcob : Integral (cob F f)) :
    Good p f 0 0 (PowerSeries.coeff 1 f) := by
  have h0 : ‖(0 : K)‖ ≤ 1 := by rw [norm_zero]; exact zero_le_one
  refine ⟨h0, low_up hp hnp hF0 hFi hF1 (cob_rem_integral hF0 hFl hde hcob h0 _) 0 fun d hd => ?_⟩
  rw [pow_zero] at hd
  rw [coeff_rem, zero_mul, sub_zero]
  have hd' : d = 0 ∨ d = 1 := by omega
  rcases hd' with rfl | rfl
  · have hl : PowerSeries.coeff 0 (lgF K p) = 0 := by
      by_contra hc
      obtain ⟨i, hi⟩ := coeff_lgF_ne_zero hc
      exact (pow_pos (pow_pos hp.pos 2) i).ne hi
    rw [hl, mul_zero, sub_zero, PowerSeries.coeff_zero_eq_constantCoeff_apply, hf0]
    exact h0
  · have hl : PowerSeries.coeff 1 (lgF K p) = 1 := by
      have := coeff_lgF_pow K hp.two_le 0
      simpa using this
    rw [hl, mul_one, sub_self]
    exact h0
end Formalism.InvariantFactorPaths.G7.LemOne
