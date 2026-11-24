-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.LemOne.correct
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:13:45.711812+00:00
-- url     : https://prove2.me/submissions/2cd5fb98-1b16-4d24-9202-96e43bd71ad3

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FirstDeriv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_NotDvdChoosePowMul
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_LemOne_norm_sub_le_max
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_LemOne_norm_coeff_of_pow
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_LemOne_low_up

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
    {h g h' : PowerSeries K} (hcob : Integral (cob F h)) (k j : ℕ)
    (hlow : ∀ d < p ^ (k + 1), ‖PowerSeries.coeff d h‖ ≤ 1)
    (hglow : ∀ d < p ^ (k + 1), ‖(p : K) ^ j * PowerSeries.coeff d g‖ ≤ 1)
    (hgtop : PowerSeries.coeff (p ^ (k + 1)) g = ((p : K) ^ (j + 1))⁻¹)
    (hh' : h' = h - PowerSeries.C ((p : K) * PowerSeries.coeff (p ^ (k + 1)) h * (p : K) ^ j) * g)
    (hcob' : Integral (cob F h')) :
    ‖(p : K) * PowerSeries.coeff (p ^ (k + 1)) h‖ ≤ 1 ∧
      ∀ d < p ^ (k + 2), ‖PowerSeries.coeff d h'‖ ≤ 1 := by
  have hμ := norm_coeff_of_pow hp hnp hF0 hFi hF1 hcob k hlow
  have hp0 : (p : K) ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hnp
    exact (inv_pos.2 (by exact_mod_cast hp.pos : (0 : ℝ) < p)).ne hnp
  refine ⟨hμ, low_up hp hnp hF0 hFi hF1 hcob' (k + 1) fun d hd => ?_⟩
  rw [hh', map_sub, PowerSeries.coeff_C_mul]
  rcases lt_or_eq_of_le hd with hlt | rfl
  · refine (norm_sub_le_max _ _).trans (max_le (hlow d hlt) ?_)
    rw [mul_assoc, norm_mul]
    exact mul_le_one₀ hμ (norm_nonneg _) (hglow d hlt)
  · rw [hgtop]
    have : PowerSeries.coeff (p ^ (k + 1)) h -
        (p : K) * PowerSeries.coeff (p ^ (k + 1)) h * (p : K) ^ j * ((p : K) ^ (j + 1))⁻¹ = 0 := by
      field_simp
      ring
    rw [this, norm_zero]
    exact zero_le_one
end Formalism.InvariantFactorPaths.G7.LemOne
