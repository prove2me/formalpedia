-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.StepIV_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T09:53:27.338867+00:00
-- url     : https://prove2.me/submissions/3ade3cb9-9deb-4e3e-b2fb-59ebecd27bac

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FirstDeriv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_ConstantCoeffFirstTwoOfThree
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_CoboundarySeries_map_Gser
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_CoboundarySeries_constantCoeff_Gser
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_frobVar_eq_expand
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_frobenius_expression_g


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
open CoboundarySeries
namespace Formalism.InvariantFactorPaths.G7
theorem _root_.solution (hW : DworkMv) : StepIV := by
  intro K _ _ _ p σ hU G c hG hσc hI
  obtain ⟨hpr, hp2, hnp, -, hσ⟩ := hU
  have hp : 2 ≤ p := hp2.le
  have hp0 : p ≠ 0 := by omega
  have hpK : (p : K) ≠ 0 := Nat.cast_ne_zero.2 hp0
  have hcc : MvPowerSeries.constantCoeff (G - Gser p c (σ c)) = 0 := by
    rw [map_sub, constantCoeff_Gser, sub_zero, ← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact hG 0 (Or.inl (by simp))
  refine ⟨hcc, ?_⟩
  rw [hW K (Fin 2) p σ hpr hnp hσ _ hcc]
  have hfs : ∀ f g : MvPowerSeries (Fin 2) K, frobVar p (f - g) = frobVar p f - frobVar p g := by
    intro f g
    simp only [frobVar_eq_expand hp0, map_sub]
  have hmapG : MvPowerSeries.map σ (Gser p c (σ c)) = Gser p (σ c) c := by rw [map_Gser, hσc]
  have hfr := frobenius_expression_g K p c (σ c) hp hpK
  have hDeS : frobVar p (MvPowerSeries.map σ G) - MvPowerSeries.C (p : K) * G =
      MvPowerSeries.C (p : K) * DeS p σ G := by
    unfold DeS
    rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hpK, map_one, one_mul]
  have key : frobVar p (MvPowerSeries.map σ (G - Gser p c (σ c))) -
      MvPowerSeries.C (p : K) * (G - Gser p c (σ c)) = MvPowerSeries.C (p : K) * Hser p σ G (σ c) (-c) := by
    rw [map_sub, hmapG, hfs]
    unfold Hser
    rw [map_neg]
    linear_combination hDeS - hfr
  intro n
  rw [key, MvPowerSeries.coeff_C_mul, norm_mul, hnp]
  exact mul_le_of_le_one_right (by positivity) (hI n)
end Formalism.InvariantFactorPaths.G7
