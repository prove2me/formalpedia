-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.CoefficientSupportCongruences.partial_coboundary_g_series_equiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:20:27.565315+00:00
-- url     : https://prove2.me/submissions/11913fce-75c6-48e3-b4ef-8b423a7af6f9

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_ThmSUniform
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FinalS
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_FrobeniusPartialCoboundaryBound
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_CoefficientSupportCongruences_suppOK_Gser
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_CoefficientSupportCongruences_constant_coeff_partial_coboundary
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_CoefficientSupportCongruences_partial_coboundary_de_s_g_series
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_CoefficientSupportCongruences_derivIs_Gser
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_CoefficientSupportCongruences_frobenius_partial_coboundary_bound
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_PhiH_apply
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_bd_C
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_bd_add
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_bd_mul
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_bd_neg
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_bd_sub
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_frob_congr
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_int_mul
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_int_pow
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_Top_dworkMv


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
open DworkIntegrality (Bd bd_add bd_sub bd_neg bd_mul bd_C int_mul int_pow frob_congr PhiH PhiH_apply)
open Formalism.InvariantFactorPaths.G7.CoefficientSupportCongruences
open FrobeniusSubstitution
namespace Formalism.InvariantFactorPaths.G7.CoefficientSupportCongruences
theorem _root_.solution {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K] {p : ℕ}
    {σ : K →+* K} (hU : UnrOK K p σ) {F : MvPowerSeries (Fin 2) K} (hF : IsLawOfLog p F)
    {c : K} (hc : ‖c‖ ≤ 1) (hσσ : σ (σ c) = c) : Simeq (d1 F (Gser p c (σ c))) 0 := by
  have hp2 : 2 ≤ p := le_of_lt hU.2.1
  have hpK : (p : K) ≠ 0 := by exact_mod_cast (show p ≠ 0 by omega)
  have hσc : ‖σ c‖ ≤ 1 := by
    have h1 : ‖σ c - c ^ p‖ ≤ (p : ℝ)⁻¹ := hU.2.2.2.2 c hc
    have h2 : ‖c ^ p‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hc
    have h3 : (p : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast (by omega : 1 ≤ p))
    calc ‖σ c‖ = ‖(σ c - c ^ p) + c ^ p‖ := by rw [sub_add_cancel]
      _ ≤ max ‖σ c - c ^ p‖ ‖c ^ p‖ := IsUltrametricDist.norm_add_le_max _ _
      _ ≤ 1 := max_le (h1.trans h3) h2
  have hG0 : MvPowerSeries.constantCoeff (Gser p c (σ c)) = 0 := by
    by_contra h
    have h' : MvPowerSeries.coeff 0 (Gser p c (σ c)) ≠ 0 := by
      rwa [MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
    obtain ⟨h1, -, -⟩ := suppOK_Gser hp2 c (σ c) 0 h'
    simp at h1
  have hd0 : MvPowerSeries.constantCoeff (d1 F (Gser p c (σ c))) = 0 := constant_coeff_partial_coboundary hF.1 hG0
  refine ⟨by rw [sub_zero]; exact hd0, ?_⟩
  rw [sub_zero]
  have hDer := derivIs_Gser (K := K) hU.1 hU.2.2.1 hc hσc
  have hΔ := partial_coboundary_de_s_g_series hp2 hpK σ hσσ hF.1 hF.2.2
  have hB := frobenius_partial_coboundary_bound hU hF hc hDer hΔ
  exact (Formalism.InvariantFactorPaths.G7.Top.dworkMv K (Fin 3) p σ hU.1 hU.2.2.1 hU.2.2.2.2 _ hd0).mpr hB
end Formalism.InvariantFactorPaths.G7.CoefficientSupportCongruences
