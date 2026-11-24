-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.DworkIntegrality.frob_monomial
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:06:47.466234+00:00
-- url     : https://prove2.me/submissions/51a4e161-ed14-4a0d-a0c2-60a5afe78823

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_CyclicPowerClassOfExpEquiv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartB
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_LocalComponentGL
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_PhiH_apply
import Theorems.Thm_Formalism_FG_SolveVAux_low_add
import Theorems.Thm_Formalism_FG_SolveVAux_low_mono
import Theorems.Thm_Formalism_FG_SolveVAux_low_mul
import Theorems.Thm_Formalism_FG_SolveVAux_low_neg
import Theorems.Thm_Formalism_FG_SolveVAux_low_one_iff
import Theorems.Thm_Formalism_FG_SolveVAux_low_pow
import Theorems.Thm_Formalism_FG_SolveVAux_low_sub
import Theorems.Thm_Formalism_FG_SolveVAux_low_zero
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_frobVar_eq_expand


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
open Formalism.FG.SolveVAux (Low low_zero low_mono low_add low_sub low_neg low_mul low_pow low_one_iff)
open Formalism.InvariantFactorPaths.G7.DworkIntegrality
variable {K ι : Type} [NormedField K] [IsUltrametricDist K] {p : ℕ} {σ : K →+* K}
namespace Formalism.InvariantFactorPaths.G7.DworkIntegrality
theorem _root_.solution (hp : p ≠ 0) (hσ : ∀ a : K, ‖a‖ ≤ 1 → ‖σ a - a ^ p‖ ≤ (p : ℝ)⁻¹)
    (a : ι →₀ ℕ) {c : K} (hc : ‖c‖ ≤ 1) :
    Bd (p : ℝ)⁻¹ ((MvPowerSeries.monomial a c) ^ p - PhiH hp σ (MvPowerSeries.monomial a c)) := by
  classical
  have e : (MvPowerSeries.monomial a c) ^ p - PhiH hp σ (MvPowerSeries.monomial a c) =
      MvPowerSeries.monomial (p • a) (c ^ p - σ c) := by
    rw [MvPowerSeries.monomial_pow, PhiH_apply, frobVar_eq_expand hp, MvPowerSeries.map_monomial,
      MvPowerSeries.expand_monomial, map_sub]
  rw [e]
  intro n
  rw [MvPowerSeries.coeff_monomial]
  split_ifs
  · rw [norm_sub_rev]; exact hσ c hc
  · simp
end Formalism.InvariantFactorPaths.G7.DworkIntegrality
