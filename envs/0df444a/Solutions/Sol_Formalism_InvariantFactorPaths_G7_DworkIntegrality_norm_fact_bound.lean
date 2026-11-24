-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.DworkIntegrality.norm_fact_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:03:54.443825+00:00
-- url     : https://prove2.me/submissions/75062a02-0eaf-4193-91f8-d3d3337aef6a

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_CyclicPowerClassOfExpEquiv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartB
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_LocalComponentGL
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_norm_natCast_eq_pow_padicValNat
import Theorems.Thm_Formalism_FG_SolveVAux_low_add
import Theorems.Thm_Formalism_FG_SolveVAux_low_mono
import Theorems.Thm_Formalism_FG_SolveVAux_low_mul
import Theorems.Thm_Formalism_FG_SolveVAux_low_neg
import Theorems.Thm_Formalism_FG_SolveVAux_low_one_iff
import Theorems.Thm_Formalism_FG_SolveVAux_low_pow
import Theorems.Thm_Formalism_FG_SolveVAux_low_sub
import Theorems.Thm_Formalism_FG_SolveVAux_low_zero


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
variable {K ι : Type} [NormedField K] [CharZero K]
variable [IsUltrametricDist K] {p : ℕ}
namespace Formalism.InvariantFactorPaths.G7.DworkIntegrality
theorem _root_.solution (hp : p.Prime) (hnp : ‖(p : K)‖ = (p : ℝ)⁻¹) (k : ℕ) :
    ‖(((k + 1).factorial : ℕ) : K)⁻¹‖ * ((p : ℝ)⁻¹) ^ (k + 1) ≤ (p : ℝ)⁻¹ := by
  have := Fact.mk hp
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hlt : ‖(p : K)‖ < 1 := by rw [hnp]; exact inv_lt_one_of_one_lt₀ hp1
  have hv : padicValNat p (k + 1).factorial ≤ k := by
    have h := sub_one_mul_padicValNat_factorial_lt_of_ne_zero (p := p) (n := k + 1) (by omega)
    have h2 : 1 ≤ p - 1 := by have := hp.two_le; omega
    have h3 : 1 * padicValNat p (k + 1).factorial ≤ (p - 1) * padicValNat p (k + 1).factorial :=
      Nat.mul_le_mul_right _ h2
    omega
  rw [norm_inv, Formalism.DworkPowerSeriesWeights.norm_natCast_eq_pow_padicValNat hp hlt (Nat.factorial_ne_zero _), hnp]
  generalize padicValNat p (k + 1).factorial = v at hv
  obtain ⟨j, rfl⟩ : ∃ j, k = v + j := ⟨k - v, by omega⟩
  have hpos : (0 : ℝ) < (p : ℝ)⁻¹ := by positivity
  rw [add_assoc, pow_add, ← mul_assoc, inv_mul_cancel₀ (pow_pos hpos v).ne', one_mul, pow_succ]
  exact mul_le_of_le_one_left hpos.le (pow_le_one₀ hpos.le (inv_le_one_of_one_le₀ hp1.le))
end Formalism.InvariantFactorPaths.G7.DworkIntegrality
