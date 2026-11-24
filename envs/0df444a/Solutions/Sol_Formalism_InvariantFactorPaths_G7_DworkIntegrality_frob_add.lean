-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.DworkIntegrality.frob_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:06:47.460715+00:00
-- url     : https://prove2.me/submissions/0febfdee-ab03-4b35-be4d-f3dbd9df4447

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_CyclicPowerClassOfExpEquiv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartB
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_LocalComponentGL
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_bd_add
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_bd_C
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_bd_sum
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_bd_natCast
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_int_mul
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_int_pow
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_sm_mul
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
variable {K ι : Type} [NormedField K] [IsUltrametricDist K] {p : ℕ} {σ : K →+* K}
namespace Formalism.InvariantFactorPaths.G7.DworkIntegrality
theorem _root_.solution (hp : p.Prime) (hnp : ‖(p : K)‖ = (p : ℝ)⁻¹) {x y : MvPowerSeries ι K}
    (hx : Bd 1 x) (hy : Bd 1 y) (hx' : Bd (p : ℝ)⁻¹ (x ^ p - PhiH hp.ne_zero σ x))
    (hy' : Bd (p : ℝ)⁻¹ (y ^ p - PhiH hp.ne_zero σ y)) :
    Bd (p : ℝ)⁻¹ ((x + y) ^ p - PhiH hp.ne_zero σ (x + y)) := by
  have hpos : (0 : ℝ) ≤ (p : ℝ)⁻¹ := by positivity
  have e : (x + y) ^ p - PhiH hp.ne_zero σ (x + y) =
      (x ^ p - PhiH hp.ne_zero σ x) + (y ^ p - PhiH hp.ne_zero σ y) +
        MvPowerSeries.C (p : K) * (x * y *
          ∑ k ∈ Ioo 0 p, x ^ (k - 1) * y ^ (p - k - 1) * ((p.choose k / p : ℕ) : MvPowerSeries ι K)) := by
    rw [add_pow_prime_eq hp, map_add, map_natCast]
    ring
  rw [e]
  refine bd_add (bd_add hx' hy') (sm_mul hpos (bd_C hpos hnp.le) (int_mul (int_mul hx hy) ?_))
  exact bd_sum zero_le_one _ _ fun k _ =>
    int_mul (int_mul (int_pow hx _) (int_pow hy _)) (bd_natCast _)
end Formalism.InvariantFactorPaths.G7.DworkIntegrality
