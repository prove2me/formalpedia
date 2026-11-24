-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.DworkIntegrality.low_exp_sub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:03:54.765436+00:00
-- url     : https://prove2.me/submissions/df948a2d-c44c-42df-bc19-b09dd409f641

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_CyclicPowerClassOfExpEquiv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartB
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_LocalComponentGL
import Theorems.Thm_Formalism_FG_SolveVAux_low_add
import Theorems.Thm_Formalism_FG_SolveVAux_low_mono
import Theorems.Thm_Formalism_FG_SolveVAux_low_mul
import Theorems.Thm_Formalism_FG_SolveVAux_low_neg
import Theorems.Thm_Formalism_FG_SolveVAux_low_one_iff
import Theorems.Thm_Formalism_FG_SolveVAux_low_pow
import Theorems.Thm_Formalism_FG_SolveVAux_low_sub
import Theorems.Thm_Formalism_FG_SolveVAux_low_zero
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_low_mvExp_sub
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_low_sum


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
namespace Formalism.InvariantFactorPaths.G7.DworkIntegrality
theorem _root_.solution {f : MvPowerSeries ι K} {d : ℕ} (hd : 1 ≤ d) (hf : Low d f) :
    Low (d + 1) (mvExp f - 1 - f) := by
  have hf0 : MvPowerSeries.constantCoeff f = 0 := (low_one_iff _).1 (low_mono hd hf)
  have h1 := low_mvExp_sub hf0 (d + 1)
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
  have h2 : expSum f (e + 1 + 1) =
      (∑ k ∈ range e, MvPowerSeries.C (((k + 1 + 1).factorial : K)⁻¹) * f ^ (k + 1 + 1)) + f + 1 := by
    unfold expSum
    rw [Finset.sum_range_succ', Finset.sum_range_succ']
    simp
  have h3 : Low (e + 1 + 1)
      (∑ k ∈ range e, MvPowerSeries.C (((k + 1 + 1).factorial : K)⁻¹) * f ^ (k + 1 + 1)) :=
    low_sum _ _ _ fun k _ => by
      have := low_mul (low_zero (MvPowerSeries.C (((k + 1 + 1).factorial : K)⁻¹)))
        (low_mul (low_mul hf hf) (low_zero (f ^ k)))
      rw [show f ^ (k + 1 + 1) = f * f * f ^ k by ring]
      exact low_mono (by omega) this
  have e' : mvExp f - 1 - f = (mvExp f - expSum f (e + 1 + 1)) +
      ∑ k ∈ range e, MvPowerSeries.C (((k + 1 + 1).factorial : K)⁻¹) * f ^ (k + 1 + 1) := by
    rw [h2]; ring
  rw [e']
  exact low_add h1 h3
end Formalism.InvariantFactorPaths.G7.DworkIntegrality
