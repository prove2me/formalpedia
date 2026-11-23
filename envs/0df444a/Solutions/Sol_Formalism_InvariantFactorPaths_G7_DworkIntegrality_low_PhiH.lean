-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.DworkIntegrality.low_PhiH
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:31:04.553523+00:00
-- url     : https://prove2.me/submissions/4fba9ff1-406f-40f7-a6d4-d77547a118cc

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
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_coeff_frobVar_ne_zero


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
variable {K ι : Type} [Field K]
namespace Formalism.InvariantFactorPaths.G7.DworkIntegrality
theorem _root_.solution {p : ℕ} (hp : p ≠ 0) (σ : K →+* K) {d : ℕ} {h : MvPowerSeries ι K}
    (hh : Low d h) : Low (p * d) (PhiH hp σ h) := by
  intro n hn
  by_contra hne
  rw [PhiH_apply] at hne
  obtain ⟨m, rfl, hm⟩ := coeff_frobVar_ne_zero hp hne
  apply hm
  have hdeg : (p • m).degree = p * m.degree := by
    rw [map_nsmul, smul_eq_mul]
  rw [hdeg] at hn
  rw [MvPowerSeries.coeff_map, hh m (lt_of_mul_lt_mul_left hn (Nat.zero_le _)), map_zero]
end Formalism.InvariantFactorPaths.G7.DworkIntegrality
