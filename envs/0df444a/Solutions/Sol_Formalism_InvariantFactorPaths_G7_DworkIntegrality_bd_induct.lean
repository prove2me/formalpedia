-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.DworkIntegrality.bd_induct
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:27:51.59883+00:00
-- url     : https://prove2.me/submissions/5f09641a-6200-492d-ad14-51601baf1ffe

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_CyclicPowerClassOfExpEquiv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartB
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_LocalComponentGL
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_coeff_truncD
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
variable {K ι : Type} [NormedField K] [Finite ι]
namespace Formalism.InvariantFactorPaths.G7.DworkIntegrality
theorem _root_.solution {c : ℝ} (hc : 0 ≤ c) (X : MvPowerSeries ι K)
    (h : ∀ d, Bd c (truncD d X) → ∀ m : ι →₀ ℕ, m.degree = d → ‖MvPowerSeries.coeff m X‖ ≤ c) :
    Bd c X := by
  have key : ∀ d, ∀ m : ι →₀ ℕ, m.degree = d → ‖MvPowerSeries.coeff m X‖ ≤ c := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      refine h d ?_
      intro n
      rw [coeff_truncD]
      split_ifs with hn
      · exact ih _ hn n rfl
      · simpa using hc
  exact fun n => key _ n rfl
end Formalism.InvariantFactorPaths.G7.DworkIntegrality
