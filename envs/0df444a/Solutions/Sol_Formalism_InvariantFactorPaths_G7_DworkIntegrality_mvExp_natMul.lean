-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.DworkIntegrality.mvExp_natMul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:03:54.614816+00:00
-- url     : https://prove2.me/submissions/033772bd-bd8e-4ebc-aff0-caea84ca7f8f

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
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_mvExp_add


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
theorem _root_.solution {Ψ : MvPowerSeries ι K} (h0 : MvPowerSeries.constantCoeff Ψ = 0) (n : ℕ) :
    mvExp (MvPowerSeries.C ((n + 1 : ℕ) : K) * Ψ) = (mvExp Ψ) ^ (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e : MvPowerSeries.C ((n + 1 + 1 : ℕ) : K) * Ψ =
        MvPowerSeries.C ((n + 1 : ℕ) : K) * Ψ + Ψ := by
      rw [Nat.cast_succ (n + 1), map_add, map_one]; ring
    rw [e, mvExp_add (by simp [h0]) h0, ih, pow_succ (mvExp Ψ) (n + 1)]
end Formalism.InvariantFactorPaths.G7.DworkIntegrality
