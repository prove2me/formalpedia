-- Prove2me | solution 1 for Formalism.L2.Th1.B.Sim.inLam_fLog
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:46:23.08264+00:00
-- url     : https://prove2.me/submissions/299e5cf8-f65e-4e74-8541-ebe21fd6d721

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_OneAddMulDerivLogSubst
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_ExpSeries
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_SimeqPadicIntegers
import Theorems.Thm_Formalism_HermitianLattices_ExpSeriesBivariate_ExpSeriesAddition_inLam_add
import Theorems.Thm_Formalism_HermitianLattices_ExpSeriesBivariate_ExpSeriesAddition_inLam_neg
import Theorems.Thm_Formalism_HermitianLattices_ExpSeriesBivariate_ExpSeriesAddition_inLam_nsmul
import Theorems.Thm_Formalism_HermitianLattices_ExpSeriesBivariate_ExpSeriesAddition_inLam_zero
import Theorems.Thm_Formalism_HermitianLattices_ExpSeriesBivariate_ExpSeriesAddition_integral_of_mul_eq_one
import Theorems.Thm_Formalism_L2_Th1_B_constantCoeff_fLog
import Theorems.Thm_Formalism_L2_Th1_B_fExp_fLog


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B Formalism.L2.Th1.B.Sim
open Finset
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7 (Simeq)
open Formalism.HermitianLattices.ExpSeriesBivariate (InLam)
open Formalism.HermitianLattices.ExpSeriesBivariate.ExpSeriesAddition (inLam_zero inLam_add inLam_neg inLam_nsmul integral_of_mul_eq_one)
variable {K ι : Type} [NormedField K] [CharZero K]
namespace Formalism.L2.Th1.B.Sim
theorem _root_.solution {g : MvPowerSeries ι K} (hg0 : MvPowerSeries.constantCoeff g = 1)
    (hg : Integral g) : InLam (fLog g) := by
  refine ⟨constantCoeff_fLog hg0, ?_⟩
  have e : fExp (fLog g) = g := fExp_fLog hg0
  have h : Integral (fExp (fLog g)) := by rw [e]; exact hg
  exact h
end Formalism.L2.Th1.B.Sim
