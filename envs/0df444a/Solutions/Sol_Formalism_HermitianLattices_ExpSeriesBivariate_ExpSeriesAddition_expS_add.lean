-- Prove2me | solution 1 for Formalism.HermitianLattices.ExpSeriesBivariate.ExpSeriesAddition.expS_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:17:26.634798+00:00
-- url     : https://prove2.me/submissions/940de145-dbd2-4d6e-adda-fd94bae93b08

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_LegendreCoefficient
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_IntegralSubstVector
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_ExpSeries
import Theorems.Thm_Formalism_HermitianLattices_ExpSeriesBivariate_ExpSeriesAddition_exp_biv
import Theorems.Thm_Formalism_HermitianLattices_ExpSeriesBivariate_ExpSeriesAddition_subst_expS

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.ExpSeriesBivariate Formalism.HermitianLattices.ExpSeriesBivariate.ExpSeriesAddition
open Finset Formalism.G Formalism.HermitianLattices.ExpSeriesBivariate
variable {σ K : Type} [Field K] [Algebra ℚ K]
namespace Formalism.HermitianLattices.ExpSeriesBivariate.ExpSeriesAddition
theorem _root_.solution (f g : MvPowerSeries σ K) (hf : MvPowerSeries.constantCoeff f = 0)
    (hg : MvPowerSeries.constantCoeff g = 0) : expS (f + g) = expS f * expS g := by
  classical
  let h : Fin 2 → MvPowerSeries σ K := ![f, g]
  have hh : ∀ i, MvPowerSeries.constantCoeff (h i) = 0 := by
    intro i
    fin_cases i
    · exact hf
    · exact hg
  have hS : MvPowerSeries.HasSubst h := by
    first
    | exact MvPowerSeries.hasSubst_of_constantCoeff_zero hh
    | exact MvPowerSeries.HasSubst.of_constantCoeff_zero' hh
    | exact ⟨fun s => by rw [hh s]; exact IsNilpotent.zero,
        by rw [Filter.cofinite_eq_bot]; exact Filter.tendsto_bot⟩
  have e2 : ∀ i, MvPowerSeries.subst h (MvPowerSeries.X i : MvPowerSeries (Fin 2) K) = h i :=
    fun i => MvPowerSeries.subst_X hS i
  have e1 : MvPowerSeries.subst h (MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) =
      f + g := by
    rw [MvPowerSeries.subst_add hS, e2, e2]
    rfl
  have h0 : ∀ i : Fin 2, MvPowerSeries.constantCoeff (MvPowerSeries.X i : MvPowerSeries (Fin 2) K) = 0 :=
    fun i => MvPowerSeries.constantCoeff_X i
  rw [← e1, ← subst_expS h hh _ (by rw [map_add, h0, h0, add_zero]), exp_biv,
    MvPowerSeries.subst_mul hS, subst_expS h hh _ (h0 0), subst_expS h hh _ (h0 1), e2, e2]
  rfl
end Formalism.HermitianLattices.ExpSeriesBivariate.ExpSeriesAddition
