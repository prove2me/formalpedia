-- Prove2me | solution 1 for Formalism.HermitianLattices.ExpSeriesBivariate.ExpSeriesAddition.subst_expS
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:11:47.466776+00:00
-- url     : https://prove2.me/submissions/fa77b17a-32bd-4dff-85b6-d9faa19ef750

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_LegendreCoefficient
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_IntegralSubstVector
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_ExpSeries

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
theorem _root_.solution {τ : Type} [Finite σ] (h : σ → MvPowerSeries τ K)
    (hh : ∀ i, MvPowerSeries.constantCoeff (h i) = 0) (f : MvPowerSeries σ K)
    (hf : MvPowerSeries.constantCoeff f = 0) :
    MvPowerSeries.subst h (expS f) = expS (MvPowerSeries.subst h f) := by
  have hs : MvPowerSeries.HasSubst h := MvPowerSeries.hasSubst_of_constantCoeff_zero hh
  have ha : MvPowerSeries.HasSubst (fun _ : Unit => f) :=
    PowerSeries.hasSubst_iff.mp (PowerSeries.HasSubst.of_constantCoeff_zero hf)
  unfold expS
  rw [PowerSeries.subst_def, PowerSeries.subst_def, MvPowerSeries.subst_comp_subst_apply ha hs]
end Formalism.HermitianLattices.ExpSeriesBivariate.ExpSeriesAddition
