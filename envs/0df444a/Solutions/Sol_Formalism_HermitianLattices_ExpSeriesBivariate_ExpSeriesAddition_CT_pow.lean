-- Prove2me | solution 1 for Formalism.HermitianLattices.ExpSeriesBivariate.ExpSeriesAddition.CT.pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:05:36.441802+00:00
-- url     : https://prove2.me/submissions/63e01584-1f03-4d76-bd60-035649ad0eff

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_LegendreCoefficient
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_IntegralSubstVector
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_ExpSeries
import Theorems.Thm_Formalism_HermitianLattices_ExpSeriesBivariate_ExpSeriesAddition_Low_mul
import Theorems.Thm_Formalism_HermitianLattices_ExpSeriesBivariate_ExpSeriesAddition_CT_mul

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
variable {σ K : Type} [NormedField K]
namespace Formalism.HermitianLattices.ExpSeriesBivariate.ExpSeriesAddition
namespace CT
theorem _root_.solution {F : ℕ → MvPowerSeries σ K} {f : MvPowerSeries σ K} (hF : CT F f) (n : ℕ) :
    CT (fun k => F k ^ n) (f ^ n) := by
  induction n with
  | zero =>
    intro d
    simp only [pow_zero]
    exact tendsto_const_nhds
  | succ n ih =>
    simp only [pow_succ]
    exact ih.mul hF
end CT
end Formalism.HermitianLattices.ExpSeriesBivariate.ExpSeriesAddition
