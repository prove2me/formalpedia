-- Prove2me | solution 1 for Formalism.HermitianLattices.ExpSeriesBivariate.ExpSeriesAddition.inLam_nsmul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:27:59.740909+00:00
-- url     : https://prove2.me/submissions/bbc0a77f-1043-4866-85f2-b0fbcbf594eb

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_LegendreCoefficient
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_IntegralSubstVector
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_ExpSeries
import Theorems.Thm_Formalism_HermitianLattices_ExpSeriesBivariate_ExpSeriesAddition_inLam_zero
import Theorems.Thm_Formalism_HermitianLattices_ExpSeriesBivariate_ExpSeriesAddition_inLam_add

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
theorem _root_.solution [IsUltrametricDist K] [Algebra ℚ K] {f : MvPowerSeries σ K} (hf : InLam f)
    (m : ℕ) : InLam (m • f) := by
  induction m with
  | zero => simpa using (inLam_zero : InLam (0 : MvPowerSeries σ K))
  | succ m ih =>
    rw [succ_nsmul]
    exact inLam_add ih hf
end Formalism.HermitianLattices.ExpSeriesBivariate.ExpSeriesAddition
