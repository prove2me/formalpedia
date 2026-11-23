-- Prove2me | solution 1 for Formalism.HermitianLattices.ExpSeriesBivariate.ExpSeriesAddition.CT.mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:09:56.6958+00:00
-- url     : https://prove2.me/submissions/3fb0cb84-99b9-491b-8489-09ebdd9c5d08

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_LegendreCoefficient
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_IntegralSubstVector
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_ExpSeries
import Theorems.Thm_Formalism_HermitianLattices_ExpSeriesBivariate_ExpSeriesAddition_Low_mul

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
theorem _root_.solution {F G : ℕ → MvPowerSeries σ K} {f g : MvPowerSeries σ K} (hF : CT F f)
    (hG : CT G g) : CT (fun k => F k * G k) (f * g) := by
  classical
  intro n
  simp only [MvPowerSeries.coeff_mul]
  apply tendsto_finset_sum
  intro p _
  exact (hF p.1).mul (hG p.2)
end CT
end Formalism.HermitianLattices.ExpSeriesBivariate.ExpSeriesAddition
