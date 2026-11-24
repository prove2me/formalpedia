-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.TPresMain.mulX_cd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:57:53.45134+00:00
-- url     : https://prove2.me/submissions/f8f339bf-4aff-4b9a-8a5c-767a10702eda

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinorSmoothness_HasDerivAtExt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinorSmoothness_ExpSecondHermitianMemLevel

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.TPresMain
open Formalism.REAL Formalism.QuantumDeterminants Formalism.QuantumDeterminants.GBasic Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.TPresLie
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {i : Fin (r + 1)} {D : Set (Mx k r)}
variable {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E'] [NormedSpace ℂ E']
namespace Formalism.FourierDecayAlt.Q.TPresMain
theorem _root_.solution (X : Mx k r) : ContDiff ℝ ∞ (fun g : Mx k r => g * X) := by
  refine contDiff_pi.2 fun a => contDiff_pi.2 fun b => ?_
  simp only [Matrix.mul_apply]
  exact ContDiff.sum fun j _ => ((contDiff_apply ℝ ℂ j).comp (contDiff_apply ℝ (Fin (2 * r + k + 1) → ℂ) a)).mul
    contDiff_const
end Formalism.FourierDecayAlt.Q.TPresMain
