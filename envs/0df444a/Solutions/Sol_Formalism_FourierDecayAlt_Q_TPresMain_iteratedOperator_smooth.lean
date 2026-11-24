-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.TPresMain.iteratedOperator_smooth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:35:07.77505+00:00
-- url     : https://prove2.me/submissions/799aee6c-902c-42e0-90f9-edb1d3a89a08

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinorSmoothness_HasDerivAtExt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinorSmoothness_ExpSecondHermitianMemLevel
import Theorems.Thm_Formalism_FourierDecayAlt_Q_TPresMain_top_smooth
import Theorems.Thm_Formalism_FourierDecayAlt_Q_TPresMain_iteratedOperator_nil
import Theorems.Thm_Formalism_FourierDecayAlt_Q_TPresMain_iteratedOperator_cons

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
variable {E E' : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E'] [NormedSpace ℂ E']
namespace Formalism.FourierDecayAlt.Q.TPresMain
theorem _root_.solution (hD : IsOpen D) (l : List (ℂ × Fin (mdim k r i) × Fin (mdim k r i)))
    (f : Mx k r → E) (hf : SmoothLev k r i D f) : SmoothLev k r i D (foldP k r i l f) := by
  induction l with
  | nil => rw [iteratedOperator_nil]; exact hf
  | cons x l ih => rw [iteratedOperator_cons]; exact top_smooth hD _ _ _ _ ih
end Formalism.FourierDecayAlt.Q.TPresMain
