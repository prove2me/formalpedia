-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.TPresMain.iteratedOperator_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:37:42.920997+00:00
-- url     : https://prove2.me/submissions/142e8e91-3f7d-44fb-845f-570518bb478b

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinorSmoothness_HasDerivAtExt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinorSmoothness_ExpSecondHermitianMemLevel
import Theorems.Thm_Formalism_FourierDecayAlt_Q_TPresMain_top_local
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
    (f f' : Mx k r → E) (h : ∀ x ∈ Glev k r i ∩ D, f x = f' x) :
    ∀ g ∈ Glev k r i ∩ D, foldP k r i l f g = foldP k r i l f' g := by
  induction l with
  | nil => intro g hg; rw [iteratedOperator_nil, iteratedOperator_nil]; exact h g hg
  | cons x l ih =>
    intro g hg
    rw [iteratedOperator_cons, iteratedOperator_cons]
    exact top_local hD x.1 x.2.1 x.2.2 _ _ ih g hg
end Formalism.FourierDecayAlt.Q.TPresMain
