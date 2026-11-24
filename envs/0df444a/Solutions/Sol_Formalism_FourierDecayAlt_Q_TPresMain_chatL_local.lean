-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.TPresMain.chatL_local
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:15:32.805866+00:00
-- url     : https://prove2.me/submissions/1ff1cffb-c640-4fc3-81ee-9fa3335f3079

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinorSmoothness_ExpSecondHermitianMemLevel
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinorSmoothness_SecondCapelliMinorContinuousLinear
import Theorems.Thm_Formalism_FourierDecayAlt_Q_TPresMain_qminor_local


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
theorem _root_.solution (hD : IsOpen D) (u : ℂ) (a β : Mx k r → Fin (mdim k r i) → ℂ) (f f' : Mx k r → E)
    (h : ∀ x ∈ Glev k r i ∩ D, f x = f' x) (g : Mx k r) (hg : g ∈ Glev k r i ∩ D) :
    chatL (EH k r) (posL k r i) u a β f g = chatL (EH k r) (posL k r i) u a β f' g := by
  simp only [chatL]
  refine Finset.sum_congr rfl fun i0 _ => Finset.sum_congr rfl fun j0 _ => ?_
  congr 1
  exact qminor_local hD _ _ u f f' h g hg
end Formalism.FourierDecayAlt.Q.TPresMain
