-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.TPresMain.tl_local
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:35:44.743808+00:00
-- url     : https://prove2.me/submissions/5a04eb40-729b-49eb-a81c-6f07215ec903

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinorSmoothness_ExpSecondHermitianMemLevel
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinorSmoothness_SecondCapelliMinorContinuousLinear
import Theorems.Thm_Formalism_FourierDecayAlt_Q_TPresMain_chatL_local
import Theorems.Thm_Formalism_FourierDecayAlt_Q_TPresMain_second_capelli_minor_local
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
theorem _root_.solution (hD : IsOpen D) (z z' : Fin (2 * r + k + 1) → ℂ) (Y : ℂ) (p q : Fin 2)
    (f f' : Mx k r → E) (h : ∀ x ∈ Glev k r i ∩ D, f x = f' x) (g : Mx k r) (hg : g ∈ Glev k r i ∩ D) :
    tL k r z z' i Y p q f g = tL k r z z' i Y p q f' g := by
  fin_cases p <;> fin_cases q
  · exact qminor_local hD (fun j => j) (fun j => j) _ f f' h g hg
  · exact congrArg Neg.neg (chatL_local hD _ (fun _ => xv k r z' i) (ybv k r z i) f f' h g hg)
  · exact congrArg Neg.neg (chatL_local hD _ (yv k r z i) (fun _ => xbv k r z' i) f f' h g hg)
  · exact congrArg Neg.neg (second_capelli_minor_local hD _ (yv k r z i) (fun _ => xv k r z' i) (ybv k r z i)
      (fun _ => xbv k r z' i) f f' h g hg)
end Formalism.FourierDecayAlt.Q.TPresMain
