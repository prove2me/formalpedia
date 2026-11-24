-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.TPresMain.tl_smooth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:45:16.345054+00:00
-- url     : https://prove2.me/submissions/f934aea8-e6be-44d7-b893-dad052558852

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinorSmoothness_ExpSecondHermitianMemLevel
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinorSmoothness_SecondCapelliMinorContinuousLinear
import Theorems.Thm_Formalism_FourierDecayAlt_Q_TPresMain_ybv_sg
import Theorems.Thm_Formalism_FourierDecayAlt_Q_TPresMain_yv_sg
import Theorems.Thm_Formalism_FourierDecayAlt_Q_TPresMain_chatL_smooth
import Theorems.Thm_Formalism_FourierDecayAlt_Q_TPresMain_second_capelli_minor_smooth
import Theorems.Thm_Formalism_FourierDecayAlt_Q_TPresMain_qminor_smooth
import Theorems.Thm_Formalism_FourierDecayAlt_Q_TPresMain_sg_const
import Theorems.Thm_Formalism_FourierDecayAlt_Q_TPresMain_sl_neg


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
    (f : Mx k r → E) (hf : SmoothLev k r i D f) : SmoothLev k r i D (tL k r z z' i Y p q f) := by
  fin_cases p <;> fin_cases q
  · exact qminor_smooth hD (fun j => j) (fun j => j) _ f hf
  · exact sl_neg (chatL_smooth hD _ (fun _ => xv k r z' i) (ybv k r z i) (fun _ => sg_const _)
      (fun j => ybv_sg z j) f hf)
  · exact sl_neg (chatL_smooth hD _ (yv k r z i) (fun _ => xbv k r z' i) (fun j => yv_sg z j)
      (fun _ => sg_const _) f hf)
  · exact sl_neg (second_capelli_minor_smooth hD _ (yv k r z i) (fun _ => xv k r z' i) (ybv k r z i) (fun _ => xbv k r z' i)
      (fun j => yv_sg z j) (fun _ => sg_const _) (fun j => ybv_sg z j) (fun _ => sg_const _) f hf)
end Formalism.FourierDecayAlt.Q.TPresMain
