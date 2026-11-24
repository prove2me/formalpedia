-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.TPresMain.chatL_smooth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:12:52.290314+00:00
-- url     : https://prove2.me/submissions/590bec73-166b-4791-801f-7b4e2237c1fa

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinorSmoothness_ExpSecondHermitianMemLevel
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinorSmoothness_SecondCapelliMinorContinuousLinear
import Theorems.Thm_Formalism_FourierDecayAlt_Q_TPresMain_qminor_smooth
import Theorems.Thm_Formalism_FourierDecayAlt_Q_TPresMain_sg_const
import Theorems.Thm_Formalism_FourierDecayAlt_Q_TPresMain_sg_mul
import Theorems.Thm_Formalism_FourierDecayAlt_Q_TPresMain_sl_smul_fun
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_Q_TPresMain_sl_sum__cd5de3938d2f


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
theorem _root_.solution (hD : IsOpen D) (u : ℂ) (a β : Mx k r → Fin (mdim k r i) → ℂ)
    (ha : ∀ j, SmoothG k r i (fun g => a g j)) (hβ : ∀ j, SmoothG k r i (fun g => β g j))
    (f : Mx k r → E) (hf : SmoothLev k r i D f) :
    SmoothLev k r i D (chatL (EH k r) (posL k r i) u a β f) := by
  unfold chatL
  exact sl_sum' _ fun i0 => sl_sum' _ fun j0 =>
    sl_smul_fun (sg_mul (sg_mul (sg_const _) (hβ i0)) (ha j0)) (qminor_smooth hD _ _ u f hf)
end Formalism.FourierDecayAlt.Q.TPresMain
