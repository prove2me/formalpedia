-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.TPresMain.tl_clm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:01:29.554246+00:00
-- url     : https://prove2.me/submissions/6637a467-8bc9-4543-a448-9db23ade742a

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinorSmoothness_ExpSecondHermitianMemLevel
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinorSmoothness_SecondCapelliMinorContinuousLinear
import Theorems.Thm_Formalism_FourierDecayAlt_Q_TPresMain_chatL_clm
import Theorems.Thm_Formalism_FourierDecayAlt_Q_TPresMain_second_capelli_minor_continuousLinear
import Theorems.Thm_Formalism_FourierDecayAlt_Q_TPresMain_qminor_clm


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
    (L : E →L[ℂ] E') (f : Mx k r → E) (hf : SmoothLev k r i D f) (g : Mx k r) (hg : g ∈ Glev k r i ∩ D) :
    tL k r z z' i Y p q (fun y => L (f y)) g = L (tL k r z z' i Y p q f g) := by
  fin_cases p <;> fin_cases q
  · exact qminor_clm hD (fun j => j) (fun j => j) _ L f hf g hg
  · exact (congrArg Neg.neg (chatL_clm hD _ (fun _ => xv k r z' i) (ybv k r z i) L f hf g hg)).trans
      (map_neg L _).symm
  · exact (congrArg Neg.neg (chatL_clm hD _ (yv k r z i) (fun _ => xbv k r z' i) L f hf g hg)).trans
      (map_neg L _).symm
  · exact (congrArg Neg.neg (second_capelli_minor_continuousLinear hD _ (yv k r z i) (fun _ => xv k r z' i) (ybv k r z i)
      (fun _ => xbv k r z' i) L f hf g hg)).trans (map_neg L _).symm
end Formalism.FourierDecayAlt.Q.TPresMain
