-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.WordIntegralScaling.rw_scale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:59:15.339356+00:00
-- url     : https://prove2.me/submissions/04cf956f-395a-4faa-9241-195845a9a7a0

import Definitions.Def_Formalism_HermitianCurvature_StatementJF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WordIntegralScaling
import Theorems.Thm_Formalism_FourierDecayAlt_P_WordIntegralScaling_lr_nrm
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_W_nrm
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_dLR_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.WordIntegralScaling
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.WordIntegralScaling
theorem _root_.solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (v : List (Mat k r)) (f : Mat k r → E) :
    Rw v f = B4.pn (B4.lr [] v) • Rw (v.map fun X => ((‖X‖⁻¹ : ℝ) : ℂ) • X) f := by
  have h := B4.W_nrm (B4.lr [] v) f
  rw [lr_nrm, ← B4.dLR_eq, ← B4.dLR_eq] at h
  exact h
end Formalism.FourierDecayAlt.P.WordIntegralScaling
