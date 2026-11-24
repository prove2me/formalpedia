-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.TPresMain.top_smooth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:18:46.560531+00:00
-- url     : https://prove2.me/submissions/c648fb67-926f-4568-bd3c-6a651cd0b813

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinorSmoothness_HasDerivAtExt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinorSmoothness_ExpSecondHermitianMemLevel
import Theorems.Thm_Formalism_FourierDecayAlt_Q_TPresMain_sl_add
import Theorems.Thm_Formalism_FourierDecayAlt_Q_TPresMain_sl_zero
import Theorems.Thm_Formalism_FourierDecayAlt_Q_TPresMain_sl_csmul
import Theorems.Thm_Formalism_FourierDecayAlt_Q_TPresMain_eh_smooth

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
theorem _root_.solution (hD : IsOpen D) (c : ℂ) (p q : Fin (mdim k r i)) (f : Mx k r → E)
    (hf : SmoothLev k r i D f) :
    SmoothLev k r i D (Top (EH k r) c (posL k r i p) (posL k r i q) f) := by
  refine sl_add (f := fun g => if posL k r i p = posL k r i q then c • f g else 0) ?_ (eh_smooth p q f hf)
  by_cases hpq : posL k r i p = posL k r i q
  · simp only [hpq, ↓reduceIte]
    exact sl_csmul c hf
  · simp only [hpq, ↓reduceIte]
    exact sl_zero
end Formalism.FourierDecayAlt.Q.TPresMain
