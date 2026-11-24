-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.TPresMain.sl_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:08:41.851616+00:00
-- url     : https://prove2.me/submissions/e2b7a3c0-5e7c-4898-bd38-79e0ec6caae4

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinorSmoothness_HasDerivAtExt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinorSmoothness_ExpSecondHermitianMemLevel
import Theorems.Thm_Formalism_FourierDecayAlt_Q_TPresMain_sl_add
import Theorems.Thm_Formalism_FourierDecayAlt_Q_TPresMain_sl_zero

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
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.Q.TPresMain
theorem _root_.solution {ι : Type*} (s : Finset ι) (f : ι → Mx k r → E) (hf : ∀ j ∈ s, SmoothLev k r i D (f j)) :
    SmoothLev k r i D (∑ j ∈ s, f j) := by
  exact Finset.sum_induction _ (fun g => SmoothLev k r i D g) (fun _ _ ha hb => sl_add ha hb) sl_zero hf
end Formalism.FourierDecayAlt.Q.TPresMain
