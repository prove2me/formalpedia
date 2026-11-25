-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.eabPres_main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:10:20.861833+00:00
-- url     : https://prove2.me/submissions/e7cdd5bb-f3f4-4d78-92eb-216c45621c72

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DerivativePreservation_HasDerivAtExt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DerivativePreservation_EabPresMain
import Theorems.Thm_Formalism_FourierDecayAlt_Q_EabLie_eab_smooth
import Theorems.Thm_Formalism_FourierDecayAlt_Q_EabLie_eab_left
import Theorems.Thm_Formalism_FourierDecayAlt_Q_EabLie_eab_lin

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
namespace Formalism.FourierDecayAlt.Q
theorem _root_.solution : EabPres := by
  intro E _ _ k r z i D a b f f₂ s hD hf hf₂
  exact ⟨EabLie.eab_smooth i D a b f hf, fun _ hL => EabLie.eab_left i z D hD a b f hf hL,
    fun g hg => EabLie.eab_lin i D a b f f₂ s hf hf₂ g hg⟩
end Formalism.FourierDecayAlt.Q
