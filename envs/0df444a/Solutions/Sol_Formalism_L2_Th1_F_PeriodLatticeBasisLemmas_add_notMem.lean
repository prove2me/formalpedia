-- Prove2me | solution 1 for Formalism.L2.Th1.F.PeriodLatticeBasisLemmas.add_notMem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:24:58.127579+00:00
-- url     : https://prove2.me/submissions/35127f8a-3261-49eb-b89b-454c4cdedad7

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_Legendre
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_SigmaQuasi

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.PeriodLatticeBasisLemmas
namespace Formalism.L2.Th1.F.PeriodLatticeBasisLemmas
theorem _root_.solution {L : PeriodPair} {ω z : ℂ} (hω : ω ∈ L.lattice) (hz : z ∉ L.lattice) :
    z + ω ∉ L.lattice := by
  intro h
  apply hz
  have h2 := L.lattice.sub_mem h hω
  rwa [add_sub_cancel_right] at h2
end Formalism.L2.Th1.F.PeriodLatticeBasisLemmas
