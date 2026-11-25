-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.Z.pole_transfer_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:10:40.373961+00:00
-- url     : https://prove2.me/submissions/469a740c-8876-436f-a4a8-2b310ec7109f

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_FactorOverLocalSubalgebraMonic
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZReuse
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZCircleCharExtends
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_FactorOverLocalSubalgebra
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_CharpolyFactorAnnihilator
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZGoodCuspidal
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZBrauerNesbitt
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_CardLtAddCardGtAddCardEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Filter Topology
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.Z
namespace Formalism.IrreducibleCountingLemmas.Z
theorem _root_.solution : PoleTransfer := by
  intro L Z R hR hR1 hL hZ
  have h1 : Tendsto (fun s => ‖R s‖) (nhdsWithin 1 {s : ℂ | 1 < s.re}) (𝓝 ‖R 1‖) :=
    (hR.norm).tendsto.mono_left nhdsWithin_le_nhds
  have h2 := hZ.atTop_mul_pos (norm_pos_iff.2 hR1) h1
  refine h2.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  rw [hL s hs, norm_mul]
end Formalism.IrreducibleCountingLemmas.Z
