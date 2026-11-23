-- Prove2me | solution 1 for Formalism.F.muMaxMono_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:22:49.743653+00:00
-- url     : https://prove2.me/submissions/f909927d-61cc-48d0-b825-9645bcc9aa10

import Definitions.Def_Formalism_LatticeSlopes_CovolAntiSameRank
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_SlopeLeMuMaxOf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.F
universe u
namespace Formalism.F
theorem _root_.solution (h : SlopesBdd.{u}) : MuMaxMono.{u} := by
  intro E _ _ _ L N hL hNL hN
  apply csSup_le_csSup (h E L hL) (show (slopes N).Nonempty from ⟨slope N, N, le_rfl, hN, rfl⟩)
  rintro t ⟨M, hMN, hM, rfl⟩
  exact ⟨M, hMN.trans hNL, hM, rfl⟩
end Formalism.F
