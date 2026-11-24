-- Prove2me | solution 1 for Formalism.G0.TailSumsP.tailK_zero_fun
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:11:34.526167+00:00
-- url     : https://prove2.me/submissions/3894a02d-14ae-4914-abf6-10f56cddf7a0

import Definitions.Def_Formalism_SubspaceCounting_StatementC
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_TailSums

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.G0
open Formalism.G0.TailSumsP
namespace Formalism.G0.TailSumsP
theorem _root_.solution {K : ℕ} (u : ℕ) : tailK (0 : Fin K → ℕ) u = 0 := by
  simp [tailK]
end Formalism.G0.TailSumsP
