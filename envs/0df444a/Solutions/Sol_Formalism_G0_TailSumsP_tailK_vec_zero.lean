-- Prove2me | solution 1 for Formalism.G0.TailSumsP.tailK_vec_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:13:45.367798+00:00
-- url     : https://prove2.me/submissions/f32c5747-eff4-4f6a-a67c-7c314de69cda

import Definitions.Def_Formalism_SubspaceCounting_StatementC
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_TailSums
import Theorems.Thm_Formalism_G0_TailSumsP_tailK_zero

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
theorem _root_.solution {K : ℕ} {α α' : Fin K → ℕ} {B : ℕ} (h : VecStep α α' B) :
    tailK α' 0 ≤ tailK α 0 + B := by
  rw [tailK_zero, tailK_zero]; exact h.2.2
end Formalism.G0.TailSumsP
