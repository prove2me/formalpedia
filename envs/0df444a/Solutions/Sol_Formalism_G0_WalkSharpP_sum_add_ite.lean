-- Prove2me | solution 1 for Formalism.G0.WalkSharpP.sum_add_ite
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:13:47.666112+00:00
-- url     : https://prove2.me/submissions/8f4cf424-aea7-4ad3-9e53-97fbb2f23ecf

import Definitions.Def_Formalism_SubspaceCounting_Statement
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_WalkSharp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.G0
open Formalism.G0.WalkSharpP
namespace Formalism.G0.WalkSharpP
theorem _root_.solution {V : ℕ} (f : Fin V → ℕ) (t : Fin V) (K : ℕ) :
    ∑ u, (f u + if u = t then K else 0) = (∑ u, f u) + K := by

  simp [Finset.sum_add_distrib]
end Formalism.G0.WalkSharpP
