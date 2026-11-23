-- Prove2me | solution 1 for Formalism.G0.DetDividesP.lastIdx_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:41:45.29587+00:00
-- url     : https://prove2.me/submissions/c3e92d7c-62a7-4e90-82d4-18bf0b2d7d4e

import Definitions.Def_Formalism_SubspaceCounting_StatementW
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_DetDivides

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
open Polynomial
open Formalism Formalism.G0 Formalism.G0.DetDividesP
open Formalism.G0
variable {L : Type} [Field L] {r : ℕ}
namespace Formalism.G0.DetDividesP
theorem _root_.solution (hr : 0 < r) (a : Fin r) : a.val + 1 = r ↔ a = ⟨r - 1, by omega⟩ := by
  constructor
  · intro h; ext; simp; omega
  · intro h; subst h; simp; omega
end Formalism.G0.DetDividesP
