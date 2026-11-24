-- Prove2me | solution 1 for Formalism.G0.TailConcavityP.tele
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:11:11.770214+00:00
-- url     : https://prove2.me/submissions/ecb8a766-bf99-4239-af3b-c3fd7d0d8d4c

import Definitions.Def_Formalism_SubspaceCounting_StatementB
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_TailConcavity

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
open Finset
open Formalism Formalism.G0
open Formalism.G0.TailConcavityP
namespace Formalism.G0.TailConcavityP
theorem _root_.solution (k N : ℕ) (B : Fin N → ℕ) (l : ℕ) :
    ∑ u ∈ range (l + 1), en k N B u = cn k N B l := by
  induction l with
  | zero => simp [en]
  | succ l ih =>
    rw [sum_range_succ, ih]
    simp [en]
end Formalism.G0.TailConcavityP
