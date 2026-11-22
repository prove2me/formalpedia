-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.ldiag_ext_fin
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:10:26.690514+00:00
-- url     : https://prove2.me/submissions/7c2d12aa-6589-4f86-b076-30e9ffd89b8d

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_DomPow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.GradedWeylDivisibility
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution {α : Type*} [Zero α] {r : ℕ} (f : Fin r → α) (a : Fin r) : ldiagExt f a = f a := by
  rw [ldiagExt, dif_pos a.isLt]
end Formalism.GradedWeylDivisibility
