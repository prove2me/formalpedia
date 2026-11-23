-- Prove2me | solution 1 for Formalism.EigenvalueLevelCeiling.isMirab_of_isUniU
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:14:05.359175+00:00
-- url     : https://prove2.me/submissions/2c2ca634-5388-4dae-86b4-207948e606d0

import Mathlib
import Definitions.Def_Formalism_MirabolicMackeyTheory_StatementL
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_Mirabolic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open Formalism Formalism.EigenvalueLevelCeiling
variable {k : Type} [Field k] {n : ℕ}
namespace Formalism.EigenvalueLevelCeiling
theorem _root_.solution (u : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (hu : IsUniU u) : IsMirab u := by
  intro j
  by_cases hj : j = Fin.last n
  · subst hj
    rw [if_pos rfl]
    exact hu.1 _
  · rw [if_neg hj]
    exact hu.2 _ _ (Fin.lt_last_iff_ne_last.2 hj)
end Formalism.EigenvalueLevelCeiling
