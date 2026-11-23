-- Prove2me | solution 1 for DensInertW.card_root_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:52:27.29873+00:00
-- url     : https://prove2.me/submissions/f3d95e5f-6e5e-420f-9f74-2ebb998d8fad

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_ExistsTraceNeZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Polynomial
open DensInertW
variable {K L : Type} [Field K] [Fintype K] [Field L] [Fintype L] [Algebra K L]
omit [Fintype K] [Algebra K L]
namespace DensInertW
theorem _root_.solution [DecidableEq L] (n : ℕ) (a : L) : #{x : L | x ^ (n + 1) = a} ≤ n + 1 := by
  calc #{x : L | x ^ (n + 1) = a} ≤ (nthRoots (n + 1) a).toFinset.card := by
        apply card_le_card
        intro x hx
        simp only [mem_filter, mem_univ, true_and] at hx
        rw [Multiset.mem_toFinset, mem_nthRoots (Nat.succ_pos n)]
        exact hx
    _ ≤ Multiset.card (nthRoots (n + 1) a) := Multiset.toFinset_card_le _
    _ ≤ n + 1 := card_nthRoots _ _
end DensInertW
