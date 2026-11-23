-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.bmF_fil_mul_low
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:22:45.782798+00:00
-- url     : https://prove2.me/submissions/bf5054b4-306c-4bbe-a39f-815867663bf8

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MemBranchRangeOfDefectEq
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchMap
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmD_omg_add

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Formalism.GradedWeylDivisibility
noncomputable section
open Formalism Formalism.BranchingDeterminantCap
namespace Formalism.BranchingDeterminantCap
theorem _root_.solution {R : Type*} [CommRing R] {n : ℕ} {D D' : ℤ} {F L : BP R n} (hF : bmF_Fil D F)
    (hL : IsLow D' L) : IsLow (D + D') (F * L) := by
  intro m hm
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp (support_mul F L hm)
  rw [map_add, bmD_omg_add]
  exact add_lt_add_of_le_of_lt (hF a ha) (hL b hb)
end Formalism.BranchingDeterminantCap
