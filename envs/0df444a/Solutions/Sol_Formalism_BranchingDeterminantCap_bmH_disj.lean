-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.bmH_disj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:29:40.192259+00:00
-- url     : https://prove2.me/submissions/89a09065-9980-4cb4-8160-4cecba5fbc45

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MemBranchRangeOfDefectEq
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchMap
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmH_anti

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
theorem _root_.solution {n : ℕ} (L : Fin (n + 1) → ℤ) (μ ν : Fin n → ℤ) (hμ : Interlace L μ) (hν : Interlace L ν)
    (i j : Fin n) (hij : i ≠ j) : (ν i - ((i : ℕ) : ℤ)) - (μ j - ((j : ℕ) : ℤ)) ≠ 0 := by
  have hA := bmH_anti L μ hμ
  rcases lt_or_gt_of_ne hij with h | h
  · have hl : i.succ ≤ j.castSucc := by
      rw [Fin.le_iff_val_le_val, Fin.val_succ, Fin.coe_castSucc]
      exact Fin.lt_iff_val_lt_val.mp h
    have e1 := hA hl
    have e2 := (hν i).2
    have e3 := (hμ j).1
    have hv : (i : ℕ) < (j : ℕ) := Fin.lt_iff_val_lt_val.mp h
    omega
  · have hl : j.succ ≤ i.castSucc := by
      rw [Fin.le_iff_val_le_val, Fin.val_succ, Fin.coe_castSucc]
      exact Fin.lt_iff_val_lt_val.mp h
    have e1 := hA hl
    have e2 := (hμ j).2
    have e3 := (hν i).1
    have hv : (j : ℕ) < (i : ℕ) := Fin.lt_iff_val_lt_val.mp h
    omega
end Formalism.BranchingDeterminantCap
