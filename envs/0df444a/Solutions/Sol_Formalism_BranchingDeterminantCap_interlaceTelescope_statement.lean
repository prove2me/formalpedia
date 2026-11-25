-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.interlaceTelescope_statement
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:16:44.23523+00:00
-- url     : https://prove2.me/submissions/f878db98-a39e-4a96-9e33-1588b4a013a2

import Definitions.Def_Formalism_BranchSandwichDivisors_StatementR
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MemBranchRangeOfDefectEq
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_Interlace

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open Formalism Formalism.BranchingDeterminantCap
namespace Formalism.BranchingDeterminantCap
theorem _root_.solution : InterlaceTelescope := by
  intro n lam sg h p q hpq
  have hpq' := Fin.le_iff_val_le_val.mp hpq
  obtain ⟨k, hk⟩ : ∃ k, q.val = p.val + k := ⟨q.val - p.val, by omega⟩
  induction k generalizing q with
  | zero =>
    have : q = p := Fin.ext (by omega)
    subst this
    simp
  | succ k ih =>
    have hlt : p.val + k < n := by omega
    have hq1 : p ≤ (⟨p.val + k, hlt⟩ : Fin n) := Fin.le_iff_val_le_val.mpr (by simp)
    have ih' := ih ⟨p.val + k, hlt⟩ hq1 (by simp) rfl
    have hIcc : Finset.Icc p q = insert q (Finset.Icc p ⟨p.val + k, hlt⟩) := by
      ext x
      simp only [Finset.mem_Icc, Finset.mem_insert, Fin.le_iff_val_le_val, Fin.ext_iff]
      omega
    rw [hIcc, Finset.sum_insert (by simp only [Finset.mem_Icc, Fin.le_iff_val_le_val]; omega)]
    have hq := (h q).1
    have hcs : q.castSucc = (⟨p.val + k, hlt⟩ : Fin n).succ := Fin.ext (by simp; omega)
    rw [hcs] at hq
    linarith
end Formalism.BranchingDeterminantCap
