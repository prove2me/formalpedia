-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.BranchingDimensions.Branch.interl_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:34:40.562177+00:00
-- url     : https://prove2.me/submissions/2aaa6b4f-976c-40e3-b0f0-4dae1ed62c6c

import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_StatementT
import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_Branch
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_Branch_extW_val

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
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.BranchingDimensions
open Formalism.InvariantFactorPaths.BranchingDimensions.Branch
namespace Formalism.InvariantFactorPaths.BranchingDimensions.Branch
theorem _root_.solution {n : ℕ} (la : Fin n → ℤ) (mu : Fin (n + 1) → ℤ) :
    Interl n (extW la) (extW mu) ↔
      la ∈ Fintype.piFinset (fun i : Fin n => Icc (mu i.succ) (mu i.castSucc)) := by
  rw [Fintype.mem_piFinset]
  constructor
  · intro h i
    have := h i.val i.isLt
    rw [extW_val] at this
    have e1 : extW mu i.val = mu i.castSucc := extW_val mu i.castSucc
    have e2 : extW mu (i.val + 1) = mu i.succ := extW_val mu i.succ
    rw [e1, e2] at this
    exact Finset.mem_Icc.2 ⟨this.2, this.1⟩
  · intro h l hl
    have := Finset.mem_Icc.1 (h ⟨l, hl⟩)
    have e0 : extW la l = la ⟨l, hl⟩ := extW_val la ⟨l, hl⟩
    have e1 : extW mu l = mu (Fin.castSucc ⟨l, hl⟩) := extW_val mu (Fin.castSucc ⟨l, hl⟩)
    have e2 : extW mu (l + 1) = mu (Fin.succ ⟨l, hl⟩) := extW_val mu (Fin.succ ⟨l, hl⟩)
    rw [e0, e1, e2]
    exact ⟨this.2, this.1⟩
end Formalism.InvariantFactorPaths.BranchingDimensions.Branch
