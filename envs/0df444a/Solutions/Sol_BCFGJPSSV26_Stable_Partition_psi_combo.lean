-- Prove2me | solution 1 for BCFGJPSSV26.Stable.Partition.psi_combo
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T17:58:36.97368+00:00
-- url     : https://prove2.me/submissions/adffeb96-2d63-44c0-9380-cbd35cbf2cf3

module

public import Definitions.Def_BCFGJPSSV26_Stable_LSBound_NiceMaps
public import Definitions.Def_BCFGJPSSV26_Stable_Submod_Candidate
public import Definitions.Def_BCFGJPSSV26_Stable_WinWin
public import Definitions.Def_BCFGJPSSV26_Stable_Final_Combine
import all Definitions.Def_BCFGJPSSV26_Stable_Final_Combine

set_option maxSynthPendingDepth 3



@[expose] public section

namespace BCFGJPSSV26.Stable

open Finset

namespace Partition

variable {X : Ctx} {Λ₁ : List (Dummy X.I)} {w₁ : ClientWitness X Λ₁}
  {LS' : Finset (Fin X.I.m)} {Λ₂ : List (Dummy X.I)} {w₂ : ClusterWitness w₁ LS' Λ₂}
  (Q : Partition w₂)

/-- **The win-win combination** of the two row sums. -/
theorem psi_combo (H : Hyp X) :
    aW * Q.PsiLS + (1 - aW) * Q.PsiT ≤ (1 + eta + 10 * X.ε) * X.opt := by
  rw [H.opt_eq_sum, Partition.PsiLS, Partition.PsiT, mul_sum, mul_sum, mul_sum,
    ← sum_add_distrib]
  exact sum_le_sum fun c hc ↦ Q.row_combo H hc

end Partition

end BCFGJPSSV26.Stable

end

public section

theorem solution : type_of% @BCFGJPSSV26.Stable.Partition.psi_combo := @BCFGJPSSV26.Stable.Partition.psi_combo
