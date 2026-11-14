-- Prove2me | solution 1 for BCFGJPSSV26.Stable.Partition.min_le_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T18:07:13.355332+00:00
-- url     : https://prove2.me/submissions/ef17181f-7681-4444-9a23-52e92edf5a65

module

public import Definitions.Def_BCFGJPSSV26_Stable_LSBound_NiceMaps
public import Definitions.Def_BCFGJPSSV26_Stable_Submod_Candidate
public import Definitions.Def_BCFGJPSSV26_Stable_WinWin
public import Definitions.Def_BCFGJPSSV26_Stable_Final_Combine
import all Definitions.Def_BCFGJPSSV26_Stable_Final_Combine
public import Theorems.Thm_BCFGJPSSV26_Stable_Partition_costF_S_le_PsiLS
public import Theorems.Thm_BCFGJPSSV26_Stable_Partition_psi_combo

set_option maxSynthPendingDepth 3



@[expose] public section

namespace BCFGJPSSV26.Stable

open Finset

namespace Partition

variable {X : Ctx} {Λ₁ : List (Dummy X.I)} {w₁ : ClientWitness X Λ₁}
  {LS' : Finset (Fin X.I.m)} {Λ₂ : List (Dummy X.I)} {w₂ : ClusterWitness w₁ LS' Λ₂}
  (Q : Partition w₂)

/-- **The final bound**: the local search or a candidate within `Ψ_T + 60 ε opt` costs at most
`(1 + η + 100 ε) opt`. -/
theorem min_le_bound (H : Hyp X) {cT : ℝ} (hT : cT ≤ Q.PsiT + 60 * X.ε * X.opt) :
    X.I.costF X.S ≤ (1 + eta + 100 * X.ε) * X.opt ∨ cT ≤ (1 + eta + 100 * X.ε) * X.opt := by
  by_contra h
  rw [not_or, not_le, not_le] at h
  have h1 := Q.costF_S_le_PsiLS H
  have h2 := Q.psi_combo H
  have hopt : 0 ≤ X.opt := H.opt_pos.le
  have hε := H.eps_pos
  unfold aW at h2
  nlinarith [mul_nonneg hε.le hopt]

end Partition

end BCFGJPSSV26.Stable

end

public section

theorem solution : type_of% @BCFGJPSSV26.Stable.Partition.min_le_bound := @BCFGJPSSV26.Stable.Partition.min_le_bound
