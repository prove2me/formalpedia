-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.BranchingDimensions.path_rows
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:59:13.100804+00:00
-- url     : https://prove2.me/submissions/25846b96-8431-4568-a40f-f50ffc1b0bc9

import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_StatementT
import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_N0LeNs
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_card_filter_Icc_succ

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
open Letters
variable {D : Letters} {mu : D.Stages}
namespace Formalism.InvariantFactorPaths.BranchingDimensions
theorem _root_.solution (hP : D.IsPATH mu) : ∀ i, i ≤ D.Ns →
    (∀ m, D.nVec i ≤ m → m < D.k → ent mu i m ≤ 0) ∧ ∀ m, m + D.nCov i < D.k → 0 ≤ ent mu i m := by
  intro i
  induction i with
  | zero =>
    intro _
    refine ⟨fun m _ _ => ?_, fun m _ => ?_⟩ <;> simp [hP.1]
  | succ i ih =>
    intro hi
    obtain ⟨ih1, ih2⟩ := ih (by omega)
    simp only [Letters.nVec, Letters.nCov] at ih1 ih2 ⊢
    rw [card_filter_Icc_succ _ _ _ (by omega), card_filter_Icc_succ _ _ _ (by omega)]
    by_cases hv : D.vec (i + 1) = true
    · have hS := hP.2.2.1 (i + 1) (by omega) hi hv
      simp only [Nat.add_sub_cancel] at hS
      rw [if_pos hv, if_neg (by simp [hv])]
      refine ⟨fun m hm hmk => ?_, fun m hm => ?_⟩
      · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
        exact (hS.2 m' hmk).trans (ih1 m' (by omega) (by omega))
      · exact (ih2 m (by omega)).trans (hS.1 m (by omega))
    · have hv' : D.vec (i + 1) = false := by simpa using hv
      have hS := hP.2.2.2.1 (i + 1) (by omega) hi hv'
      simp only [Nat.add_sub_cancel] at hS
      rw [if_neg hv, if_pos hv']
      refine ⟨fun m hm hmk => ?_, fun m hm => ?_⟩
      · exact (hS.1 m hmk).trans (ih1 m (by omega) hmk)
      · exact (ih2 (m + 1) (by omega)).trans (hS.2 m (by omega))
end Formalism.InvariantFactorPaths.BranchingDimensions
