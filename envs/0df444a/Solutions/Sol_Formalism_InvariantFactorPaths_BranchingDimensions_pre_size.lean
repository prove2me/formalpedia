-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.BranchingDimensions.pre_size
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:12:13.106257+00:00
-- url     : https://prove2.me/submissions/9a23f714-eff2-4a9e-9d1c-e327ee2d344c

import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_StatementT
import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_N0LeNs
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_sum_filter_Icc_succ
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_HStrip_diff_le

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
theorem _root_.solution (hk : 1 ≤ D.k) (hP : D.IsPre mu) : ∀ i, i ≤ D.n0 →
    -((∑ l ∈ (Icc 1 i).filter (fun l => D.vec l = false), D.B l : ℕ) : ℤ) ≤ ent mu i (D.k - 1) ∧
    ent mu i 0 ≤ ((∑ l ∈ (Icc 1 i).filter (fun l => D.vec l = true), D.B l : ℕ) : ℤ) := by
  intro i
  induction i with
  | zero =>
    intro _
    simp [hP.1]
  | succ i ih =>
    intro hi
    obtain ⟨ih1, ih2⟩ := ih (by omega)
    rw [sum_filter_Icc_succ _ _ _ _ (by omega), sum_filter_Icc_succ _ _ _ _ (by omega)]
    have hk1 : D.k - 1 < D.k := by omega
    have hk0 : 0 < D.k := by omega
    by_cases hv : D.vec (i + 1) = true
    · have hS := hP.2.2.1 (i + 1) (by omega) hi hv
      have hW := hP.2.2.2.2.1 (i + 1) (by omega) hi hv
      simp only [Nat.add_sub_cancel] at hS hW
      have hd := HStrip.diff_le hS 0 hk0
      have h1 := hS.1 (D.k - 1) hk1
      rw [if_neg (by simp [hv]), if_pos hv]
      push_cast at ih1 ih2 ⊢
      constructor <;> linarith
    · have hv' : D.vec (i + 1) = false := by simpa using hv
      have hS := hP.2.2.2.1 (i + 1) (by omega) hi hv'
      have hW := hP.2.2.2.2.2 (i + 1) (by omega) hi hv'
      simp only [Nat.add_sub_cancel] at hS hW
      have hd := HStrip.diff_le hS (D.k - 1) hk1
      have h1 := hS.1 0 hk0
      rw [if_pos hv', if_neg hv]
      push_cast at ih1 ih2 ⊢
      constructor <;> linarith
end Formalism.InvariantFactorPaths.BranchingDimensions
