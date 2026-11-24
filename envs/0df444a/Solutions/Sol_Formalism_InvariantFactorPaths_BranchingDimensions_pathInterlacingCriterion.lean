-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.BranchingDimensions.pathInterlacingCriterion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T09:50:25.703437+00:00
-- url     : https://prove2.me/submissions/33d31331-6d22-4552-bf39-789392edd86f

import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_StatementT
import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_N0LeNs
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_Interl_size
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_n0_le_Ns
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_Ns_eq
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_r_lt_k
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_pre_of_path
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_be_eq
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_pre_size
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_interl_of_path
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_tails_range
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_path_of_interl
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_wsize_head

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
theorem _root_.solution : PathInterlacingCriterion := by
  intro D mu hW
  have hNs := Ns_eq hW
  have hrk := r_lt_k hW
  have hk1 : 1 ≤ D.k := by omega
  have hr1 : 1 ≤ D.r := hW.1
  refine ⟨fun hPre hH => ⟨fun hP i' h1 h2 => ?_, fun h => ?_⟩, fun hP => ?_⟩
  · have hIj := interl_of_path hW hP (i' - 1) (by omega)
    rw [show i' - 1 + 1 = i' by omega, show D.n0 + (i' - 1) = D.n0 + i' - 1 by omega] at hIj
    exact hIj
  · refine path_of_interl hW hPre hH (fun j hj => ?_)
    have hIj := h (j + 1) (by omega) (by omega)
    rw [show D.n0 + (j + 1) - 1 = D.n0 + j by omega] at hIj
    exact hIj
  · have hpre : -(D.beNeg : ℤ) ≤ ent mu D.n0 (D.k - 1) ∧ ent mu D.n0 0 ≤ (D.bePos : ℤ) :=
      pre_size hk1 (pre_of_path hP) D.n0 le_rfl
    have hD0 : Dom D.k (ent mu D.n0) := hP.2.1 D.n0 (n0_le_Ns D)
    have hTR := tails_range hD0 (fun j hj => interl_of_path hW hP j hj)
    have hbe : (D.be : ℤ) = D.bePos + D.beNeg := by exact_mod_cast be_eq D
    refine ⟨hpre.1, hpre.2, hTR, fun i' h1 h2 => ?_⟩
    have hH' : ∀ m, m < i' → ent mu (D.n0 + i') m = D.be := hP.2.2.2.2.2.2 i' h1 h2
    have hHm : ∀ m, m < i' - 1 → ent mu (D.n0 + (i' - 1)) m = D.be :=
      fun m hm => hP.2.2.2.2.2.2 (i' - 1) (by omega) (by omega) m hm
    have e1 := wsize_head i' (by omega) hH'
    have e2 := wsize_head (i' - 1) (by omega) hHm
    have hIj := interl_of_path hW hP (i' - 1) (by omega)
    rw [show i' - 1 + 1 = i' by omega] at hIj
    have hsz := hIj.size
    rw [show D.k - i' + 1 = D.k - (i' - 1) by omega] at hsz
    have hT0 := hTR (i' - 1) (by omega) 0 (by omega)
    have hT1 := hTR (i' - 1) (by omega) (D.k - i') (by omega)
    rw [show D.n0 + i' - 1 = D.n0 + (i' - 1) by omega, e1, e2]
    have hc : ((i' - 1 : ℕ) : ℤ) = (i' : ℤ) - 1 := by omega
    rw [hc]
    refine ⟨by ring, ?_, ?_⟩ <;> linarith [hsz.1, hsz.2, hT0.2, hT1.1, hpre.1, hpre.2]
end Formalism.InvariantFactorPaths.BranchingDimensions
