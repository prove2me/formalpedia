-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LD.last_graded_at_of_exp_dual
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:36:59.539606+00:00
-- url     : https://prove2.me/submissions/a12275dc-e33d-45c7-afa5-875e89954150

import Definitions.Def_Formalism_PieriBlockIdeals_LastGradedOfGradedAlone
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LastGradedImpliesOneBlock
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightShiftEqDetMul
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LEhwLemmas
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightProdLeadingMinors
import Theorems.Thm_Formalism_CohomologicalDescent_LD_dualWtSpec
import Theorems.Thm_Formalism_CohomologicalDescent_LD_blockDual
import Theorems.Thm_Formalism_CohomologicalDescent_LD_depthDual
import Theorems.Thm_Formalism_CohomologicalDescent_LD_wtBound
import Theorems.Thm_Formalism_CohomologicalDescent_LD_exp_le_cast_iff
import Theorems.Thm_Formalism_CohomologicalDescent_LD_depth_two_of_dual_weights
import Theorems.Thm_Formalism_CohomologicalDescent_LD_block_weight_last_le_bound
import Theorems.Thm_Formalism_CohomologicalDescent_LD_weight_space_ne_bot
import Theorems.Thm_Formalism_CohomologicalDescent_LD_block_weight_last_antitone
import Theorems.Thm_Formalism_CohomologicalDescent_LD_exp_le_of_nonzero_weight_vectors
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open MvPolynomial
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LD
open Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent.LA
namespace Formalism.CohomologicalDescent.LD
theorem _root_.solution (hE : ExpDual) (hD : LemmaDGraded) (l p q w M : ℕ) (lam2 : Fin q → ℕ) (ξ : Fin (q + p) → ℤ)
    (hl : l.Prime) (ha : Antitone lam2) (hb : ∀ b, w ≤ lam2 b ∧ lam2 b ≤ M) (hwM : w ≤ M) (hξ : Antitone ξ) :
    LemmaDLastGradedAt l p q w M lam2 ξ := by
  intro i' eL heL i μ hd hd2
  have hlamA : Antitone (blockWtLast p q w lam2) := block_weight_last_antitone p q w lam2 ha (fun b => (hb b).1)
  have hlamM := block_weight_last_le_bound p q w M lam2 (fun b => (hb b).2) hwM
  refine exp_le_of_nonzero_weight_vectors l _ _ μ _ hl fun x hx hne => ?_
  have hμM : ∀ a, μ a ≤ M := wtBound _ M _ μ hlamA hlamM (weight_space_ne_bot hx hne)
  rw [hE l (q + p) M _ μ _ hl hlamA hlamM hμM, ← exp_le_cast_iff l (Nat.add_comm p q)]
  have hB := blockDual p q w M lam2
  simp only [dualWt] at hB
  rw [hB]
  have hξs : Antitone fun a : Fin (p + q) => -ξ (Fin.rev (Fin.cast (Nat.add_comm p q) a)) := by
    intro a b hab
    refine neg_le_neg (hξ (Fin.rev_le_rev.mpr ?_))
    exact hab
  refine hD l p q (M - w) (dualWt M lam2) _ hl ((dualWtSpec q M lam2).2.2 ha)
    (fun b => Nat.sub_le_sub_left (hb _).1 M) hξs i' eL ?_ i _ ((depthDual p q w M i μ hwM hμM).1 hd) ?_
  · intro μ2' hdep
    refine exp_le_of_nonzero_weight_vectors l _ _ μ2' _ hl fun y hy hyne => ?_
    have hM2 : ∀ a, μ2' a ≤ M :=
      wtBound _ M _ μ2' ((dualWtSpec q M lam2).2.2 ha) (dualWtSpec q M lam2).2.1 (weight_space_ne_bot hy hyne)
    have e2 : dualWt M (dualWt M μ2') = μ2' := (dualWtSpec q M μ2').1 hM2
    have h3 := (hE l q M lam2 (dualWt M μ2') eL hl ha (fun b => (hb b).2) (dualWtSpec q M μ2').2.1).1
    have h4 : ExpLe l q (dualWt M lam2) (dualWt M (dualWt M μ2')) eL := by
      refine h3 (heL _ ?_)
      rw [← e2, ← blockDual, ← blockDual, depth_two_of_dual_weights p q M ξ _ _ hlamM
        (block_weight_last_le_bound p q w M _ (dualWtSpec q M μ2').2.1 hwM)] at hdep
      exact hdep
    rwa [e2] at h4
  · rw [← blockDual]
    exact (depth_two_of_dual_weights p q M ξ _ μ hlamM hμM).le.trans hd2
end Formalism.CohomologicalDescent.LD
