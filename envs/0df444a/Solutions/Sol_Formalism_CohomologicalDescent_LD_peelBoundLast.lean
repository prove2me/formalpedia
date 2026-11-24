-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LD.peelBoundLast
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:46:02.739183+00:00
-- url     : https://prove2.me/submissions/43b7c075-a354-46ff-bd2f-8649848ac75f

import Definitions.Def_Formalism_PieriBlockIdeals_BranchingBoundLastGradedOneRow
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DividedPowerZeroZeroVector
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LastGradedImpliesOneBlock
import Theorems.Thm_Formalism_CohomologicalDescent_LD_exp_le_of_nonzero_weight_vectors
import Theorems.Thm_Formalism_CohomologicalDescent_LD_depth_exists_last_block
import Theorems.Thm_Formalism_CohomologicalDescent_LD_dnVal
import Theorems.Thm_Formalism_CohomologicalDescent_LD_expLeMono


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LD
open Formalism.GradedWeylDivisibility
namespace Formalism.CohomologicalDescent.LD
theorem _root_.solution : PeelBoundLast := by
  intro hD l q w M lam2 ξ hl ha hb hξ i' eL heL μ hμ
  have hl1 : 0 < l - 1 := by have := hl.two_le; omega
  refine exp_le_of_nonzero_weight_vectors l _ _ μ _ hl fun x hx hne => ?_
  obtain ⟨i, hd, _⟩ := depth_exists_last_block 1 q w lam2 ha (fun b => (hb b).1) μ x hx hne
  have h1 := hD l q w M lam2 ξ hl ha hb hξ i' eL heL i μ hd hμ
  refine expLeMono l _ _ μ _ _ ?_ h1
  refine Nat.add_le_add_left ?_ eL
  refine (Nat.le_div_iff_mul_le hl1).mpr ?_
  have h2 := dnVal l 1 (M - w) i q 0 (fun b : Fin q => M - lam2 (Fin.rev b)) hl fun b => by
    have := hb (Fin.rev b)
    exact ⟨Nat.zero_le _, by omega⟩
  rw [one_mul] at h2
  rw [mul_comm]
  refine le_trans h2 ?_
  rcases Nat.eq_zero_or_pos q with hq | hq
  · omega
  · have := hb ⟨0, hq⟩
    omega
end Formalism.CohomologicalDescent.LD
