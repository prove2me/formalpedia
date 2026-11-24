-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LD.cofactor_weighted_homog
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:29:08.95559+00:00
-- url     : https://prove2.me/submissions/3545b125-5f22-4fea-8c05-3910398166d9

import Definitions.Def_Formalism_PieriBlockIdeals_LastGradedOfGradedAlone
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LastGradedImpliesOneBlock
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightShiftEqDetMul
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LEhwLemmas
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightProdLeadingMinors
import Theorems.Thm_Formalism_CohomologicalDescent_LD_adjugate_entry_weighted_homog
import Theorems.Thm_Formalism_CohomologicalDescent_LD_aeval_weighted_homog
import Theorems.Thm_Formalism_CohomologicalDescent_LD_weight_omega_add_degree
import Theorems.Thm_Formalism_GradedWeylDivisibility_ldrow_weight_rowW
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
theorem _root_.solution {r : ℕ} (μ : Fin r → ℕ) (x : MvPolynomial (Fin r × Fin r) ℤ)
    (hx : IsWeightedHomogeneous (rowW r r) x μ) :
    IsWeightedHomogeneous (rowW r r) (cofMap r x) (fun c => ∑ a, μ a - μ (Fin.rev c)) := by
  unfold cofMap
  refine aeval_weighted_homog (rowW r r) _ (diagonalEntryIndicator r) (fun v => adjugate_entry_weighted_homog r _ _) x _ ?_
  intro d hd
  have hwt := hx hd
  funext c
  have h := weight_omega_add_degree d c
  simp only [← ldrow_weight_rowW, hwt] at h
  omega
end Formalism.CohomologicalDescent.LD
